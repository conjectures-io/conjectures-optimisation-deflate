"""The engine's JSONL as typed objects, plus the one definition of every number
derived from it.

The engine folds nothing, so "the parse time of a method on a file" is a choice
made here and nowhere else: the minimum over the measured reps. Every caller --
the gate, the miner CLI, the worker -- reads it through these, so they cannot
drift apart.
"""

from __future__ import annotations

import json
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from typing import cast

from .corpora import Corpus
from .errors import Malformed

INCUMBENT = "incumbent"

#: The engine's `record::SCHEMA_VERSION`; a file that says otherwise is not ours.
SCHEMA_VERSION = 3

#: How much the incumbent's own time may vary between processes before the run
#: is called noise rather than measurement.
HOST_DRIFT = 1.25


@dataclass(frozen=True)
class Rep:
    phase: str
    order_index: int
    time_s: float


@dataclass(frozen=True)
class MethodResult:
    name: str
    external: bool
    output_bytes: int | None
    output_sha256: str | None
    tokens: int | None
    tokens_sha256: str | None
    deterministic: bool
    encode_s: float | None
    errors: tuple[str, ...]
    reps: tuple[Rep, ...]

    @property
    def ok(self) -> bool:
        return not self.errors and self.deterministic

    @property
    def measured(self) -> tuple[float, ...]:
        return tuple(r.time_s for r in self.reps if r.phase == "measured")

    @property
    def parse_s(self) -> float:
        # The floor of what the parse costs: the fastest rep, as the gate has
        # always measured it. Slower reps are the host's noise, not the parser's.
        return min(self.measured, default=0.0)

    @property
    def spread(self) -> float:
        # max/min over the measured reps. Large means a loaded host, not a slow parser.
        m = self.measured
        lo = min(m, default=0.0)
        return max(m, default=0.0) / lo if lo > 0 else 0.0


@dataclass(frozen=True)
class FileResult:
    file: str
    format: str
    raw_bytes: int
    sha256: str
    methods: Mapping[str, MethodResult]


@dataclass(frozen=True)
class MethodMeta:
    external: bool
    crate_dir: str | None
    source_sha256: str | None
    lib_sha256: str | None


@dataclass(frozen=True)
class Meta:
    schema_version: int
    started_at_unix: float
    corpus: str
    corpus_dir: str
    os: str
    arch: str
    rustc_version: str | None
    cpu_model: str | None
    cpu_governor: str | None
    warmup_rounds: int
    measured_rounds: int
    speed_floor: float | None
    methods: Mapping[str, MethodMeta]


@dataclass(frozen=True)
class Totals:
    raw_bytes: int
    output_bytes: int
    parse_s: float
    encode_s: float


@dataclass(frozen=True)
class Run:
    """One engine process: the incumbent and one candidate over one corpus."""

    meta: Meta
    files: tuple[FileResult, ...]
    raw_records: tuple[dict[str, object], ...] = ()

    def method_names(self) -> tuple[str, ...]:
        return tuple(self.meta.methods)

    def candidates(self) -> tuple[str, ...]:
        return tuple(n for n, m in self.meta.methods.items() if not m.external and n != INCUMBENT)

    def totals(self, method: str) -> Totals:
        raw = output = 0
        parse = encode = 0.0
        for f in self.files:
            m = f.methods.get(method)
            if m is None:
                continue
            raw += f.raw_bytes
            output += m.output_bytes or 0
            parse += m.parse_s
            encode += m.encode_s or 0.0
        return Totals(raw_bytes=raw, output_bytes=output, parse_s=parse, encode_s=encode)

    def ratio(self, method: str, against: str = INCUMBENT) -> float:
        # Compressed size against the incumbent's: below 1.0 is an improvement.
        return _over(self.totals(method).output_bytes, self.totals(against).output_bytes)

    def slowdown(self, method: str, against: str = INCUMBENT) -> float:
        # Parse time against the incumbent's; what SPEED_FLOOR is applied to.
        return _over(self.totals(method).parse_s, self.totals(against).parse_s)

    def failures(self, method: str) -> tuple[str, ...]:
        out: list[str] = []
        for f in self.files:
            m = f.methods.get(method)
            if m is None:
                out.append(f"{f.file}: {method}: not measured")
                continue
            out += [f"{f.file}: {method}: {e}" for e in m.errors]
            if not m.deterministic:
                out.append(f"{f.file}: {method}: tokens changed between reps")
        return tuple(out)

    def worst_spread(self) -> float:
        # The noisiest (file, method) in the run; the host-load signal.
        return max((m.spread for f in self.files for m in f.methods.values()), default=0.0)


def parse(stdout: str, corpus: Corpus) -> Run:
    """The engine's stdout into a `Run`, attaching each file's format label."""
    records = [_object(ln) for ln in stdout.splitlines() if ln.strip()]
    if not records:
        raise Malformed("the engine produced no output")
    head = records[0]
    if head.get("kind") != "meta":
        raise Malformed("the first line must be the meta record")
    meta = _meta(head)
    if meta.schema_version != SCHEMA_VERSION:
        raise Malformed(f"schema version {meta.schema_version}, expected {SCHEMA_VERSION}")
    files = tuple(_file(r, corpus) for r in records[1:] if r.get("kind") == "file")
    return Run(meta=meta, files=files, raw_records=tuple(records))


def incumbent_agreement(runs: Iterable[Run]) -> tuple[str, ...]:
    """What the incumbent, measured once per candidate process, says about the host.

    Its compressed output must be identical in every process -- if it is not,
    something is badly wrong. Its *time* may drift, and a large drift means the
    machine was loaded, which makes every ratio in the run suspect.
    """
    seen = list(runs)
    if len(seen) < 2:
        return ()
    out: list[str] = []
    per_file: dict[str, set[str]] = {}
    for run in seen:
        for f in run.files:
            m = f.methods.get(INCUMBENT)
            if m is not None and m.output_sha256:
                per_file.setdefault(f.file, set()).add(m.output_sha256)
    for file, hashes in sorted(per_file.items()):
        if len(hashes) > 1:
            out.append(f"{file}: the incumbent compressed it differently across processes")
    times = [run.totals(INCUMBENT).parse_s for run in seen]
    lo = min(times)
    if lo > 0 and max(times) / lo > HOST_DRIFT:
        out.append(
            f"the incumbent's own parse time varied {max(times) / lo:.2f}x across "
            "processes; the host was loaded and these ratios are not comparable"
        )
    return tuple(out)


def _over(a: float, b: float) -> float:
    return a / b if b > 0 else 0.0


def _meta(r: Mapping[str, object]) -> Meta:
    return Meta(
        schema_version=_int(r, "schema_version"),
        started_at_unix=_float(r, "started_at_unix"),
        corpus=_str(r, "corpus"),
        corpus_dir=_str(r, "corpus_dir"),
        os=_str(r, "os"),
        arch=_str(r, "arch"),
        rustc_version=_opt_str(r, "rustc_version"),
        cpu_model=_opt_str(r, "cpu_model"),
        cpu_governor=_opt_str(r, "cpu_governor"),
        warmup_rounds=_int(r, "warmup_rounds"),
        measured_rounds=_int(r, "measured_rounds"),
        speed_floor=_opt_float(r, "speed_floor"),
        methods={
            name: MethodMeta(
                external=_bool(m, "external"),
                crate_dir=_opt_str(m, "crate_dir"),
                source_sha256=_opt_str(m, "source_sha256"),
                lib_sha256=_opt_str(m, "lib_sha256"),
            )
            for name, m in _objects(r, "methods").items()
        },
    )


def _file(r: Mapping[str, object], corpus: Corpus) -> FileResult:
    name = _str(r, "file")
    return FileResult(
        file=name,
        format=corpus.format_of(name),
        raw_bytes=_int(r, "raw_bytes"),
        sha256=_str(r, "sha256"),
        methods={n: _method(n, m) for n, m in _objects(r, "methods").items()},
    )


def _method(name: str, r: Mapping[str, object]) -> MethodResult:
    return MethodResult(
        name=name,
        external=_bool(r, "external"),
        output_bytes=_opt_int(r, "output_bytes"),
        output_sha256=_opt_str(r, "output_sha256"),
        tokens=_opt_int(r, "tokens"),
        tokens_sha256=_opt_str(r, "tokens_sha256"),
        deterministic=_bool(r, "deterministic"),
        encode_s=_opt_float(r, "encode_s"),
        errors=tuple(str(e) for e in _list(r, "errors")),
        reps=tuple(
            Rep(
                phase=_str(rep, "phase"),
                order_index=_int(rep, "order_index"),
                time_s=_float(rep, "time_s"),
            )
            for rep in (_as_dict(x) for x in _list(r, "reps"))
        ),
    )


def _object(line: str) -> dict[str, object]:
    try:
        return _as_dict(cast("object", json.loads(line)))
    except json.JSONDecodeError as e:
        raise Malformed(f"not JSON: {e}") from None


def _as_dict(v: object) -> dict[str, object]:
    if not isinstance(v, dict):
        raise Malformed(f"expected an object, got {type(v).__name__}")
    return cast("dict[str, object]", v)


def _objects(r: Mapping[str, object], k: str) -> dict[str, dict[str, object]]:
    return {name: _as_dict(v) for name, v in _as_dict(r.get(k, {})).items()}


def _list(r: Mapping[str, object], k: str) -> list[object]:
    v = r.get(k, [])
    if not isinstance(v, list):
        raise Malformed(f"{k} must be a list")
    return cast("list[object]", v)


def _str(r: Mapping[str, object], k: str) -> str:
    v = r.get(k)
    if not isinstance(v, str):
        raise Malformed(f"{k} must be a string")
    return v


def _opt_str(r: Mapping[str, object], k: str) -> str | None:
    return None if r.get(k) is None else _str(r, k)


def _int(r: Mapping[str, object], k: str) -> int:
    v = r.get(k)
    if isinstance(v, bool) or not isinstance(v, int):
        raise Malformed(f"{k} must be an integer")
    return v


def _opt_int(r: Mapping[str, object], k: str) -> int | None:
    return None if r.get(k) is None else _int(r, k)


def _float(r: Mapping[str, object], k: str) -> float:
    v = r.get(k)
    if isinstance(v, bool) or not isinstance(v, (int, float)):
        raise Malformed(f"{k} must be a number")
    return float(v)


def _opt_float(r: Mapping[str, object], k: str) -> float | None:
    return None if r.get(k) is None else _float(r, k)


def _bool(r: Mapping[str, object], k: str) -> bool:
    v = r.get(k)
    if not isinstance(v, bool):
        raise Malformed(f"{k} must be true or false")
    return v
