"""Turning a measurement into something to read, to store, or to send back.

The one place the `public = false` rule is enforced: per-file numbers returned
to whoever submitted are an oracle over a held-out corpus across repeated
submissions, so a corpus that is not public leaves here as totals only. The raw
records still exist -- `records()` is what the validator keeps for itself.
"""

from __future__ import annotations

from collections.abc import Sequence

from .driver import Measurement
from .results import INCUMBENT, FileResult, MethodResult
from .verdict import SPEED_FLOOR, Verdict, judge


def merge(m: Measurement) -> tuple[FileResult, ...]:
    """One record per corpus file, holding every candidate's methods at once.

    N candidates means N processes, each with its own incumbent. The merged view
    keeps the first process's incumbent and reference bars; what the others said
    about the incumbent is a check on the host, not a measurement of a parser,
    and comes back through `Measurement.warnings()`.
    """
    if not m.runs:
        return ()
    merged: dict[str, dict[str, MethodResult]] = {}
    shape: dict[str, FileResult] = {}
    for run in m.runs:
        for f in run.files:
            into = merged.setdefault(f.file, {})
            shape.setdefault(f.file, f)
            for name, method in f.methods.items():
                into.setdefault(name, method)
    return tuple(
        FileResult(
            file=f.file,
            format=f.format,
            raw_bytes=f.raw_bytes,
            sha256=f.sha256,
            methods=merged[file],
        )
        for file, f in shape.items()
    )


def verdicts(m: Measurement, floor: float = SPEED_FLOOR) -> dict[str, Verdict]:
    return {name: judge(m.of(name), name, floor) for name in m.candidates()}


def table(m: Measurement, floor: float = SPEED_FLOOR) -> str:
    """The score, as a table: one row per corpus file, one column per method."""
    files = merge(m)
    order = _order(m)
    lines: list[str] = []
    if m.corpus.public:
        lines += _bytes_table(files, order)
        lines.append("")
    else:
        lines.append(f"corpus {m.corpus.name} is held out; totals only.")
        lines.append("")
    lines += _summary_table(m, order, floor)
    for w in m.warnings():
        lines.append(f"warning: {w}")
    return "\n".join(lines)


def summary(m: Measurement, floor: float = SPEED_FLOOR) -> dict[str, object]:
    """The machine-readable answer: what a validator stores and a miner is sent."""
    files = merge(m)
    judged = verdicts(m, floor)
    methods: dict[str, object] = {}
    for name in _order(m):
        run = m.of(name) if name in judged else m.runs[0]
        totals = run.totals(name)
        meta = run.meta.methods.get(name)
        entry: dict[str, object] = {
            "external": bool(meta and meta.external),
            "output_bytes": totals.output_bytes,
            "parse_s": totals.parse_s,
            "encode_s": totals.encode_s,
            "source_sha256": meta.source_sha256 if meta else None,
            "lib_sha256": meta.lib_sha256 if meta else None,
            "errors": list(run.failures(name)),
        }
        if (v := judged.get(name)) is not None:
            entry |= {
                "ratio": v.ratio,
                "slowdown": v.slowdown,
                "accepted": v.accepted,
                "improved": v.improved,
                "reason": v.reason,
            }
        methods[name] = entry
    head = m.runs[0].meta
    out: dict[str, object] = {
        "schema_version": head.schema_version,
        "corpus": {"name": m.corpus.name, "public": m.corpus.public},
        # Which entries in `methods` are the parsers under test, so a reader
        # never has to know what the caller happened to name them.
        "candidates": list(m.candidates()),
        "raw_bytes": sum(f.raw_bytes for f in files),
        "rustc_version": head.rustc_version,
        "cpu_model": head.cpu_model,
        "cpu_governor": head.cpu_governor,
        "started_at_unix": head.started_at_unix,
        "warmup_rounds": head.warmup_rounds,
        "measured_rounds": head.measured_rounds,
        "speed_floor": floor,
        "worst_spread": max((r.worst_spread() for r in m.runs), default=0.0),
        "warnings": list(m.warnings()),
        "methods": methods,
    }
    if m.corpus.public:
        out["files"] = [_file_json(f) for f in files]
    return out


def records(m: Measurement, floor: float = SPEED_FLOOR) -> list[dict[str, object]]:
    """The full raw run, as JSONL records. Never leaves the validator unfiltered."""
    head = m.runs[0].meta
    meta: dict[str, object] = {
        "kind": "meta",
        "schema_version": head.schema_version,
        "started_at_unix": head.started_at_unix,
        "corpus": m.corpus.name,
        "corpus_dir": head.corpus_dir,
        "corpus_public": m.corpus.public,
        "os": head.os,
        "arch": head.arch,
        "rustc_version": head.rustc_version,
        "cpu_model": head.cpu_model,
        "cpu_governor": head.cpu_governor,
        "warmup_rounds": head.warmup_rounds,
        "measured_rounds": head.measured_rounds,
        "speed_floor": floor,
        "methods": {
            name: {
                "external": meta_.external,
                "source_sha256": meta_.source_sha256,
                "lib_sha256": meta_.lib_sha256,
            }
            for run in m.runs
            for name, meta_ in run.meta.methods.items()
        },
        "incumbent_parse_s": [r.totals(INCUMBENT).parse_s for r in m.runs],
        "warnings": list(m.warnings()),
    }
    return [meta, *(_file_json(f) | {"kind": "file", "corpus": m.corpus.name} for f in merge(m))]


def _order(m: Measurement) -> list[str]:
    # The incumbent first, candidates in the order they were asked for, bars last.
    head = m.runs[0].meta
    bars = [n for n, meta in head.methods.items() if meta.external]
    return [INCUMBENT, *m.candidates(), *bars]


def _file_json(f: FileResult) -> dict[str, object]:
    return {
        "file": f.file,
        "format": f.format,
        "raw_bytes": f.raw_bytes,
        "sha256": f.sha256,
        "methods": {name: _method_json(mr) for name, mr in sorted(f.methods.items())},
    }


def _method_json(mr: MethodResult) -> dict[str, object]:
    return {
        "external": mr.external,
        "output_bytes": mr.output_bytes,
        "output_sha256": mr.output_sha256,
        "tokens": mr.tokens,
        "tokens_sha256": mr.tokens_sha256,
        "deterministic": mr.deterministic,
        "encode_s": mr.encode_s,
        "errors": list(mr.errors),
        "reps": [
            {"phase": r.phase, "order_index": r.order_index, "time_s": r.time_s} for r in mr.reps
        ],
    }


def _bytes_table(files: Sequence[FileResult], order: Sequence[str]) -> list[str]:
    head = ["file", "raw", *order]
    rows = [[f.file, str(f.raw_bytes), *[_bytes(f.methods.get(n)) for n in order]] for f in files]

    def column(n: str) -> str:
        return str(sum((f.methods[n].output_bytes or 0) for f in files if n in f.methods))

    total = ["TOTAL", str(sum(f.raw_bytes for f in files)), *[column(n) for n in order]]
    return _grid(head, [*rows, None, total])


def _summary_table(m: Measurement, order: Sequence[str], floor: float) -> list[str]:
    judged = verdicts(m, floor)
    head = ["method", "bytes", "ratio", "parse", "slowdown", ""]
    rows: list[list[str] | None] = []
    for name in order:
        # Always against the incumbent from the same process. Across processes
        # the incumbent's own time drifts, and a ratio taken across them is not
        # a measurement of anything.
        run = m.of(name) if name in judged else m.runs[0]
        base = run.totals(INCUMBENT)
        t = run.totals(name)
        v = judged.get(name)
        rows.append(
            [
                name,
                str(t.output_bytes),
                f"{_over(t.output_bytes, base.output_bytes):.5f}x",
                f"{t.parse_s:.3f}s",
                f"{_over(t.parse_s, base.parse_s):.2f}x",
                v.line() if v else ("reference" if name != INCUMBENT else "the incumbent"),
            ]
        )
    return _grid(head, rows, left=frozenset({0, len(head) - 1}))


def _bytes(mr: MethodResult | None) -> str:
    return "-" if mr is None or mr.output_bytes is None else str(mr.output_bytes)


def _over(a: float, b: float) -> float:
    return a / b if b > 0 else 0.0


def _grid(
    head: Sequence[str], rows: Sequence[Sequence[str] | None], left: frozenset[int] = frozenset({0})
) -> list[str]:
    # Numbers right, names and prose left; `None` is a rule.
    body = [r for r in rows if r is not None]
    width = [max(len(head[i]), *(len(r[i]) for r in body)) for i in range(len(head))]

    def line(cells: Sequence[str]) -> str:
        return "  ".join(
            c.ljust(width[i]) if i in left else c.rjust(width[i]) for i, c in enumerate(cells)
        ).rstrip()

    rule = "-" * (sum(width) + 2 * (len(width) - 1))
    out = [line(head), rule]
    for r in rows:
        out.append(rule if r is None else line(r))
    return out
