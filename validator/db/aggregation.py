"""Select immutable benchmark evidence for one explicit corpus-content set."""

from __future__ import annotations

import json
import math
import re
import warnings
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

from sqlalchemy import select
from sqlalchemy.orm import Session

from bench.corpora import Corpus
from bench.results import INCUMBENT, Run, parse
from bench.storage import sha256

from .models import BenchmarkRun


@dataclass(frozen=True, order=True)
class CorpusIdentity:
    name: str
    sha256: str

    def __post_init__(self) -> None:
        if not self.name or re.fullmatch(r"[0-9a-f]{64}", self.sha256) is None:
            raise ValueError("a corpus requires a name and SHA-256 content identity")


def select_runs(
    session: Session,
    source_sha256: str,
    corpora: Sequence[CorpusIdentity],
    run_ids: Sequence[int] | None = None,
) -> list[BenchmarkRun]:
    """One complete run per corpus; explicit selections never fall back.

    Runs without a measurement timestamp are eligible only by explicit ID: import
    time is not a reliable substitute for measurement time. Latest selection uses
    started_at, then database ID to deterministically resolve equal timestamps.
    """
    if re.fullmatch(r"[0-9a-f]{64}", source_sha256) is None:
        raise ValueError("invalid source SHA-256")
    if not corpora or len({c.name for c in corpora}) != len(corpora):
        raise ValueError("provide a nonempty set of uniquely named corpora")
    wanted = set(corpora)
    if run_ids is not None:
        if len(run_ids) != len(wanted) or len(set(run_ids)) != len(run_ids):
            raise ValueError("select exactly one distinct run per corpus")
        rows = list(session.scalars(select(BenchmarkRun).where(BenchmarkRun.id.in_(run_ids))))
        if len(rows) != len(run_ids):
            raise ValueError("a requested benchmark run does not exist")
    else:
        rows = []
        for corpus in sorted(wanted):
            row = session.scalar(
                select(BenchmarkRun)
                .where(
                    BenchmarkRun.source_sha256 == source_sha256,
                    BenchmarkRun.corpus == corpus.name,
                    BenchmarkRun.corpus_sha256 == corpus.sha256,
                    BenchmarkRun.status == "complete",
                    BenchmarkRun.invalidated_at.is_(None),
                    BenchmarkRun.started_at.is_not(None),
                )
                .order_by(BenchmarkRun.started_at.desc(), BenchmarkRun.id.desc())
                .limit(1)
            )
            if row is None:
                raise ValueError(f"no valid timestamped run for {corpus.name}:{corpus.sha256}")
            rows.append(row)
    identities = [CorpusIdentity(r.corpus, r.corpus_sha256) for r in rows]
    if len(set(identities)) != len(rows) or set(identities) != wanted:
        raise ValueError("selected runs do not cover the exact requested corpus set")
    for row in rows:
        if row.source_sha256 != source_sha256:
            raise ValueError(f"run {row.id}: source mismatch")
        if row.status != "complete" or row.invalidated_at is not None:
            raise ValueError(f"run {row.id}: failed or invalidated")
    return sorted(rows, key=lambda r: (r.corpus, r.corpus_sha256))


def validate_evidence(row: BenchmarkRun) -> Run:
    """Validate retained raw evidence without relying on original local files.

    Unknown determinism is not sufficient for scoring: both measured Rust methods
    need a token hash and at least two repetitions, including warmups.
    """
    if row.status != "complete" or row.invalidated_at is not None:
        raise ValueError(f"run {row.id}: failed or invalidated")
    run = parse(
        "\n".join(json.dumps(record, allow_nan=False) for record in row.raw_data),
        Corpus(row.corpus, Path("."), False, {}),
    )
    if len(row.raw_data) != len(run.files) + 1 or not run.files:
        raise ValueError("unexpected or missing file records")
    if run.candidates() != (row.candidate_method,):
        raise ValueError("candidate identity mismatch")
    if run.meta.corpus != row.corpus:
        raise ValueError("corpus name mismatch")
    if run.meta.methods[row.candidate_method].source_sha256 != row.source_sha256:
        raise ValueError("candidate source mismatch")
    manifest = sorted((f.file, f.sha256, f.raw_bytes) for f in run.files)
    if len({f.file for f in run.files}) != len(run.files) or sha256(manifest) != row.corpus_sha256:
        raise ValueError("corpus manifest mismatch")
    if run.meta.measured_rounds < 1 or run.meta.warmup_rounds < 0:
        raise ValueError("invalid repetition counts")
    if run.meta.measured_rounds + run.meta.warmup_rounds < 2:
        raise ValueError("repeated token determinism evidence required")
    for name in (INCUMBENT, row.candidate_method):
        meta = run.meta.methods.get(name)
        if (
            meta is None
            or meta.external
            or re.fullmatch(r"[0-9a-f]{64}", meta.source_sha256 or "") is None
        ):
            raise ValueError("missing Rust method source identity")
        for file in run.files:
            result = file.methods.get(name)
            if result is None or result.external or not result.ok:
                raise ValueError(f"{file.file}: missing or failed {name}")
            if file.raw_bytes < 0 or re.fullmatch(r"[0-9a-f]{64}", file.sha256) is None:
                raise ValueError("invalid input size/hash")
            if result.output_bytes is None or result.output_bytes < 0:
                raise ValueError("missing output size")
            for digest in (result.tokens_sha256, result.output_sha256):
                if re.fullmatch(r"[0-9a-f]{64}", digest or "") is None:
                    raise ValueError("missing output/token hash")
            for phase, count in (
                ("warmup", run.meta.warmup_rounds),
                ("measured", run.meta.measured_rounds),
            ):
                if sum(rep.phase == phase for rep in result.reps) != count:
                    raise ValueError("incomplete timing samples")
            for rep in result.reps:
                if (
                    rep.phase not in {"warmup", "measured"}
                    or not math.isfinite(rep.time_s)
                    or rep.time_s < 0
                ):
                    raise ValueError("invalid timing sample")
    return run


CALCULATOR_VERSION = "median-v2"


@dataclass(frozen=True)
class Aggregated:
    source_sha256: str
    raw_bytes: int
    incumbent_bytes: int
    bytes: int
    incumbent_seconds: float
    parse_seconds: float
    run_ids: tuple[int, ...]

    @property
    def ratio_pct(self) -> float:
        return 100 * self.bytes / self.raw_bytes

    @property
    def time_ratio(self) -> float:
        return self.parse_seconds / self.incumbent_seconds


def compatibility(run: Run) -> tuple[object, ...]:
    """Recorded protocol/environment only; absent metadata is not certification.

    Current artifacts do not identify the engine binary, CPU affinity, compiler
    flags or host uniquely. These omissions must remain visible in reports.
    """
    m = run.meta
    provenance = run.raw_records[0].get("benchmark_provenance")
    if not isinstance(provenance, dict) or not all(
        provenance.get(key) for key in ("engine_sha256", "template_sha256", "host_sha256")
    ):
        raise ValueError("benchmark provenance missing; rebenchmark before aggregation")
    return (
        sha256(run.raw_records[0].get("benchmark_provenance")),
        m.schema_version,
        m.os,
        m.arch,
        m.rustc_version,
        m.cpu_model,
        m.cpu_governor,
        m.warmup_rounds,
        m.measured_rounds,
        m.methods[INCUMBENT].source_sha256,
        m.methods[INCUMBENT].lib_sha256,
    )


def reduce_runs(rows: Sequence[BenchmarkRun]) -> Aggregated:
    """Sum per-file median times and byte counts; never pool independent runs."""
    if not rows or len({r.corpus for r in rows}) != len(rows):
        raise ValueError("exactly one run per requested corpus is required")
    if len({r.source_sha256 for r in rows}) != 1:
        raise ValueError("mixed candidate sources")
    runs = [validate_evidence(row) for row in rows]
    if len({compatibility(run) for run in runs}) != 1:
        raise ValueError("incompatible benchmark protocol, environment or incumbent")
    seen: set[str] = set()
    for run in runs:
        hashes = {f.sha256 for f in run.files}
        if seen & hashes:
            warnings.warn(
                "corpora contain identical file content; counted once per corpus", stacklevel=2
            )
        seen.update(hashes)
    raw = output = incumbent_output = 0
    seconds = incumbent_seconds = 0.0
    for row, run in zip(rows, runs, strict=True):
        candidate = run.totals(row.candidate_method)
        incumbent = run.totals(INCUMBENT)
        raw += candidate.raw_bytes
        output += candidate.output_bytes
        incumbent_output += incumbent.output_bytes
        seconds += candidate.parse_s
        incumbent_seconds += incumbent.parse_s
    if raw <= 0 or seconds <= 0 or incumbent_seconds <= 0:
        raise ValueError("positive input size and measured times required")
    if not math.isfinite(seconds) or not math.isfinite(incumbent_seconds):
        raise ValueError("nonfinite aggregate time")
    return Aggregated(
        rows[0].source_sha256,
        raw,
        incumbent_output,
        output,
        incumbent_seconds,
        seconds,
        tuple(sorted(row.id for row in rows)),
    )


def timing_statistics(rows: Sequence[BenchmarkRun], *, draws: int = 2000) -> dict[str, object]:
    """Paired per-file bootstrap of median timing estimates.

    Resample indices independently per file, pairing the two methods within
    that file. File independence is an approximation; intervals exclude host
    drift and describe only the recorded repetitions.
    """
    import random
    import statistics

    if draws < 100:
        raise ValueError("at least 100 bootstrap draws required")
    rows = sorted(rows, key=lambda r: r.id)
    runs = [validate_evidence(row) for row in rows]
    files = []
    for row, run in zip(rows, runs, strict=True):
        for file in run.files:
            for method in (INCUMBENT, row.candidate_method):
                result = file.methods[method]
                files.append(
                    {
                        "run_id": row.id,
                        "file": file.file,
                        "method": method,
                        "n": len(result.measured),
                        "median_s": result.parse_s,
                        "sample_std_s": result.sample_std_s,
                    }
                )
    answer: dict[str, object] = {
        "files": files,
        "method": "paired-per-file-percentile-bootstrap-v2",
        "confidence": 0.95,
        "draws": draws,
        "scope": "within recorded runs only; excludes host drift and systematic bias",
        "sparse": any(run.meta.measured_rounds < 10 for run in runs),
    }
    if any(run.meta.measured_rounds < 2 for run in runs):
        answer["intervals"] = None
        return answer
    seed = int(sha256([row.raw_data for row in rows])[:16], 16)
    rng = random.Random(seed)
    samples: dict[str, list[float]] = {
        "parse_seconds": [],
        "incumbent_seconds": [],
        "time_ratio": [],
    }
    for _ in range(draws):
        candidate = incumbent = 0.0
        for row, run in zip(rows, runs, strict=True):
            n = run.meta.measured_rounds
            for file in run.files:
                indices = [rng.randrange(n) for _ in range(n)]
                candidate += statistics.median(
                    [file.methods[row.candidate_method].measured[i] for i in indices]
                )
                incumbent += statistics.median(
                    [file.methods[INCUMBENT].measured[i] for i in indices]
                )
        samples["parse_seconds"].append(candidate)
        samples["incumbent_seconds"].append(incumbent)
        if incumbent <= 0:
            raise ValueError("zero incumbent time in bootstrap resample")
        samples["time_ratio"].append(candidate / incumbent)
    answer["intervals"] = {
        name: [
            sorted(values)[int(0.025 * draws)],
            sorted(values)[min(draws - 1, int(0.975 * draws))],
        ]
        for name, values in samples.items()
    }
    return answer


def evaluation_context(rows: Sequence[BenchmarkRun]) -> dict[str, object]:
    runs = [validate_evidence(row) for row in rows]
    if len({compatibility(run) for run in runs}) != 1:
        raise ValueError("incompatible measurement context")
    return {
        "corpora": sorted([[r.corpus, r.corpus_sha256] for r in rows]),
        "protocol": list(compatibility(runs[0])),
        "calculator": CALCULATOR_VERSION,
    }


def aggregate(session: Session, rows: Sequence[BenchmarkRun]):
    """Create immutable evidence, atomically and idempotently, without publication."""
    from sqlalchemy import text

    from .models import BenchmarkAggregation, BenchmarkAggregationInput

    values = reduce_runs(rows)
    key = sha256([CALCULATOR_VERSION, list(values.run_ids)])
    # Transaction lock serializes competing creators before querying for a prior result.
    session.execute(text("SELECT pg_advisory_xact_lock(:key)"), {"key": int(key[:15], 16)})
    existing = session.scalar(
        select(BenchmarkAggregation).where(BenchmarkAggregation.input_key == key)
    )
    if existing is not None:
        return existing
    row = BenchmarkAggregation(
        source_sha256=values.source_sha256,
        calculator_version=CALCULATOR_VERSION,
        input_key=key,
        context=evaluation_context(rows),
        statistics=timing_statistics(rows),
        raw_bytes=values.raw_bytes,
        bytes=values.bytes,
        incumbent_bytes=values.incumbent_bytes,
        parse_seconds=values.parse_seconds,
        incumbent_seconds=values.incumbent_seconds,
    )
    session.add(row)
    session.flush()
    session.add_all(
        [BenchmarkAggregationInput(aggregation_id=row.id, run_id=rid) for rid in values.run_ids]
    )
    session.flush()
    return row


def publish(
    session: Session, submission_id: int, aggregation_id: int, *, speed_floor: float = 8.0
) -> None:
    """Bind verified source to selected evidence; acceptance/registration stay separate."""
    from verifier.identity import required_fingerprint

    from .models import BenchmarkAggregation, BenchmarkAggregationInput, Submission

    submission = session.get(Submission, submission_id, with_for_update=True)
    aggregation = session.get(BenchmarkAggregation, aggregation_id)
    if submission is None or aggregation is None:
        raise ValueError("submission or aggregation does not exist")
    if (
        submission.static_verified_at is None
        or submission.lean_verified_at is None
        or submission.verifier_fingerprint != required_fingerprint()
        or submission.source_sha256 != aggregation.source_sha256
    ):
        raise ValueError("matching current static and Lean verification required")
    rows = list(
        session.scalars(
            select(BenchmarkRun)
            .join(BenchmarkAggregationInput, BenchmarkAggregationInput.run_id == BenchmarkRun.id)
            .where(BenchmarkAggregationInput.aggregation_id == aggregation.id)
            .with_for_update(of=BenchmarkRun)
        )
    )
    values = reduce_runs(rows)
    if (
        aggregation.calculator_version != CALCULATOR_VERSION
        or aggregation.context != evaluation_context(rows)
    ):
        raise ValueError("stale aggregation context")
    for field in ("raw_bytes", "bytes", "incumbent_bytes", "parse_seconds", "incumbent_seconds"):
        if getattr(aggregation, field) != getattr(values, field):
            raise ValueError("aggregation no longer matches evidence")
    if not math.isfinite(speed_floor) or speed_floor <= 0 or values.time_ratio > speed_floor:
        raise ValueError("aggregation exceeds speed floor")
    for field in ("raw_bytes", "bytes", "incumbent_bytes", "parse_seconds", "incumbent_seconds"):
        setattr(submission, field, getattr(values, field))
    submission.time_ratio = values.time_ratio
    submission.measured_source_sha256 = values.source_sha256
    submission.aggregation_id = aggregation.id
