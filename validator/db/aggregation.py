"""Select immutable benchmark evidence for one explicit corpus-content set."""

from __future__ import annotations

import json
import math
import re
import statistics
import warnings
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import TypedDict, cast

from sqlalchemy import select, text
from sqlalchemy.orm import Session

from bench.corpora import Corpus
from bench.results import INCUMBENT, SCHEMA_VERSION, FileResult, Run, parse
from bench.storage import sha256
from verifier.identity import required_fingerprint

from .locks import publication_lock
from .models import BenchmarkAggregation, BenchmarkAggregationInput, BenchmarkRun, Submission


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
        rows: list[BenchmarkRun] = []
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
    if run.meta.schema_version != SCHEMA_VERSION:
        raise ValueError("full compression timings required; rebenchmark legacy runs")
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


CALCULATOR_VERSION = "compression-relative-time-v5"


@dataclass(frozen=True)
class Aggregated:
    source_sha256: str
    raw_bytes: int
    incumbent_bytes: int
    bytes: int
    incumbent_seconds: float
    parse_seconds: float
    compression_seconds: float
    run_ids: tuple[int, ...]

    ratio_pct: float
    incumbent_ratio_pct: float
    balanced_time_ratio: float

    @property
    def byte_weighted_ratio_pct(self) -> float:
        return 100 * self.bytes / self.raw_bytes

    @property
    def time_ratio(self) -> float:
        return self.compression_seconds / self.incumbent_seconds


def compatibility(run: Run) -> tuple[object, ...]:
    """Recorded protocol/environment only; absent metadata is not certification.

    Provenance binds the engine, template, host and configured resource limits.
    Only matching protocols and environments may be combined.
    """
    m = run.meta
    missing_provenance = "benchmark provenance missing; rebenchmark before aggregation"
    raw_provenance = run.raw_records[0].get("benchmark_provenance")
    if not isinstance(raw_provenance, dict):
        raise ValueError(missing_provenance)
    # isinstance narrows to the bare `dict`, erasing the `dict[str, object]` we know this
    # is from Run.raw_records' own type; cast restores it instead of losing that back to
    # `dict[Unknown, Unknown]`.
    provenance = cast(dict[str, object], raw_provenance)
    if not all(provenance.get(key) for key in ("engine_sha256", "template_sha256", "host_sha256")):
        raise ValueError(missing_provenance)
    return (
        sha256(provenance),
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


class CorpusCompressionStats(TypedDict):
    corpus: str
    files: int
    empty_files: int
    ratio_pct: float
    incumbent_ratio_pct: float


class CompressionStatistics(TypedDict):
    method: str
    corpora: list[CorpusCompressionStats]
    ratio_pct: float
    incumbent_ratio_pct: float
    byte_weighted_ratio_pct: float
    incumbent_byte_weighted_ratio_pct: float


def _output_ratio_pct(file: FileResult, method: str) -> float:
    output_bytes = file.methods[method].output_bytes
    # validate_evidence already required a non-negative output size for every file.
    assert output_bytes is not None
    return 100 * output_bytes / file.raw_bytes


def compression_statistics(rows: Sequence[BenchmarkRun]) -> CompressionStatistics:
    """Equal weight per nonempty file, then equal weight per corpus."""
    corpora: list[CorpusCompressionStats] = []
    raw = output = incumbent_output = 0
    for row in sorted(rows, key=lambda row: row.corpus):
        run = validate_evidence(row)
        files = [file for file in run.files if file.raw_bytes > 0]
        if not files:
            raise ValueError(f"{row.corpus}: compression ratio requires nonempty files")
        ratios: dict[str, float] = {}
        for role, method in (("candidate", row.candidate_method), ("incumbent", INCUMBENT)):
            ratios[role] = statistics.mean(_output_ratio_pct(file, method) for file in files)
        corpora.append(
            {
                "corpus": row.corpus,
                "files": len(files),
                "empty_files": len(run.files) - len(files),
                "ratio_pct": ratios["candidate"],
                "incumbent_ratio_pct": ratios["incumbent"],
            }
        )
        totals = run.totals(row.candidate_method)
        raw += totals.raw_bytes
        output += totals.output_bytes
        incumbent_output += run.totals(INCUMBENT).output_bytes
    if not corpora:
        raise ValueError("at least one corpus required")
    return {
        "method": "equal-corpus-mean-of-nonempty-file-ratios",
        "corpora": corpora,
        "ratio_pct": statistics.mean(c["ratio_pct"] for c in corpora),
        "incumbent_ratio_pct": statistics.mean(c["incumbent_ratio_pct"] for c in corpora),
        "byte_weighted_ratio_pct": 100 * output / raw,
        "incumbent_byte_weighted_ratio_pct": 100 * incumbent_output / raw,
    }


class CorpusTimingStats(TypedDict):
    corpus: str
    files: int
    time_ratio: float


class RelativeTimingStatistics(TypedDict):
    method: str
    time_ratio: float
    corpora: list[CorpusTimingStats]


def relative_timing_statistics(rows: Sequence[BenchmarkRun]) -> RelativeTimingStatistics:
    """Equal-corpus mean of per-nonempty-file ratios of median total times."""
    corpora: list[CorpusTimingStats] = []
    for row in sorted(rows, key=lambda row: row.corpus):
        run = validate_evidence(row)
        ratios: list[float] = []
        for file in run.files:
            if file.raw_bytes == 0:
                continue
            candidate = file.methods[row.candidate_method].total_s
            incumbent = file.methods[INCUMBENT].total_s
            if candidate is None or incumbent is None or candidate <= 0 or incumbent <= 0:
                raise ValueError(f"{file.file}: positive per-file compression times required")
            ratio = candidate / incumbent
            if not math.isfinite(ratio):
                raise ValueError("nonfinite per-file time ratio")
            ratios.append(ratio)
        if not ratios:
            raise ValueError(f"{row.corpus}: relative timing requires nonempty files")
        corpora.append(
            {
                "corpus": row.corpus,
                "files": len(ratios),
                "time_ratio": statistics.mean(ratios),
            }
        )
    if not corpora:
        raise ValueError("at least one corpus required")
    return {
        "method": "equal-corpus-mean-of-per-file-median-time-ratios",
        "time_ratio": statistics.mean(c["time_ratio"] for c in corpora),
        "corpora": corpora,
    }


def reduce_runs(rows: Sequence[BenchmarkRun]) -> Aggregated:
    """Sum median times; balance compression ratios across files and corpora."""
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
    seconds = parse_seconds = incumbent_seconds = 0.0
    for row, run in zip(rows, runs, strict=True):
        candidate = run.totals(row.candidate_method)
        incumbent = run.totals(INCUMBENT)
        raw += candidate.raw_bytes
        output += candidate.output_bytes
        incumbent_output += incumbent.output_bytes
        assert candidate.total_s is not None and incumbent.total_s is not None
        parse_seconds += candidate.parse_s
        seconds += candidate.total_s
        incumbent_seconds += incumbent.total_s
    compression = compression_statistics(rows)
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
        parse_seconds,
        seconds,
        tuple(sorted(row.id for row in rows)),
        compression["ratio_pct"],
        compression["incumbent_ratio_pct"],
        relative_timing_statistics(rows)["time_ratio"],
    )


class FileTimingRecord(TypedDict):
    run_id: int
    file: str
    method: str
    n: int
    median_s: float | None
    sample_std_s: float | None
    lz77_median_s: float
    lz77_sample_std_s: float | None
    encode_median_s: float | None
    encode_sample_std_s: float | None


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
    files: list[FileTimingRecord] = []
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
                        "median_s": result.total_s,
                        "sample_std_s": statistics.stdev(result.measured_total)
                        if len(result.measured_total) > 1
                        else None,
                        "lz77_median_s": result.parse_s,
                        "lz77_sample_std_s": result.sample_std_s,
                        "encode_median_s": result.encoding_s,
                        "encode_sample_std_s": statistics.stdev(result.measured_encode)
                        if len(result.measured_encode) > 1
                        else None,
                    }
                )
    answer: dict[str, object] = {
        "files": files,
        "totals": {
            role: {
                "lz77_s": sum(run.totals(method).parse_s for run, method in pairs),
                "encode_s": sum(run.totals(method).encode_s or 0.0 for run, method in pairs),
                "compression_s": sum(run.totals(method).total_s or 0.0 for run, method in pairs),
            }
            for role, pairs in (
                ("candidate", list(zip(runs, [row.candidate_method for row in rows], strict=True))),
                ("incumbent", [(run, INCUMBENT) for run in runs]),
            )
        },
        "relative_timing": relative_timing_statistics(rows),
        "method": "paired-per-file-compression-bootstrap-v4",
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
        "compression_seconds": [],
        "incumbent_seconds": [],
        "time_ratio": [],
        "balanced_time_ratio": [],
    }
    for _ in range(draws):
        candidate = incumbent = 0.0
        corpus_ratios: list[float] = []
        for row, run in zip(rows, runs, strict=True):
            n = run.meta.measured_rounds
            file_ratios: list[float] = []
            for file in run.files:
                indices = [rng.randrange(n) for _ in range(n)]
                candidate_file = statistics.median(
                    [file.methods[row.candidate_method].measured_total[i] for i in indices]
                )
                incumbent_file = statistics.median(
                    [file.methods[INCUMBENT].measured_total[i] for i in indices]
                )
                candidate += candidate_file
                incumbent += incumbent_file
                if file.raw_bytes > 0:
                    if incumbent_file <= 0:
                        raise ValueError("zero per-file incumbent time in bootstrap resample")
                    file_ratios.append(candidate_file / incumbent_file)
            corpus_ratios.append(statistics.mean(file_ratios))
        samples["balanced_time_ratio"].append(statistics.mean(corpus_ratios))
        samples["compression_seconds"].append(candidate)
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


class EvaluationContext(TypedDict):
    # Kept as list-of-lists, not list-of-tuples: this is stored in and compared against
    # a JSONB column, which has no tuple type, and tuple != list even with equal
    # elements -- a tuple here would make every stale-context comparison fail.
    corpora: list[list[str]]
    protocol: list[object]
    calculator: str
    timing: str
    compression: str
    speed: str


def evaluation_context(rows: Sequence[BenchmarkRun]) -> EvaluationContext:
    runs = [validate_evidence(row) for row in rows]
    if len({compatibility(run) for run in runs}) != 1:
        raise ValueError("incompatible measurement context")
    return {
        "corpora": sorted([[r.corpus, r.corpus_sha256] for r in rows]),
        "protocol": list(compatibility(runs[0])),
        "calculator": CALCULATOR_VERSION,
        "timing": "lz77+encode; median of paired stage sums per file",
        "compression": "equal-corpus-mean-of-nonempty-file-ratios",
        "speed": "equal-corpus-mean-of-per-file-median-time-ratios",
    }


def aggregate(session: Session, rows: Sequence[BenchmarkRun]) -> BenchmarkAggregation:
    """Create immutable evidence, atomically and idempotently, without publication."""
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
        statistics={**timing_statistics(rows), "compression": compression_statistics(rows)},
        raw_bytes=values.raw_bytes,
        bytes=values.bytes,
        incumbent_bytes=values.incumbent_bytes,
        parse_seconds=values.parse_seconds,
        compression_seconds=values.compression_seconds,
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
    session: Session, submission_id: int, aggregation_id: int, *, speed_floor: float | None = None
) -> None:
    """Bind verified source to selected evidence; acceptance/registration stay separate."""
    del speed_floor  # Legacy keyword retained; scoring admission owns the limits.
    publication_lock(session)
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
    for field in (
        "raw_bytes",
        "bytes",
        "incumbent_bytes",
        "parse_seconds",
        "compression_seconds",
        "incumbent_seconds",
    ):
        if getattr(aggregation, field) != getattr(values, field):
            raise ValueError("aggregation no longer matches evidence")
    # Benchmark publication preserves evidence regardless of reward eligibility.
    # The legacy speed_floor argument is retained for callers; admission owns bounds.
    for field in (
        "raw_bytes",
        "bytes",
        "incumbent_bytes",
        "parse_seconds",
        "compression_seconds",
        "incumbent_seconds",
    ):
        setattr(submission, field, getattr(values, field))
    submission.time_ratio = values.time_ratio
    submission.measured_source_sha256 = values.source_sha256
    submission.aggregation_id = aggregation.id
