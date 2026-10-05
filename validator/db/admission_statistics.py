"""Fixed-corpus repetition bootstrap for a single admission comparison.

Files are fixed weighted strata, not a sample of possible future inputs. Methods
are paired only inside a recorded interleaved round. Different run IDs are never
paired. Shared run observations reuse the same bootstrap draws.
"""

from __future__ import annotations

import math
import random
import statistics
from collections.abc import Sequence
from typing import TypedDict, cast

from bench.hashing import sha256
from bench.results import INCUMBENT

from .aggregation import reduce_runs, validate_evidence
from .models import BenchmarkRun

METHOD_VERSION = "mixed-files-independent-runs-percentile-v2"
MIN_REPETITIONS = 3
DEFAULT_DRAWS = 2000

# corpus, corpus_sha256, file sha256, file path, raw byte size.
FileIdentity = tuple[str, str, str, str, int]
# The measured run id, the run's own content hash and the file path -- what makes an
# observation reusable across a resample: the same triple always draws the same indices.
ObservationKey = tuple[int, str, str]


class FileEvidence(TypedDict):
    samples: list[list[float]]
    paired: bool
    observation_key: ObservationKey
    run_id: int
    output_bytes: int
    incumbent_bytes: int


def quantile(values: Sequence[float], probability: float) -> float:
    """Linear interpolation at (n-1)*p, including both endpoints."""
    ordered = sorted(values)
    index = (len(ordered) - 1) * probability
    low = int(index)
    high = min(low + 1, len(ordered) - 1)
    return ordered[low] + (ordered[high] - ordered[low]) * (index - low)


def evidence_files(rows: Sequence[BenchmarkRun]) -> dict[FileIdentity, FileEvidence]:
    reduce_runs(rows)  # Includes source, manifest, protocol and complete-sample validation.
    files: dict[FileIdentity, FileEvidence] = {}
    for row in sorted(rows, key=lambda r: (r.corpus, r.corpus_sha256)):
        run = validate_evidence(row)
        for file in sorted(run.files, key=lambda f: (f.sha256, f.file)):
            if not file.raw_bytes:
                continue
            # Content plus manifest membership: duplicate bytes in distinct files retain
            # their existing scoring weights. A matching index/path alone is insufficient.
            identity = (row.corpus, row.corpus_sha256, file.sha256, file.file, file.raw_bytes)
            samples: list[list[float]] = []
            orders: list[list[int]] = []
            for name in (row.candidate_method, INCUMBENT):
                reps = sorted(
                    (r for r in file.methods[name].reps if r.phase == "measured"),
                    key=lambda r: r.order_index,
                )
                values = [r.total_s for r in reps]
                if len(values) < MIN_REPETITIONS:
                    raise ValueError(
                        f"{file.file}: at least {MIN_REPETITIONS} measured repetitions required"
                    )
                if any(v is None or not math.isfinite(v) or v <= 0 for v in values):
                    raise ValueError("positive finite total compression samples required")
                samples.append(cast(list[float], values))
                orders.append([r.order_index for r in reps])
            n = len(samples[0])
            if len(samples[1]) != n:
                raise ValueError("incomplete candidate/incumbent rounds")
            # Explicit two-way zip, not zip(*orders, ...): orders always holds exactly
            # the candidate's and the incumbent's own order-index lists, but pyright
            # can't see that through a starred unpack of a plain list, and falls back
            # to Any per element.
            blocks = [sorted(pair) for pair in zip(orders[0], orders[1], strict=True)]
            paired = all(a < b for a, b in blocks) and all(
                blocks[i][1] < blocks[i + 1][0] for i in range(n - 1)
            )
            # validate_evidence already required a non-negative output size for every
            # file, for both the candidate method and INCUMBENT.
            output_bytes = file.methods[row.candidate_method].output_bytes
            incumbent_bytes = file.methods[INCUMBENT].output_bytes
            assert output_bytes is not None
            assert incumbent_bytes is not None
            files[identity] = {
                "samples": samples,
                "paired": paired,
                "observation_key": (row.id, sha256(row.raw_data), file.file),
                "run_id": row.id,
                "output_bytes": output_bytes,
                "incumbent_bytes": incumbent_bytes,
            }
    return files


def coordinate(
    files: dict[FileIdentity, FileEvidence],
    resampled: dict[ObservationKey, list[float]] | None = None,
) -> float:
    corpora: dict[tuple[str, str], list[float]] = {}
    for identity, file in files.items():
        if resampled is None:
            medians = [statistics.median(v) for v in file["samples"]]
        else:
            medians = resampled[file["observation_key"]]
        corpus_identity = (identity[0], identity[1])
        corpora.setdefault(corpus_identity, []).append(medians[0] / medians[1])
    return statistics.mean(statistics.mean(values) for values in corpora.values())


class PerFileComparison(TypedDict):
    corpus: str
    corpus_sha256: str
    sha256: str
    file: str
    raw_bytes: int
    candidate_run_id: int
    reference_run_id: int
    candidate_time_ratio: float
    reference_time_ratio: float
    gain_pct: float


class AdmissionComparison(TypedDict):
    method_version: str
    draws: int
    seed: int
    min_repetitions: int
    candidate_time: float
    reference_time: float
    gain_pct: float
    lower_pct: float
    upper_pct: float
    confidence: float
    threshold_pct: int
    interval: str
    quantile: str
    outcome: str
    uncertainty_target: str
    resampling: str
    pairing: str
    paired_file_observations: int
    file_observations: int
    shared_observations: int
    limitations: str
    per_file_sizes_equal: bool
    file_sets_equal: bool
    files: list[PerFileComparison]
    file_wins: int
    file_ties: int


def compare(
    candidate_rows: Sequence[BenchmarkRun],
    reference_rows: Sequence[BenchmarkRun],
    *,
    draws: int = DEFAULT_DRAWS,
) -> AdmissionComparison:
    if draws < 100:
        raise ValueError("at least 100 bootstrap draws required")
    candidate = evidence_files(candidate_rows)
    reference = evidence_files(reference_rows)
    shared = candidate.keys() & reference.keys()
    candidate_time, reference_time = coordinate(candidate), coordinate(reference)
    point_gain = 100 * (1 - candidate_time / reference_time)
    observations: dict[ObservationKey, FileEvidence] = {}
    for file in [*candidate.values(), *reference.values()]:
        observations[file["observation_key"]] = file
    seed = int(sha256([METHOD_VERSION, sorted(observations)])[:16], 16)
    rng = random.Random(seed)
    gains: list[float] = []
    for _ in range(draws):
        resampled: dict[ObservationKey, list[float]] = {}
        for key, file in sorted(observations.items()):
            values = file["samples"]
            n = len(values[0])
            first = [rng.randrange(n) for _ in range(n)]
            second = first if file["paired"] else [rng.randrange(n) for _ in range(n)]
            resampled[key] = [
                statistics.median([v[i] for i in indices])
                for v, indices in zip(values, (first, second), strict=True)
            ]
        gains.append(
            100 * (1 - coordinate(candidate, resampled) / coordinate(reference, resampled))
        )
    if not all(math.isfinite(g) for g in [point_gain, *gains]):
        raise ValueError("nonfinite bootstrap gain")
    lower, upper = quantile(gains, 0.05), quantile(gains, 0.95)
    per_file: list[PerFileComparison] = []
    for identity in sorted(shared):
        c = candidate[identity]
        r = reference[identity]
        ct, rt = [
            statistics.median(f["samples"][0]) / statistics.median(f["samples"][1]) for f in (c, r)
        ]
        per_file.append(
            {
                "corpus": identity[0],
                "corpus_sha256": identity[1],
                "sha256": identity[2],
                "file": identity[3],
                "raw_bytes": identity[4],
                "candidate_run_id": c["run_id"],
                "reference_run_id": r["run_id"],
                "candidate_time_ratio": ct,
                "reference_time_ratio": rt,
                "gain_pct": 100 * (1 - ct / rt),
            }
        )
    return {
        "method_version": METHOD_VERSION,
        "draws": draws,
        "seed": seed,
        "min_repetitions": MIN_REPETITIONS,
        "candidate_time": candidate_time,
        "reference_time": reference_time,
        "gain_pct": point_gain,
        "lower_pct": lower,
        "upper_pct": upper,
        "confidence": 0.95,
        "threshold_pct": 0,
        "interval": "central 90% percentile interval (5th–95th percentiles)",
        "quantile": "linear interpolation at (n-1)*p",
        "outcome": "passed" if lower > 0 else "inconclusive",
        "uncertainty_target": "repetition timing within each recorded corpus",
        "resampling": "each run's fixed files; repetitions within files; independent distinct runs",
        "pairing": "within-run interleaved rounds where order indices establish blocks",
        "paired_file_observations": sum(f["paired"] for f in observations.values()),
        "file_observations": len(observations),
        "shared_observations": len(candidate) + len(reference) - len(observations),
        "limitations": "excludes host/corpus drift and cross-file dependence; "
        "nominal coverage is not guaranteed for small samples",
        "per_file_sizes_equal": all(
            candidate[k]["output_bytes"] == reference[k]["output_bytes"] for k in shared
        ),
        "file_sets_equal": candidate.keys() == reference.keys(),
        "files": per_file,
        "file_wins": sum(f["gain_pct"] > 0 for f in per_file),
        "file_ties": sum(f["gain_pct"] == 0 for f in per_file),
    }
