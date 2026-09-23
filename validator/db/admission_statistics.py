"""Fixed-corpus repetition bootstrap for a single admission comparison.

Files are fixed weighted strata, not a sample of possible future inputs. Methods
are paired only inside a recorded interleaved round. Different run IDs are never
paired. Shared run observations reuse the same bootstrap draws.
"""

from __future__ import annotations

import math
import random
import statistics
from typing import Any

from bench.results import INCUMBENT
from bench.storage import sha256

from .aggregation import evaluation_context, reduce_runs, validate_evidence

METHOD_VERSION = "fixed-files-independent-runs-percentile-v1"
MIN_REPETITIONS = 3
DEFAULT_DRAWS = 2000


def quantile(values, probability):
    """Linear interpolation at (n-1)*p, including both endpoints."""
    ordered = sorted(values)
    index = (len(ordered) - 1) * probability
    low = int(index)
    high = min(low + 1, len(ordered) - 1)
    return ordered[low] + (ordered[high] - ordered[low]) * (index - low)


def evidence_files(rows):
    reduce_runs(rows)  # Includes source, manifest, protocol and complete-sample validation.
    files = {}
    for row in sorted(rows, key=lambda r: (r.corpus, r.corpus_sha256)):
        run = validate_evidence(row)
        for file in sorted(run.files, key=lambda f: (f.sha256, f.file)):
            if not file.raw_bytes:
                continue
            # Content plus manifest membership: duplicate bytes in distinct files retain
            # their existing scoring weights. A matching index/path alone is insufficient.
            identity = (row.corpus, row.corpus_sha256, file.sha256, file.file, file.raw_bytes)
            samples, orders = [], []
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
                samples.append(values)
                orders.append([r.order_index for r in reps])
            n = len(samples[0])
            if len(samples[1]) != n:
                raise ValueError("incomplete candidate/incumbent rounds")
            blocks = [sorted(pair) for pair in zip(*orders, strict=True)]
            paired = all(a < b for a, b in blocks) and all(
                blocks[i][1] < blocks[i + 1][0] for i in range(n - 1)
            )
            files[identity] = {
                "samples": samples,
                "paired": paired,
                "observation_key": (row.id, sha256(row.raw_data), file.file),
                "run_id": row.id,
                "output_bytes": file.methods[row.candidate_method].output_bytes,
                "incumbent_bytes": file.methods[INCUMBENT].output_bytes,
            }
    return files


def coordinate(files, resampled=None):
    corpora = {}
    for identity, file in files.items():
        if resampled is None:
            medians = [statistics.median(v) for v in file["samples"]]
        else:
            medians = resampled[file["observation_key"]]
        corpora.setdefault(identity[:2], []).append(medians[0] / medians[1])
    return statistics.mean(statistics.mean(values) for values in corpora.values())


def compare(candidate_rows, reference_rows, *, draws=DEFAULT_DRAWS) -> dict[str, Any]:
    if draws < 100:
        raise ValueError("at least 100 bootstrap draws required")
    if evaluation_context(candidate_rows) != evaluation_context(reference_rows):
        raise ValueError("incompatible corpus, protocol or incumbent evidence")
    candidate = evidence_files(candidate_rows)
    reference = evidence_files(reference_rows)
    if candidate.keys() != reference.keys():
        raise ValueError("file content or manifest membership mismatch")
    if any(candidate[k]["incumbent_bytes"] != reference[k]["incumbent_bytes"] for k in candidate):
        raise ValueError("inconsistent incumbent compression evidence")
    candidate_time, reference_time = coordinate(candidate), coordinate(reference)
    point_gain = 100 * (1 - candidate_time / reference_time)
    observations = {}
    for file in [*candidate.values(), *reference.values()]:
        observations[file["observation_key"]] = file
    seed = int(sha256([METHOD_VERSION, sorted(observations)])[:16], 16)
    rng = random.Random(seed)
    gains = []
    for _ in range(draws):
        resampled = {}
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
    per_file = []
    for identity, c in candidate.items():
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
        "uncertainty_target": "repetition timing on the fixed scored corpus",
        "resampling": "fixed files; repetitions within files; independent distinct runs",
        "pairing": "within-run interleaved rounds where order indices establish blocks",
        "paired_file_observations": sum(f["paired"] for f in observations.values()),
        "file_observations": len(observations),
        "shared_observations": len(candidate) + len(reference) - len(observations),
        "limitations": "excludes host drift, cross-file dependence; "
        "nominal coverage is not guaranteed for small samples",
        "per_file_sizes_equal": all(
            candidate[k]["output_bytes"] == reference[k]["output_bytes"] for k in candidate
        ),
        "files": per_file,
        "file_wins": sum(f["gain_pct"] > 0 for f in per_file),
        "file_ties": sum(f["gain_pct"] == 0 for f in per_file),
    }
