"""Scoring boundaries, independent of benchmark execution limits."""

import math


def bounds_detail(point, config):
    time_ratio = point.normalized_time_ratio
    if time_ratio is None:
        time_ratio = point.time_s / point.incumbent_seconds
    violations = []
    if not math.isfinite(time_ratio) or time_ratio <= 0 or time_ratio > config.speed_floor:
        violations.append("time-ratio-limit")
    if (
        not math.isfinite(point.ratio_pct)
        or point.ratio_pct < 0
        or point.ratio_pct > config.max_ratio_pct
    ):
        violations.append("compression-ratio-limit")
    return {
        "eligible": not violations,
        "violations": violations,
        "time_ratio": time_ratio,
        "compression_pct": point.ratio_pct,
        "max_time_ratio": config.speed_floor,
        "max_compression_pct": config.max_ratio_pct,
    }
