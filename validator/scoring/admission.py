"""Statistical admission policy, independent of database and service deployment."""

from __future__ import annotations

import math

POLICY_VERSION = "fixed-corpus-speed-v1"
BASELINE_ORDER_VERSION = "examples-v1"
# Append new entries and bump the version; never infer admission order from discovery.
BASELINE_ORDER = (
    "template",
    "hash-chains",
    "hc-d4",
    "hc-d64",
    "lazy",
    "mo-lazy",
    "no-lz77",
    "optimal",
    "optimal-iter",
)
ADMITTED = {"passed", "not_required"}


def ordered_candidates(points):
    unknown = {p.baseline_key for p in points if p.baseline_key} - set(BASELINE_ORDER)
    if unknown:
        raise ValueError(f"baselines absent from admission manifest: {sorted(unknown)}")
    return sorted(
        points,
        key=lambda p: (
            (0, BASELINE_ORDER.index(p.baseline_key), p.submitted_at, p.submission_id)
            if p.baseline_key
            else (1, 0, p.submitted_at, p.submission_id)
        ),
    )


def dominates(a, b):
    # Equality preserves the previously admitted point, preventing duplicate rewards.
    return a.pareto_time <= b.pareto_time and a.ratio_pct <= b.ratio_pct


def select_reference(frontier, candidate):
    """Return (outcome, reference); `test` requires evidence before frontier changes."""
    for p in [*frontier, candidate]:
        if not math.isfinite(p.pareto_time) or p.pareto_time <= 0:
            raise ValueError("positive finite scored time required")
        if not math.isfinite(p.ratio_pct) or p.ratio_pct < 0:
            raise ValueError("finite nonnegative compression ratio required")
    ordered = sorted(frontier, key=lambda p: (p.pareto_time, p.submission_id))
    if any(dominates(p, candidate) for p in ordered):
        return "dominated", None
    equal = [p for p in ordered if p.ratio_pct == candidate.ratio_pct]
    if equal:
        return "test", equal[0]
    hypothetical = [p for p in ordered if not dominates(candidate, p)]
    neighbor = next((p for p in hypothetical if p.pareto_time > candidate.pareto_time), None)
    return ("test", neighbor) if neighbor is not None else ("not_required", None)


def advance(frontier, candidate, outcome):
    if outcome not in ADMITTED:
        return list(frontier)
    return sorted(
        [p for p in frontier if not dominates(candidate, p)] + [candidate],
        key=lambda p: (p.pareto_time, p.submission_id),
    )
