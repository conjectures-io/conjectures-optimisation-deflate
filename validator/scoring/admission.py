"""Statistical admission policy, independent of database and service deployment."""

from __future__ import annotations

import datetime as dt
import math
from collections.abc import Sequence
from typing import Literal, Protocol, TypeVar

POLICY_VERSION = "fixed-corpus-speed-v1"
BASELINE_ORDER_VERSION = "examples-slow-to-fast-v2"
# Frozen from the 2026-09-24 preview's incumbent-normalized scored times.
# Never re-sort from noisy measurements; changes require a version bump and replay.
BASELINE_ORDER = (
    "optimal-iter",
    "optimal",
    "mo-lazy",
    "lazy",
    "hc-d64",
    "no-lz77",
    "hash-chains",
    "hc-d4",
    "template",
)
ADMITTED = {"passed", "not_required"}


class Point(Protocol):
    """The five fields this policy reads off a scored submission.

    Structural rather than db.scoring.ScoredSubmission itself: this module is the
    statistical policy, independent of the database (see the module docstring), so it
    is written against the shape it needs, not the store's concrete type. Declared as
    read-only properties, not plain fields, because ScoredSubmission is a frozen
    dataclass -- a plain-field protocol would demand a *writable* attribute, which a
    frozen dataclass structurally is not.
    """

    @property
    def baseline_key(self) -> str | None: ...
    @property
    def submitted_at(self) -> dt.datetime: ...
    @property
    def submission_id(self) -> int: ...
    @property
    def pareto_time(self) -> float: ...
    @property
    def ratio_pct(self) -> float: ...


Outcome = Literal["dominated", "test", "not_required"]

P = TypeVar("P", bound=Point)


def ordered_candidates(points: Sequence[P]) -> list[P]:
    unknown = {
        p.baseline_key for p in points if p.baseline_key and not p.baseline_key.startswith("local:")
    } - set(BASELINE_ORDER)
    if unknown:
        raise ValueError(f"baselines absent from admission manifest: {sorted(unknown)}")
    return sorted(
        points,
        key=lambda p: (
            (0, BASELINE_ORDER.index(p.baseline_key), p.submitted_at, p.submission_id)
            if p.baseline_key in BASELINE_ORDER
            else (1, 0, p.submitted_at, p.submission_id)
        ),
    )


def dominates(a: Point, b: Point) -> bool:
    # Equality preserves the previously admitted point, preventing duplicate rewards.
    return a.pareto_time <= b.pareto_time and a.ratio_pct <= b.ratio_pct


def select_reference(frontier: Sequence[P], candidate: P) -> tuple[Outcome, P | None]:
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


def advance(frontier: Sequence[P], candidate: P, outcome: str) -> list[P]:
    if outcome not in ADMITTED:
        return list(frontier)
    return sorted(
        [p for p in frontier if not dominates(candidate, p)] + [candidate],
        key=lambda p: (p.pareto_time, p.submission_id),
    )
