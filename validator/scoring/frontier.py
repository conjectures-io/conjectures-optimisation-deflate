"""The 60% share: turn accepted submissions into a frontier, and weigh it.

One point is one verified submission; payout ownership is applied after weighting. Everything
below is pure -- it takes the rows the store already read and returns numbers -- so the
rule can be exercised without a database or a chain.
"""

from __future__ import annotations

import dataclasses as dc
from collections.abc import Sequence

from db.scoring import ScoredSubmission

from .config import ScoringConfig
from .eligibility import bounds_detail
from .pareto import Boundaries, Point, pareto_front, weigh


@dc.dataclass(frozen=True, slots=True)
class FrontierScore:
    """What the Pareto component decided, and enough to explain it afterwards."""

    # hotkey -> its share of emission, already scaled by pareto_share.
    weights: dict[str, float]
    # The points as the scorer saw them, by hotkey: what goes into score_snapshots.
    points: dict[str, Point]
    frontier: tuple[str, ...]
    bounds: Boundaries

    def on_frontier(self, hotkey: str) -> bool:
        return hotkey in self.frontier


def to_points(submissions: Sequence[ScoredSubmission]) -> dict[str, Point]:
    # One point per submission. Current evidence uses balanced relative time and
    # compression ratios; legacy standalone inputs retain absolute time coordinates.
    return {
        s.point_id: Point(name=s.point_id, time_s=s.pareto_time, ratio_pct=s.ratio_pct)
        for s in sorted(submissions, key=lambda s: (s.submitted_at, s.submission_id))
    }


def boundaries_for(submissions: Sequence[ScoredSubmission], speed_floor: float) -> Boundaries:
    """Incumbent-relative reference for boundary-based comparison methods.

    The relative time coordinate uses incumbent=1. Scoring eligibility uses
    that same coordinate; execution timeouts are independent.

    Every accepted submission carries the incumbent's time as measured on the same run,
    so they should agree; they can differ when the operator promoted a new incumbent
    mid-round. The most recent measurement is the one that describes the current gate, so
    that is the one used.
    """
    if not submissions:
        return Boundaries()
    if all(s.normalized_time_ratio is not None for s in submissions):
        return Boundaries.from_incumbent(1.0, speed_floor)
    newest = max(submissions, key=lambda s: (s.submitted_at, s.submission_id))
    return Boundaries.from_incumbent(newest.incumbent_seconds, speed_floor)


def score_frontier(submissions: Sequence[ScoredSubmission], config: ScoringConfig) -> FrontierScore:
    """Weigh the frontier, scaled to the Pareto share of emission.

    A hotkey not on the frontier gets nothing here: it is dominated, meaning some other
    submission is both faster and smaller, and there is no sense in which it bought
    anything. It can still earn from the improvement share, which is the point of having
    two components.
    """
    submissions = [s for s in submissions if bounds_detail(s, config)["eligible"]]
    points = to_points(submissions)
    bounds = dc.replace(
        boundaries_for(submissions, config.speed_floor), ratio_pct=config.max_ratio_pct
    )
    front = pareto_front(list(points.values()))
    raw = weigh(front, bounds, config.method)
    weights = {point_id: 0.0 for point_id in points}
    for hotkey, share in raw.items():
        weights[hotkey] = share * config.pareto_share
    return FrontierScore(
        weights=weights,
        points=points,
        frontier=tuple(p.name for p in front),
        bounds=bounds,
    )
