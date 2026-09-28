"""Both components, added, then turned into a uid-aligned weight vector.

The Pareto frontier takes `pareto_share` -- where the engineering is, and where it stays
rewarded for as long as it stands -- and recent improvement, decaying, takes
`improvement_share`. The competition runs frontier only (1.0/0.0, `.env.example`).

Everything here is pure. `score` takes rows the store read and returns numbers;
`to_vector` takes those numbers and a view of the metagraph and returns the vector. The
worker does the I/O around them.
"""

from __future__ import annotations

import dataclasses as dc
import json
from collections.abc import Sequence

from chain.types import MetagraphView, WeightPlan
from db.scored import ScoredSubmission

from .config import ScoringConfig
from .eligibility import bounds_detail
from .frontier import FrontierScore, score_frontier
from .improvement import Improvement, decay_shares, score_improvements
from .split import TREASURY_UID


@dc.dataclass(frozen=True, slots=True)
class HotkeyScore:
    """One algorithm point, its computed allocation and its payout disposition."""

    hotkey: str | None
    submission_id: int
    time_s: float
    ratio_pct: float
    on_frontier: bool
    pareto_weight: float
    improvement_weight: float
    aggregation_id: int | None = None
    baseline_key: str | None = None
    burn_reason: str | None = None
    payable_weight: float = 0.0
    normalized_time_ratio: float | None = None
    admission_check_id: int | None = None
    admission: dict[str, object] | None = None
    # Alpha rao this pair had received when it was scored, and whether it has reached the
    # submission bounty (`scoring.bounty`). None for a baseline, which is never paid.
    bounty_rao: int | None = None
    bounty_capped: bool = False

    @property
    def combined_weight(self) -> float:
        return self.pareto_weight + self.improvement_weight

    def as_snapshot(self) -> dict[str, object]:
        snapshot: dict[str, object] = dc.asdict(self)
        # The dimensionless coordinate is recoverable from aggregation evidence.
        # Keep the historical snapshot time_s column in actual seconds.
        snapshot.pop("normalized_time_ratio")
        snapshot.pop("admission")
        # Published in the pass's api_snapshot["bounty"]; a capped row's burn_reason says so.
        snapshot.pop("bounty_rao")
        snapshot.pop("bounty_capped")
        snapshot["combined_weight"] = self.combined_weight
        return snapshot


@dc.dataclass(frozen=True, slots=True)
class Scoring:
    scores: tuple[HotkeyScore, ...]
    frontier: FrontierScore
    improvements: tuple[Improvement, ...]
    eligibility_known: bool = False
    api_snapshot: dict[str, object] | None = dc.field(default=None, compare=False, repr=False)

    @property
    def weights(self) -> dict[str, float]:
        weights: dict[str, float] = {}
        for s in self.scores:
            if s.hotkey is not None and s.payable_weight > 0:
                weights[s.hotkey] = weights.get(s.hotkey, 0.0) + s.payable_weight
        return weights

    @property
    def burn_weight(self) -> float:
        return max(0.0, 1.0 - sum(self.weights.values()))

    def snapshots(self) -> list[dict[str, object]]:
        return [s.as_snapshot() for s in self.scores]

    def summary(self) -> str:
        return (
            f"frontier={len(self.frontier.frontier)} "
            f"improvements={len(self.improvements)} burn={self.burn_weight:.3f}"
        )


def score(
    submissions: Sequence[ScoredSubmission],
    history: Sequence[ScoredSubmission],
    config: ScoringConfig,
    *,
    eligible_hotkeys: set[str] | None = None,
) -> Scoring:
    """Score all valid points first; burn ineligible allocations without renormalizing.

    With no metagraph, miner payments are provisional and explicitly labeled.
    The oldest frontier submission per hotkey wins payout eligibility. Recency
    events remain independent: duplicate frontier exclusion does not erase history.
    """
    if len({s.normalized_time_ratio is not None for s in [*submissions, *history]}) > 1:
        raise ValueError("cannot mix absolute and relative time coordinates")
    contexts = {json.dumps(s.context, sort_keys=True) for s in [*submissions, *history]}
    if len(contexts) > 1:
        raise ValueError("cannot score incomparable evaluation contexts")
    if len({s.submission_id for s in submissions}) != len(submissions):
        raise ValueError("duplicate submission IDs")
    from db.admission import admitted

    frontier = score_frontier(
        [s for s in submissions if admitted(s) and bounds_detail(s, config)["eligible"]], config
    )
    _, improvements = score_improvements(
        [s for s in history if admitted(s) and bounds_detail(s, config)["eligible"]], config
    )
    improvement_by_id = {
        event.submission_id: share * config.improvement_share
        for event, share in zip(
            improvements, decay_shares(len(improvements), config.improvement_decay), strict=True
        )
    }
    chosen: dict[str, int] = {}
    ordered = sorted(submissions, key=lambda s: (s.submitted_at, s.submission_id))
    for s in ordered:
        if s.hotkey is not None and s.point_id in frontier.frontier:
            chosen.setdefault(s.hotkey, s.submission_id)
    by_id = {s.submission_id: s for s in [*history, *submissions]}
    scores: list[HotkeyScore] = []
    for sid, s in sorted(by_id.items()):
        pareto = frontier.weights.get(s.point_id, 0.0)
        improvement = improvement_by_id.get(sid, 0.0)
        reason: str | None = None
        payable = pareto + improvement
        if not bounds_detail(s, config)["eligible"]:
            reason, payable = (
                "scoring-bounds:" + ",".join(bounds_detail(s, config)["violations"]),
                0.0,
            )
        elif not admitted(s):
            reason, payable = (
                "admission-" + str((s.admission or {"outcome": "pending"})["outcome"]),
                0.0,
            )
        elif s.baseline_key is not None or s.hotkey is None:
            reason, payable = "baseline", 0.0
        elif eligible_hotkeys is not None and s.hotkey not in eligible_hotkeys:
            reason, payable = "deregistered", 0.0
        elif s.point_id in frontier.frontier and chosen.get(s.hotkey) != sid:
            reason, payable = "duplicate-hotkey", improvement
        elif eligible_hotkeys is None:
            reason = "registration-unknown"
        scores.append(
            HotkeyScore(
                s.hotkey,
                sid,
                s.time_s,
                s.ratio_pct,
                s.point_id in frontier.frontier,
                pareto,
                improvement,
                s.aggregation_id,
                s.baseline_key,
                reason,
                payable,
                s.normalized_time_ratio,
                s.admission_check_id,
                s.admission,
            )
        )
    return Scoring(tuple(scores), frontier, tuple(improvements), eligible_hotkeys is not None)


def to_vector(
    weights: dict[str, float], meta: MetagraphView, *, burn_uid: int = TREASURY_UID
) -> WeightPlan:
    """Map per-hotkey weights onto the metagraph's uids; burn whatever is unclaimed.

    A hotkey that has since deregistered has no uid, so its share cannot be paid to
    anyone -- it burns rather than being redistributed, because redistributing it would
    quietly pay everyone else for someone else's work. Whatever neither component
    claimed burns for the same reason.

    The vector covers every uid in the metagraph, most of them zero: a weight vector is
    a statement about the whole subnet, and omitting a uid is not the same as giving it
    nothing.
    """
    if not meta.uids:
        return WeightPlan((), (), False, "no neurons in the metagraph", "")

    by_uid = {uid: 0.0 for uid in meta.uids}
    paid: dict[int, float] = {}
    unpaid = 0.0
    for hotkey, weight in weights.items():
        uid = meta.uid_by_hotkey.get(hotkey)
        if uid is None or uid not in by_uid or uid == burn_uid:
            unpaid += weight
            continue
        by_uid[uid] += weight
        paid[uid] = paid.get(uid, 0.0) + weight

    burn = max(0.0, 1.0 - sum(paid.values()))
    if burn > 0 and burn_uid not in by_uid:
        return WeightPlan((), (), False, f"burn uid {burn_uid} absent from the metagraph", "")
    if burn > 0:
        by_uid[burn_uid] += burn

    uids = tuple(meta.uids)
    vector = tuple(by_uid[uid] for uid in uids)
    miners = ", ".join(f"uid{uid}={w:.3f}" for uid, w in sorted(paid.items()))
    summary = f"miners=[{miners}] burn={burn:.3f}->uid{burn_uid}"
    if unpaid > 0:
        summary += f" (unregistered={unpaid:.3f})"
    return WeightPlan(uids, vector, True, None, summary)
