"""Scale competition allocations without redistributing unpaid baseline shares."""

from __future__ import annotations

import math

from chain.types import MetagraphView, WeightPlan


def reward_vector(
    weights: dict[str, float],
    meta: MetagraphView,
    *,
    collector_uid: int,
    competition_share: float,
) -> WeightPlan:
    if not 0 <= competition_share <= 1:
        raise ValueError("competition_share must be between 0 and 1")
    if any(not math.isfinite(w) or w < 0 for w in weights.values()):
        raise ValueError("competition weights must be finite and nonnegative")
    if sum(weights.values()) > 1 + 1e-9:
        raise ValueError("competition weights must sum to at most one")
    if collector_uid not in meta.uids:
        return WeightPlan((), (), False, "reward collector absent from the metagraph", "")
    by_uid = dict.fromkeys(meta.uids, 0.0)
    for hotkey, weight in weights.items():
        uid = meta.uid_by_hotkey.get(hotkey)
        if uid in by_uid and uid != collector_uid:
            by_uid[uid] += competition_share * weight
    miner_total = sum(by_uid.values())
    by_uid[collector_uid] = max(0.0, 1 - miner_total)
    summary = (
        f"competition_share={competition_share:.6f} "
        f"miner_total={miner_total:.6f} "
        f"collector={by_uid[collector_uid]:.6f}->uid{collector_uid}; "
        "score snapshots are fractions of the competition budget"
    )
    return WeightPlan(meta.uids, tuple(by_uid[uid] for uid in meta.uids), True, None, summary)
