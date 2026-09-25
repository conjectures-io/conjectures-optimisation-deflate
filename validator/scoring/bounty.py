"""The submission bounty: the most alpha one (hotkey, submission) pair can ever earn.

A frontier point keeps its weight for as long as it stands, so without a limit one early
submission could collect emission indefinitely. `ALPHA_TOTAL_SUBMISSION_BOUNTY` (default
3600 alpha, half a day of the subnet's total alpha emission) bounds it: once a pair has
received that much, or would pass it before a new vector could stop paying it, its weight
is 0 and its share goes to the treasury, whatever its current position or incentive.

What a pair has received is read from the chain, not inferred from this validator's
weights: after every epoch the weight setter records each uid's `Emission` and credits it
to the submissions this validator was paying that hotkey for (`attribute`). Everything
here is pure; `db.bounty` does the reading and writing.

The limit is sticky. A pair that reaches it stays capped even though its observed rate
then falls to zero, because a total that could reopen would pay it again.
"""

from __future__ import annotations

import dataclasses as dc
import math
import os
from collections.abc import Mapping, Sequence

from chain.types import EpochEmission

from .combine import HotkeyScore, Scoring

RAO_PER_ALPHA = 1_000_000_000
DEFAULT_BOUNTY_ALPHA = 3600.0
BOUNTY_CAPPED = "bounty-cap"


def bounty_alpha_from_env(env: Mapping[str, str] | None = None) -> float:
    raw = (os.environ if env is None else env).get("ALPHA_TOTAL_SUBMISSION_BOUNTY", "").strip()
    if not raw:
        return DEFAULT_BOUNTY_ALPHA
    try:
        value = float(raw)
    except ValueError:
        raise ValueError(f"ALPHA_TOTAL_SUBMISSION_BOUNTY={raw!r} is not a number") from None
    if not math.isfinite(value) or value <= 0:
        raise ValueError("ALPHA_TOTAL_SUBMISSION_BOUNTY must be a positive number of alpha")
    return value


@dc.dataclass(frozen=True, slots=True)
class Ledger:
    """What one submission has received so far, in alpha rao."""

    earned_rao: int = 0
    # Its credit in the most recent epoch that credited it: the observed rate.
    last_epoch_rao: int = 0
    capped: bool = False


@dc.dataclass(frozen=True, slots=True)
class Outlook:
    """How the next vector turns into alpha, from the most recent recorded epoch."""

    # Alpha rao the epoch paid for incentive, over all uids.
    miner_pool_rao: int = 0
    # Epochs a vector set now is paid for before a later one replaces it: the next epoch,
    # plus the commit-reveal delay during which the vector already set keeps paying.
    horizon_epochs: int = 1


@dc.dataclass(frozen=True, slots=True)
class NewCap:
    submission_id: int
    hotkey: str
    earned_rao: int
    projected_rao: int


@dc.dataclass(frozen=True, slots=True)
class Credit:
    """One submission's share of one uid's emission in one epoch."""

    submission_id: int
    hotkey: str
    coldkey: str
    uid: int
    alpha_rao: int
    weight_set_id: int


@dc.dataclass(frozen=True, slots=True)
class PaidSet:
    """An accepted weight set, and the submissions it paid each hotkey for."""

    weight_set_id: int
    block: int
    paid: Mapping[str, Sequence[tuple[int, float]]]


def attribute(epoch: EpochEmission, sets: Sequence[PaidSet]) -> list[Credit]:
    """Credit each uid's emission to the submissions this validator paid its hotkey for.

    The vector consensus read at `epoch_block` is the one set `reveal_epochs` epochs before
    it, so a set at or before that point is preferred, newest first; a later one covers a
    hotkey the earlier sets did not pay. A hotkey paid for several submissions splits its
    emission by their weights. Emission to a hotkey none of these sets paid is not this
    competition's to count, and is left out.
    """
    cutoff = epoch.epoch_block - epoch.reveal_epochs * (epoch.tempo + 1)
    eligible = sorted(
        (s for s in sets if s.block <= epoch.epoch_block), key=lambda s: -s.weight_set_id
    )
    ordered = [s for s in eligible if s.block <= cutoff] + [s for s in eligible if s.block > cutoff]
    credits: list[Credit] = []
    for neuron in epoch.neurons:
        if neuron.emission_rao <= 0:
            continue
        chosen = next((s for s in ordered if s.paid.get(neuron.hotkey)), None)
        if chosen is None:
            continue
        paid = [(sid, w) for sid, w in chosen.paid[neuron.hotkey] if w > 0]
        total = sum(w for _, w in paid)
        given = 0
        for index, (sid, weight) in enumerate(sorted(paid)):
            # Integer rao; the last share takes the rounding so nothing is lost.
            amount = (
                neuron.emission_rao - given
                if index == len(paid) - 1
                else int(neuron.emission_rao * weight / total)
            )
            given += amount
            credits.append(
                Credit(sid, neuron.hotkey, neuron.coldkey, neuron.uid, amount, chosen.weight_set_id)
            )
    return credits


def apply(
    result: Scoring,
    ledgers: Mapping[int, Ledger],
    *,
    bounty_alpha: float,
    outlook: Outlook,
    competition_share: float,
) -> tuple[Scoring, list[NewCap]]:
    """Zero every pair that has reached the bounty, or would before it could be stopped.

    A pair's next payments are projected as the larger of what it received in its last
    credited epoch and what this vector would pay it (its weight times the competition's
    share times the epoch's miner pool), over the outlook's horizon. The projection is
    deliberately the cautious one: stopping a pair a little short of the bounty costs it
    at most a few epochs' pay, and passing it cannot be undone.
    """
    cap_rao = int(bounty_alpha * RAO_PER_ALPHA)
    scores: list[HotkeyScore] = []
    caps: list[NewCap] = []
    for s in result.scores:
        if s.hotkey is None or s.baseline_key is not None:
            scores.append(s)
            continue
        ledger = ledgers.get(s.submission_id, Ledger())
        capped = ledger.capped
        if not capped and s.payable_weight > 0:
            expected = int(s.payable_weight * competition_share * outlook.miner_pool_rao)
            projected = outlook.horizon_epochs * max(ledger.last_epoch_rao, expected)
            if ledger.earned_rao + projected > cap_rao:
                capped = True
                caps.append(NewCap(s.submission_id, s.hotkey, ledger.earned_rao, projected))
        if capped and s.payable_weight > 0:
            s = dc.replace(s, payable_weight=0.0, burn_reason=BOUNTY_CAPPED)
        scores.append(dc.replace(s, bounty_rao=ledger.earned_rao, bounty_capped=capped))
    return dc.replace(result, scores=tuple(scores)), caps


def publication(result: Scoring, *, bounty_alpha: float) -> dict[str, object]:
    """The pass's bounty totals as the read API publishes them: api_snapshot["bounty"]."""
    return {
        "limit_alpha": bounty_alpha,
        "limit_rao": int(bounty_alpha * RAO_PER_ALPHA),
        "submissions": [
            {
                "submission_id": s.submission_id,
                "hotkey": s.hotkey,
                "earned_rao": s.bounty_rao,
                "earned_alpha": s.bounty_rao / RAO_PER_ALPHA,
                "capped": s.bounty_capped,
            }
            for s in result.scores
            if s.bounty_rao is not None
        ],
    }


__all__ = [
    "BOUNTY_CAPPED",
    "DEFAULT_BOUNTY_ALPHA",
    "RAO_PER_ALPHA",
    "Credit",
    "Ledger",
    "NewCap",
    "Outlook",
    "PaidSet",
    "apply",
    "attribute",
    "bounty_alpha_from_env",
    "publication",
]
