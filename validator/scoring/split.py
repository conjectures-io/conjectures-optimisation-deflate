"""How this validator's weight on Subnet 66 is divided: the treasury, and the competition.

This weight setter is the only process on the validator that calls set_weights. It took that
job over from conjectures-validator's emissions worker, which gave treasury uid 121 all of the
weight every epoch; two processes setting weights with one hotkey on one subnet would each
overwrite the other's vector every epoch. So the vector set here is the whole validator's:

    treasury share    ->  the treasury uid
    competition share ->  miners by score (`scoring.routing.reward_vector`), multiplied by the
                          share without renormalizing; whatever the competition does not pay a
                          miner -- baselines, deregistered hotkeys, what neither scoring
                          component claimed -- goes to the treasury, not the burn uid

The shares and the mainnet treasury uid are code constants, as they were in the emissions
worker: changing where emission goes on netuid 66 is a reviewed code change, never an
environment edit on a running validator. Off mainnet both are configurable, because uid 121
means nothing on a testnet.

Failing closed means paying the treasury. If scoring fails, the whole weight goes to the
treasury for that epoch rather than the epoch being skipped, because an epoch's weight cannot be
set retroactively and a skipped one pays nobody. The one skip is a treasury that is not in the
metagraph (or whose pinned hotkey is not where it should be): then there is no vector that sums
to one without paying a stranger the treasury's share.
"""

from __future__ import annotations

import math
from collections.abc import Mapping

from chain.types import MetagraphView, WeightPlan
from scoring.routing import reward_vector

# Subnet 66 on mainnet, and the conjectures.io treasury's uid on it.
MAINNET_NETUID = 66
TREASURY_UID = 121

# The competition's share of the validator's weight, in basis points; the treasury has the rest.
COMPETITION_BPS = 2_000
TREASURY_BPS = 10_000 - COMPETITION_BPS
COMPETITION_SHARE = COMPETITION_BPS / 10_000
assert 0 <= COMPETITION_BPS <= 10_000, "the competition's share must be between 0 and 100%"


def treasury_uid_for(netuid: int, override: int | None, *, burn_uid: int) -> int:
    """The uid the treasury share goes to on `netuid`.

    Fixed on mainnet: an override there must agree with the constant or the worker refuses to
    start. Anywhere else -- a testnet, a localnet -- uid 121 means nothing, so the override is
    used, and without one the treasury share burns with the rest.
    """
    if netuid == MAINNET_NETUID:
        if override is not None and override != TREASURY_UID:
            raise ValueError(
                f"the treasury uid on netuid {MAINNET_NETUID} is {TREASURY_UID}, a code constant; "
                f"WEIGHT_TREASURY_UID={override} is refused"
            )
        return TREASURY_UID
    return burn_uid if override is None else override


def competition_share_for(netuid: int, override: float | None) -> float:
    """The competition's fraction of the validator's weight on `netuid`.

    Fixed on mainnet at `COMPETITION_BPS`, like the treasury uid: an override there must agree
    or the worker refuses to start. Off mainnet the override (0..1) is used.
    """
    if override is not None and not (math.isfinite(override) and 0 <= override <= 1):
        raise ValueError("WEIGHT_COMPETITION_SHARE must be between 0 and 1")
    if netuid == MAINNET_NETUID:
        if override is not None and not math.isclose(override, COMPETITION_SHARE, abs_tol=1e-9):
            raise ValueError(
                f"the competition's share on netuid {MAINNET_NETUID} is {COMPETITION_SHARE}, "
                f"a code constant; WEIGHT_COMPETITION_SHARE={override} is refused"
            )
        return COMPETITION_SHARE
    return COMPETITION_SHARE if override is None else override


def resolve_treasury(
    meta: MetagraphView, *, netuid: int, treasury_uid: int, treasury_hotkey: str | None
) -> tuple[int | None, str | None]:
    """This epoch's treasury uid, or None and why there is none.

    A pinned hotkey follows the treasury if its uid changes, and refuses to pay a uid that was
    reassigned to somebody else. On mainnet it is a check, not a relocation: the uid stays the
    code constant, and a hotkey found anywhere else skips the epoch.
    """
    if treasury_hotkey is None:
        return treasury_uid, None
    uid = meta.uid_by_hotkey.get(treasury_hotkey)
    if uid is None or uid not in meta.uids:
        return None, f"treasury hotkey {treasury_hotkey} absent from the metagraph"
    if netuid == MAINNET_NETUID and uid != TREASURY_UID:
        return None, (
            f"treasury hotkey {treasury_hotkey} is at uid {uid}, not the treasury uid "
            f"{TREASURY_UID} on netuid {MAINNET_NETUID}"
        )
    return uid, None


def _absent(treasury_uid: int, meta: MetagraphView) -> WeightPlan | None:
    if treasury_uid not in meta.uids:
        return WeightPlan(
            (), (), False, f"treasury uid {treasury_uid} absent from the metagraph", ""
        )
    return None


def split(
    weights: Mapping[str, float] | None,
    meta: MetagraphView,
    *,
    treasury_uid: int,
    competition_share: float = COMPETITION_SHARE,
    reason: str | None = None,
) -> WeightPlan:
    """The validator's vector: miners paid their score times the competition's share, and the
    treasury everything else.

    `weights` are the competition-local fractions from `scoring.score` (they sum to at most
    one). None means there is no competition vector this epoch -- scoring failed -- and the
    treasury is paid everything, with `reason` in the summary.
    """
    if (absent := _absent(treasury_uid, meta)) is not None:
        return absent
    uids = tuple(meta.uids)
    if weights is None:
        by_uid = dict.fromkeys(uids, 0.0)
        by_uid[treasury_uid] = 1.0
        summary = f"treasury=1.000->uid{treasury_uid} (competition unpaid: {reason or 'no vector'})"
        return WeightPlan(uids, tuple(by_uid[uid] for uid in uids), True, None, summary)

    plan = reward_vector(
        dict(weights), meta, collector_uid=treasury_uid, competition_share=competition_share
    )
    if not plan.submittable:
        return plan
    by_uid = dict(zip(plan.uids, plan.weights, strict=True))
    miners = ", ".join(
        f"uid{uid}={w:.3f}" for uid, w in sorted(by_uid.items()) if uid != treasury_uid and w > 0
    )
    summary = (
        f"treasury={by_uid[treasury_uid]:.3f}->uid{treasury_uid} miners=[{miners}] [{plan.summary}]"
    )
    return WeightPlan(plan.uids, plan.weights, True, None, summary)


def burn(
    meta: MetagraphView,
    *,
    treasury_uid: int,
    burn_uid: int,
    competition_share: float = COMPETITION_SHARE,
) -> WeightPlan:
    """Burn mode: the competition's share burns; the treasury's is not the competition's to burn.

    A burn uid missing from the metagraph cannot take the competition's share, so the treasury
    is paid everything rather than the epoch being skipped.
    """
    if (absent := _absent(treasury_uid, meta)) is not None:
        return absent
    if burn_uid not in meta.uids:
        return split(None, meta, treasury_uid=treasury_uid, reason=f"burn uid {burn_uid} absent")
    uids = tuple(meta.uids)
    by_uid = dict.fromkeys(uids, 0.0)
    by_uid[burn_uid] += competition_share
    by_uid[treasury_uid] += 1.0 - competition_share
    summary = (
        f"treasury={1.0 - competition_share:.3f}->uid{treasury_uid} "
        f"burn={competition_share:.3f}->uid{burn_uid} (burn mode)"
    )
    return WeightPlan(uids, tuple(by_uid[uid] for uid in uids), True, None, summary)


__all__ = [
    "COMPETITION_BPS",
    "COMPETITION_SHARE",
    "MAINNET_NETUID",
    "TREASURY_BPS",
    "TREASURY_UID",
    "burn",
    "competition_share_for",
    "resolve_treasury",
    "split",
    "treasury_uid_for",
]
