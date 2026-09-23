"""How this validator's weight on Subnet 66 is divided: the treasury, and the competition.

This weight setter is the only process on the validator that calls set_weights. It took that
job over from conjectures-validator's emissions worker, which gave treasury uid 121 all of the
weight every epoch; two processes setting weights with one hotkey on one subnet would each
overwrite the other's vector every epoch. So the vector set here is the whole validator's:

    treasury share   ->  the treasury uid
    competition share -> the competition's own vector (`scoring.to_vector`), scaled down,
                         including whatever that vector burns

The shares and the mainnet treasury uid are code constants, as they were in the emissions
worker: changing where emission goes is a reviewed code change, never an environment edit on a
running validator.

Failing closed means paying the treasury. If scoring fails or the competition's vector cannot be
submitted, the whole weight goes to the treasury for that epoch rather than the epoch being
skipped, because an epoch's weight cannot be set retroactively and a skipped one pays nobody.
"""

from __future__ import annotations

from chain.types import MetagraphView, WeightPlan

# Subnet 66 on mainnet, and the conjectures.io treasury's uid on it.
MAINNET_NETUID = 66
TREASURY_UID = 121

# The competition's share of the validator's weight, in basis points; the treasury has the rest.
COMPETITION_BPS = 2_000
TREASURY_BPS = 10_000 - COMPETITION_BPS
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


def split(
    competition: WeightPlan | None,
    meta: MetagraphView,
    *,
    treasury_uid: int,
    competition_bps: int = COMPETITION_BPS,
    reason: str | None = None,
) -> WeightPlan:
    """The validator's vector: the treasury share plus the competition's, scaled to its share.

    `competition` is None, or unsubmittable, when there is no competition vector to pay this
    epoch -- scoring failed, or its burn uid is gone. The treasury is then paid everything, and
    `reason` (or the competition plan's own) says why in the summary.
    """
    if treasury_uid not in meta.uids:
        absent = f"treasury uid {treasury_uid} absent from the metagraph"
        return WeightPlan((), (), False, absent, "")
    uids = tuple(meta.uids)
    by_uid = dict.fromkeys(uids, 0.0)

    if competition is None or not competition.submittable:
        why = reason or (competition.skip_reason if competition is not None else None)
        by_uid[treasury_uid] = 1.0
        summary = f"treasury=1.000->uid{treasury_uid} (competition unpaid: {why or 'no vector'})"
        return WeightPlan(uids, tuple(by_uid[uid] for uid in uids), True, None, summary)

    share = competition_bps / 10_000
    for uid, weight in zip(competition.uids, competition.weights, strict=True):
        if uid not in by_uid:
            # Both vectors are built from the same metagraph, so this is a bug, not a state.
            raise ValueError(f"competition vector names uid {uid}, absent from the metagraph")
        by_uid[uid] += weight * share
    by_uid[treasury_uid] += 1.0 - share
    summary = (
        f"treasury={1.0 - share:.3f}->uid{treasury_uid} "
        f"competition={share:.3f} [{competition.summary}]"
    )
    return WeightPlan(uids, tuple(by_uid[uid] for uid in uids), True, None, summary)


__all__ = [
    "COMPETITION_BPS",
    "MAINNET_NETUID",
    "TREASURY_BPS",
    "TREASURY_UID",
    "split",
    "treasury_uid_for",
]
