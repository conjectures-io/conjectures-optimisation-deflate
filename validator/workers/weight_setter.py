"""Score each cycle, then set the validator's weights when the epoch permits.

    cd validator && python -m workers.weight_setter

The only process on the validator that calls set_weights. The vector it sets is the whole
validator's: the treasury's share to treasury uid 121 and the competition's share by score --
see `scoring.split`, which also says why a failure pays the treasury rather than skipping.
Run it with `WEIGHT_DRY_RUN=0` wherever this validator is expected to set weights at all.

The cadence gate (`chain.schedule.should_set`) and the scoring rule (`scoring`) are both
pure; `step` is the testable unit that puts them together with a `WeightChain`, and `run`
is the loop around it. Each cycle saves scoring before checking registration or timing in a
`weight_sets` row with the per-hotkey reasoning beside it, so a disputed epoch can be
reconstructed from the validator's own records.

Set `WEIGHT_DRY_RUN=1` to compute and record the vector without submitting it. That is
the whole path except the last call, which is what makes it useful before a validator
hotkey is registered.
"""

from __future__ import annotations

import dataclasses as dc
import os
import sys
import time
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import Literal

from loguru import logger

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import db  # noqa: E402
import scoring  # noqa: E402
from chain.schedule import should_set  # noqa: E402
from chain.types import (  # noqa: E402
    BLOCK_SECONDS,
    FINNEY,
    NETUID,
    MetagraphView,
    SubnetParams,
    WeightPlan,
)
from chain.weights import WeightChain  # noqa: E402
from observability.axiom import EventType, Severity, config_error, get_events, init  # noqa: E402
from scoring.split import (  # noqa: E402
    burn,
    competition_share_for,
    resolve_treasury,
    split,
    treasury_uid_for,
)

Action = Literal["wait", "skip", "set", "failed"]


def _dry_run(value: str) -> bool:
    normalized = value.strip().lower()
    if normalized in ("1", "true", "yes"):
        return True
    if normalized in ("0", "false", "no"):
        return False
    raise ValueError("WEIGHT_DRY_RUN must be 1/true/yes or 0/false/no")


@dc.dataclass(frozen=True, slots=True)
class WeightSetterConfig:
    network: str = FINNEY
    netuid: int = NETUID
    wallet_name: str = "default"
    wallet_hotkey: str = "default"
    wallet_path: str = "~/.bittensor/wallets"

    # Burn mode's destination for the competition's share, and, off mainnet with no
    # WEIGHT_TREASURY_UID, the treasury's. Never eligible for miner payment.
    burn_uid: int = 0
    # Burn the competition's share, ignoring the scores; the treasury is still paid its share.
    # A deliberate, restart-toggled switch for a round that is paused or not yet open.
    burn_mode: bool = False

    # Set this many blocks (or fewer) before each epoch boundary, so the vector lands
    # just before consensus reads it while leaving time for inclusion.
    set_margin: int = 12
    # Idle sleep between ticks; about one block.
    poll_seconds: float = 12.0
    # Compute and record the vector, but do not submit it.
    dry_run: bool = True
    # Off mainnet only: where the treasury share goes (default: the burn uid). On netuid 66 the
    # treasury uid is a code constant and a different value here refuses to start.
    treasury_override: int | None = None
    # The treasury's registered hotkey. When set, the epoch is skipped unless it is in the
    # metagraph -- off mainnet it also locates the treasury uid; on mainnet it must sit at the
    # constant uid, so a reassigned uid 121 is never paid.
    treasury_hotkey: str | None = None
    # Off mainnet only: the competition's fraction of the validator's weight (default 0.20).
    # On netuid 66 it is a code constant and a different value here refuses to start.
    competition_share_override: float | None = None

    def __post_init__(self) -> None:
        if self.burn_uid < 0:
            raise ValueError("burn_uid must be >= 0")
        if self.treasury_override is not None and self.treasury_override < 0:
            raise ValueError("WEIGHT_TREASURY_UID must be >= 0")
        if self.treasury_hotkey is not None and not self.treasury_hotkey.strip():
            raise ValueError("WEIGHT_TREASURY_HOTKEY must not be blank")
        self.treasury_uid  # noqa: B018 - validates the override against the netuid now
        self.competition_share  # noqa: B018 - likewise
        if self.set_margin < 0:
            raise ValueError("set_margin must be >= 0")
        if self.poll_seconds <= 0:
            raise ValueError("poll_seconds must be positive")

    @property
    def treasury_uid(self) -> int:
        return treasury_uid_for(self.netuid, self.treasury_override, burn_uid=self.burn_uid)

    @property
    def competition_share(self) -> float:
        return competition_share_for(self.netuid, self.competition_share_override)

    @classmethod
    def from_env(cls) -> WeightSetterConfig:
        d = cls()
        env = os.environ
        share = env.get("WEIGHT_COMPETITION_SHARE", "").strip()
        return cls(
            network=env.get("BITTENSOR_NETWORK", d.network),
            netuid=int(env.get("NETUID", str(d.netuid))),
            wallet_name=env.get("BITTENSOR_WALLET_NAME", d.wallet_name),
            wallet_hotkey=env.get("BITTENSOR_WALLET_HOTKEY", d.wallet_hotkey),
            wallet_path=env.get("BITTENSOR_WALLET_PATH", d.wallet_path),
            burn_uid=int(env.get("WEIGHT_BURN_UID", str(d.burn_uid))),
            burn_mode=env.get("WEIGHT_BURN_MODE", "").lower() in ("1", "true", "yes"),
            set_margin=int(env.get("WEIGHT_SET_MARGIN", str(d.set_margin))),
            poll_seconds=float(env.get("WEIGHT_POLL_SECONDS", str(d.poll_seconds))),
            dry_run=_dry_run(env.get("WEIGHT_DRY_RUN", "1")),
            treasury_override=_aliased_int(env, "WEIGHT_TREASURY_UID", "WEIGHT_COLLECTOR_UID"),
            treasury_hotkey=_aliased(env, "WEIGHT_TREASURY_HOTKEY", "WEIGHT_COLLECTOR_HOTKEY"),
            competition_share_override=float(share) if share else None,
        )


def _aliased(env: Mapping[str, str], name: str, alias: str) -> str | None:
    """`name`, or the earlier `alias` for it; both set and disagreeing refuses to start."""
    value = env.get(name, "").strip() or None
    legacy = env.get(alias, "").strip() or None
    if value is not None and legacy is not None and value != legacy:
        raise ValueError(f"{name}={value} and {alias}={legacy} disagree; set only {name}")
    return value if value is not None else legacy


def _aliased_int(env: Mapping[str, str], name: str, alias: str) -> int | None:
    value = _aliased(env, name, alias)
    return None if value is None else int(value)


@dc.dataclass(frozen=True, slots=True)
class StepResult:
    action: Action
    reason: str
    epoch_blocks: int | None = None
    rate_off_blocks: int | None = None
    next_try_block: int | None = None
    next_try_blocks: int | None = None
    block: int | None = None
    plan: WeightPlan | None = None
    scoring: scoring.Scoring | None = None
    weight_set_id: int | None = None


def plan_for(
    store: db.Store,
    meta: MetagraphView,
    config: WeightSetterConfig,
    scoring_config: scoring.ScoringConfig,
) -> tuple[WeightPlan, scoring.Scoring | None]:
    """The validator's vector: the treasury share, and the competition's by score.

    Scoring that raises pays the treasury everything this epoch instead of failing the tick:
    a failed tick sets nothing, and an epoch with no weight set cannot be made up later.
    """
    treasury, missing = resolve_treasury(
        meta,
        netuid=config.netuid,
        treasury_uid=config.treasury_uid,
        treasury_hotkey=config.treasury_hotkey,
    )
    if treasury is None:
        return WeightPlan((), (), False, missing, f"treasury_hotkey={config.treasury_hotkey}"), None
    share = config.competition_share
    if config.burn_mode:
        return burn(
            meta, treasury_uid=treasury, burn_uid=config.burn_uid, competition_share=share
        ), None
    try:
        from dataclasses import asdict, replace

        from scoring.admission import POLICY_VERSION

        points, snapshot = store.scoring.api_inputs(
            {
                **asdict(scoring_config),
                "version": POLICY_VERSION,
                "scoring_method": scoring_config.method,
                "max_balanced_time_ratio": scoring_config.speed_floor,
                "max_mean_file_compression_pct": scoring_config.max_ratio_pct,
                "competition_share": share,
                "confidence_level": 0.95,
                "bootstrap_draws": 2000,
            }
        )
        eligible = {
            hotkey
            for hotkey, uid in meta.uid_by_hotkey.items()
            if uid in meta.uids and uid not in (config.burn_uid, treasury)
        }
        result = scoring.score(points, points, scoring_config, eligible_hotkeys=eligible)
        result = replace(result, api_snapshot=snapshot)
    except Exception as exc:  # noqa: BLE001 - any scoring failure pays the treasury
        logger.exception(f"[weights] scoring failed; paying the treasury this epoch: {exc}")
        return split(None, meta, treasury_uid=treasury, reason=f"scoring failed: {exc}"), None
    return split(result.weights, meta, treasury_uid=treasury, competition_share=share), result


def step(
    chain: WeightChain,
    store: db.Store,
    config: WeightSetterConfig,
    scoring_config: scoring.ScoringConfig,
    params: SubnetParams | None = None,
) -> StepResult:
    """Score and persist first, then check whether chain submission is possible."""
    block = chain.current_block()
    meta = chain.metagraph(config.netuid)
    plan, result = plan_for(store, meta, config, scoring_config)
    weight_set_id = record(
        store,
        config,
        block,
        plan,
        result,
        False,
        "chain submission not attempted: eligibility checks pending",
    )

    def finish(action: Action, reason: str, *, accepted: bool = False) -> StepResult:
        store.scoring.weight_set_outcome(
            weight_set_id, accepted=accepted, error=None if accepted else reason
        )
        return StepResult(
            action, reason, block=block, plan=plan, scoring=result, weight_set_id=weight_set_id
        )

    try:
        params = params if params is not None else chain.params(config.netuid)
    except Exception as exc:  # noqa: BLE001 - registration failure must not discard scoring
        reason = f"scores saved; chain submission skipped: {exc}"
        logger.warning(f"[weights] {reason}")
        return finish("skip", reason)

    try:
        poll = chain.poll(config.netuid, params.uid)
    except Exception as exc:  # noqa: BLE001 - preserve evidence through chain outages
        return finish("skip", f"scores saved; chain timing unavailable: {exc}")
    decision = should_set(
        current_block=poll.current_block,
        tempo=params.tempo,
        netuid=config.netuid,
        blocks_since_last_update=poll.blocks_since_last_update,
        weights_rate_limit=params.weights_rate_limit,
        set_margin=config.set_margin,
    )
    if not decision.proceed:
        outcome = finish("wait", "scores saved; waiting for chain submission window")
        return dc.replace(
            outcome,
            epoch_blocks=decision.epoch_blocks,
            rate_off_blocks=decision.rate_off_blocks,
            next_try_block=decision.next_try_block,
            next_try_blocks=decision.next_try_block - poll.current_block,
        )
    if not plan.submittable:
        reason = plan.skip_reason or "unsubmittable vector"
        emit_plan("warning", "weights_skipped", config, meta, block, plan, reason)
        return finish("skip", reason)
    summary = plan.summary + (f" | {result.summary()}" if result else " | burn mode")
    if config.dry_run:
        emit_plan("info", "weights_planned", config, meta, block, plan)
        return finish("skip", f"dry run: not submitted | {summary}")
    try:
        accepted = chain.set_weights(config.netuid, list(plan.uids), list(plan.weights))
    except Exception as exc:  # noqa: BLE001 - an RPC error may have an unknown chain outcome
        return finish("failed", f"chain submission outcome unknown: {exc}")
    if not accepted:
        emit_plan(
            "error", "weights_failed", config, meta, block, plan, "the chain refused the vector"
        )
        return finish("failed", "the chain refused the vector")
    emit_plan("info", "weights_set", config, meta, block, plan)
    return dc.replace(
        finish("set", f"block {block}: {summary}", accepted=True),
        epoch_blocks=decision.epoch_blocks,
    )


def emit_plan(
    severity: Severity,
    event_type: EventType,
    config: WeightSetterConfig,
    meta: MetagraphView,
    block: int,
    plan: WeightPlan,
    error: str | None = None,
) -> None:
    """One Axiom event for a tick's outcome: the vector's nonzero entries and its split."""
    treasury, _ = resolve_treasury(
        meta,
        netuid=config.netuid,
        treasury_uid=config.treasury_uid,
        treasury_hotkey=config.treasury_hotkey,
    )
    paid = {uid: w for uid, w in zip(plan.uids, plan.weights, strict=True) if w > 0}
    get_events().emit(
        severity,
        event_type,
        block=block,
        dry_run=config.dry_run,
        burn_mode=config.burn_mode,
        uids=list(paid),
        weights=list(paid.values()),
        treasury_uid=treasury,
        treasury_share=paid.get(treasury, 0.0) if treasury is not None else None,
        competition_share=config.competition_share,
        burn_uid=config.burn_uid,
        # Off mainnet the treasury may be the burn uid; the two shares are then one number.
        burn_share=paid.get(config.burn_uid, 0.0) if config.burn_uid != treasury else None,
        miners=sum(1 for uid in paid if uid not in (treasury, config.burn_uid)),
        summary=plan.summary,
        error=error,
    )


def record(
    store: db.Store,
    config: WeightSetterConfig,
    block: int,
    plan: WeightPlan,
    result: scoring.Scoring | None,
    accepted: bool,
    error: str | None,
) -> int:
    # The vector and its reasoning, in one transaction. Recorded whatever happened: a
    # refused or skipped epoch is exactly the one somebody will ask about later.
    if result is not None and result.api_snapshot is None:
        raise ValueError("completed scoring requires API evidence")
    return store.scoring.record_weight_set(
        netuid=config.netuid,
        block=block,
        uids=list(plan.uids),
        weights=list(plan.weights),
        summary=plan.summary,
        accepted=accepted,
        dry_run=config.dry_run,
        error=error,
        snapshots=result.snapshots() if result else None,
        api_snapshot=result.api_snapshot if result else None,
    )


def run(
    chain: WeightChain,
    store: db.Store,
    config: WeightSetterConfig,
    scoring_config: scoring.ScoringConfig,
    *,
    sleep: Callable[[float], None] = time.sleep,
) -> None:
    events = get_events()
    events.info("service_started", dry_run=config.dry_run, scoring_method=scoring_config.method)
    logger.info(
        f"[weights] sequential scoring -> weight setting; netuid={config.netuid} "
        f"poll_seconds={config.poll_seconds} dry_run={config.dry_run}"
    )
    ticks = TickLog()
    try:
        while True:
            try:
                # Registration is checked inside step, after scoring has been persisted.
                ticks.report(step(chain, store, config, scoring_config))
            except Exception as exc:  # noqa: BLE001 - a bad tick must not end the worker
                logger.exception(f"[weights] tick failed: {exc}")
                events.error("weights_failed", dry_run=config.dry_run, error=config_error(exc))
            sleep(config.poll_seconds)
    except KeyboardInterrupt:
        logger.info("[weights] interrupted")


def human(seconds: float) -> str:
    if seconds < 90:
        return f"~{seconds:.0f}s"
    if seconds < 5400:
        return f"~{seconds / 60:.0f}m"
    return f"~{seconds / 3600:.1f}h"


class TickLog:
    """Log a wait once, not every twelve seconds.

    The loop spends almost all its time waiting, and a line per tick would bury the ones
    that matter. Only a change in when the next attempt is due is worth saying again.
    """

    def __init__(self) -> None:
        self._wait_key: int | None = None

    def report(self, result: StepResult) -> None:
        if result.action == "wait":
            if result.next_try_block != self._wait_key:
                self._wait_key = result.next_try_block
                seconds = (result.next_try_blocks or 0) * BLOCK_SECONDS
                logger.info(
                    f"[weights] waiting: rate-off ~{result.rate_off_blocks}b, "
                    f"epoch ~{result.epoch_blocks}b, next try block {result.next_try_block} "
                    f"in {human(seconds)}"
                )
            return
        self._wait_key = None
        if result.action == "set":
            logger.info(
                f"[weights] set: {result.reason}; next epoch in "
                f"{human((result.epoch_blocks or 0) * BLOCK_SECONDS)}"
            )
        elif result.action == "skip":
            logger.warning(f"[weights] skipped: {result.reason}")
        else:
            logger.error(f"[weights] failed: {result.reason}")


def main() -> None:
    from chain.finney import BittensorWeightChain

    events = init("competition-weight-setter")
    try:
        config = WeightSetterConfig.from_env()
        scoring_config = scoring.ScoringConfig.from_env()
    except Exception as exc:
        events.error("service_misconfigured", error=config_error(exc))
        raise
    events.bind(netuid=config.netuid, network=config.network)
    chain = BittensorWeightChain(
        network=config.network,
        wallet_name=config.wallet_name,
        wallet_hotkey=config.wallet_hotkey,
        wallet_path=config.wallet_path,
    )
    store = db.connect()
    reason = "crashed"
    try:
        run(chain, store, config, scoring_config)
        reason = "interrupted"  # run() returns only on KeyboardInterrupt
    finally:
        events.info("service_stopped", reason=reason)
        store.close()


if __name__ == "__main__":
    main()
