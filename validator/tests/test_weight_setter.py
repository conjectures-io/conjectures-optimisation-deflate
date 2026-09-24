"""The weight setter: when it sets, what it sets, and what it writes down.

What it sets is the whole validator's vector -- the treasury's share to uid 121 and the
competition's share by score (`scoring.split`) -- so every metagraph here carries uid 121.

A fake `WeightChain` stands in for the network, so the cadence gate, the scoring call,
the audit write and the failure paths are all exercised without a wallet or a node. The
store is real, because the audit trail is half of what this worker is for.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest
import sqlalchemy as sa
from conftest import register

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

import db as store_pkg  # noqa: E402
import scoring  # noqa: E402
from chain.schedule import blocks_until_next_epoch, should_set  # noqa: E402
from chain.types import MetagraphView, PollState, SubnetParams  # noqa: E402
from db import SubmissionState, models  # noqa: E402
from scoring.split import COMPETITION_BPS, TREASURY_UID, split  # noqa: E402
from workers.weight_setter import StepResult, TickLog, WeightSetterConfig, run, step  # noqa: E402

NETUID = 66
RAW = 8_060_939
SHARE = COMPETITION_BPS / 10_000


class FakeChain:
    """A chain that is always ready to take a vector, unless told otherwise."""

    def __init__(
        self, *, uids=(0, 1, 2, TREASURY_UID), hotkeys=None, block=1000, since=1000, accept=True
    ):
        self._uids = tuple(uids)
        self._hotkeys = hotkeys or {}
        self.block = block
        self.since = since
        self.accept = accept
        self.submitted: list[tuple[list[int], list[float]]] = []
        self.param_calls = 0

    def params(self, netuid: int) -> SubnetParams:
        self.param_calls += 1
        return SubnetParams(uid=9, tempo=100, weights_rate_limit=10)

    def poll(self, netuid: int, uid: int) -> PollState:
        return PollState(current_block=self.block, blocks_since_last_update=self.since)

    def metagraph(self, netuid: int) -> MetagraphView:
        return MetagraphView(uids=self._uids, uid_by_hotkey=dict(self._hotkeys))

    def set_weights(self, netuid, uids, weights) -> bool:
        self.submitted.append((list(uids), list(weights)))
        return self.accept


PARAMS = SubnetParams(uid=9, tempo=100, weights_rate_limit=10)
CONFIG = WeightSetterConfig(netuid=NETUID, burn_uid=0, dry_run=False)
SCORING = scoring.ScoringConfig()


def at_epoch_boundary(tempo: int = 100, netuid: int = NETUID, margin: int = 12) -> int:
    # The first block at which should_set would proceed, found rather than assumed: the
    # boundary is offset by the netuid and getting it wrong here would hide a real bug.
    for block in range(1, 10_000):
        if blocks_until_next_epoch(block, tempo, netuid) <= margin:
            return block
    raise AssertionError("no block inside the margin")


def accept(store, hotkey, byte_count, seconds, *, incumbent=2_153_387, digest=None):
    # One accepted submission, through the store, so the scorer reads real rows.
    register(store, hotkey, uid=abs(hash(hotkey)) % 1000, block=abs(hash(hotkey)) % 10_000)
    sub_id, _ = store.submissions.add(hotkey, digest or f"{abs(hash(hotkey)):064x}")
    store.submissions.finish(
        sub_id,
        SubmissionState.ACCEPTED,
        raw_bytes=RAW,
        bytes=byte_count,
        incumbent_bytes=incumbent,
        parse_seconds=seconds,
        compression_seconds=seconds,
        incumbent_seconds=0.52,
        time_ratio=seconds / 0.52,
    )
    from verifier.identity import fingerprint

    with store_pkg.session_scope(store.sessions) as session:
        row = session.get(models.Submission, sub_id)
        assert row is not None
        row.source_sha256 = "a" * 64
        row.proof_sha256 = "b" * 64
        row.verifier_fingerprint = fingerprint()
        row.static_verified_at = store_pkg.now()
        row.lean_verified_at = store_pkg.now()
        row.measured_source_sha256 = row.source_sha256
    from conftest import attach_aggregation

    attach_aggregation(store, sub_id)
    from db.admission import run as admit

    admit(store.scoring, persist=True)
    return sub_id


def weight_sets(store) -> list[models.WeightSet]:
    with store_pkg.session_scope(store.sessions) as session:
        rows = (
            session.execute(sa.select(models.WeightSet).order_by(models.WeightSet.id))
            .scalars()
            .all()
        )
        for r in rows:
            session.expunge(r)
        return list(rows)


def snapshots(store, weight_set_id: int) -> list[models.ScoreSnapshot]:
    with store_pkg.session_scope(store.sessions) as session:
        rows = (
            session.execute(
                sa.select(models.ScoreSnapshot).where(
                    models.ScoreSnapshot.weight_set_id == weight_set_id
                )
            )
            .scalars()
            .all()
        )
        for r in rows:
            session.expunge(r)
        return list(rows)


def require(value: int | None) -> int:
    # A step that recorded a weight set always carries its id; this is that, as an
    # assertion, so the tests below read as what they mean rather than as `or 0`.
    assert value is not None, "the step recorded no weight_sets row"
    return value


# ── The cadence gate ──────────────────────────────────────────────────────


def test_it_waits_while_the_rate_limit_is_still_running(store):
    chain = FakeChain(block=at_epoch_boundary(), since=0)  # just set weights
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "wait" and result.rate_off_blocks == 10
    assert chain.submitted == [] and weight_sets(store) == []


def test_it_waits_while_the_epoch_boundary_is_far_off(store):
    far = at_epoch_boundary() + 50
    chain = FakeChain(block=far, since=1000)
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "wait"
    assert result.next_try_block is not None and result.next_try_block > far


def test_a_wait_names_the_block_it_will_try_again_at(store):
    chain = FakeChain(block=at_epoch_boundary() + 50, since=0)
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    # Both gates apply: it cannot try before the rate limit clears, and then it still
    # waits for the margin before the next boundary.
    assert result.next_try_block is not None
    assert result.next_try_block >= chain.block + 10
    assert blocks_until_next_epoch(result.next_try_block, 100, NETUID) <= CONFIG.set_margin


def test_the_cadence_is_pure_arithmetic():
    decision = should_set(
        current_block=at_epoch_boundary(),
        tempo=100,
        netuid=NETUID,
        blocks_since_last_update=1000,
        weights_rate_limit=10,
        set_margin=12,
    )
    assert decision.proceed and decision.rate_off_blocks == 0
    # A degenerate tempo means every block is a boundary, not a division by zero.
    assert blocks_until_next_epoch(1234, 0, NETUID) == 0


# ── Setting ───────────────────────────────────────────────────────────────


def test_it_scores_the_round_and_sets_a_vector_that_sums_to_one(store):
    accept(store, "alice", 2_100_000, 2.0)
    accept(store, "bob", 2_120_000, 0.30)
    chain = FakeChain(
        hotkeys={"burn": 0, "alice": 1, "bob": 2},
        block=at_epoch_boundary(),
        since=1000,
    )
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "set", result.reason
    uids, weights = chain.submitted[0]
    assert uids == [0, 1, 2, TREASURY_UID]
    assert sum(weights) == pytest.approx(1.0)
    assert weights[1] > 0 and weights[2] > 0
    # Miners are paid their score times the competition's share; whatever the competition
    # does not pay a miner goes to the treasury with its own share, never to the burn uid.
    assert result.scoring is not None
    assert weights[1] == pytest.approx(SHARE * result.scoring.weights["alice"])
    assert weights[2] == pytest.approx(SHARE * result.scoring.weights["bob"])
    assert weights[0] == 0
    assert weights[3] == pytest.approx(1.0 - weights[1] - weights[2])
    assert weights[3] >= 1.0 - SHARE


def test_every_outcome_is_written_down_with_its_reasoning(store):
    accept(store, "alice", 2_100_000, 2.0)
    chain = FakeChain(hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000)
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    rows = weight_sets(store)
    assert len(rows) == 1 and rows[0].accepted is True and rows[0].dry_run is False
    assert rows[0].netuid == NETUID and rows[0].block == chain.block
    assert sum(rows[0].weights) == pytest.approx(1.0)
    snaps = snapshots(store, require(result.weight_set_id))
    assert [s.hotkey for s in snaps] == ["alice"]
    assert snaps[0].on_frontier is True
    assert snaps[0].admission_check_id is not None
    assert snaps[0].combined_weight == pytest.approx(
        snaps[0].pareto_weight + snaps[0].improvement_weight
    )


def test_a_refused_vector_is_recorded_as_refused(store):
    accept(store, "alice", 2_100_000, 2.0)
    chain = FakeChain(
        hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000, accept=False
    )
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "failed"
    rows = weight_sets(store)
    assert rows[0].accepted is False and "refused" in (rows[0].error or "")


def test_a_deregistered_miners_share_goes_to_the_treasury(store):
    # bob earned a share and then left the subnet, and there is no burn uid in the metagraph
    # either. His share has nobody to go to, so the treasury takes it: it is not redistributed
    # to alice, and a missing burn uid no longer matters outside burn mode.
    accept(store, "alice", 2_100_000, 2.0)
    accept(store, "bob", 2_120_000, 0.30)
    chain = FakeChain(
        uids=(1, 2, TREASURY_UID), hotkeys={"alice": 1}, block=at_epoch_boundary(), since=1000
    )
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "set", result.reason
    _, weights = chain.submitted[0]
    assert result.scoring is not None
    alice = SHARE * result.scoring.weights["alice"]
    assert weights == pytest.approx([alice, 0.0, 1.0 - alice])


def test_a_vector_with_no_treasury_uid_is_skipped_and_recorded(store):
    # Without the treasury in the metagraph there is no vector that sums to one without
    # paying someone else the treasury's share; skipping beats that.
    accept(store, "alice", 2_100_000, 2.0)
    chain = FakeChain(uids=(0, 1), hotkeys={"alice": 1}, block=at_epoch_boundary(), since=1000)
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "skip" and f"treasury uid {TREASURY_UID} absent" in result.reason
    assert chain.submitted == []
    assert weight_sets(store)[0].accepted is False


def test_a_scoring_failure_pays_the_treasury_instead_of_failing_the_tick(store, monkeypatch):
    accept(store, "alice", 2_100_000, 2.0)

    def broken(*_args, **_kwargs):
        raise RuntimeError("aggregation context changed")

    monkeypatch.setattr(scoring, "score", broken)
    chain = FakeChain(hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000)
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "set" and result.scoring is None
    uids, weights = chain.submitted[0]
    assert weights[uids.index(TREASURY_UID)] == pytest.approx(1.0)
    assert "scoring failed" in (weight_sets(store)[0].summary or "")


def test_a_dry_run_computes_and_records_but_never_submits(store):
    # The whole path except the last call: what makes the worker exercisable before a
    # validator hotkey exists.
    accept(store, "alice", 2_100_000, 2.0)
    chain = FakeChain(hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000)
    config = WeightSetterConfig(netuid=NETUID, dry_run=True)
    result = step(chain, store, config, SCORING, PARAMS)
    assert result.action == "skip" and "dry run" in result.reason
    assert chain.submitted == []
    row = weight_sets(store)[0]
    assert row.dry_run is True and row.accepted is False
    assert sum(row.weights) == pytest.approx(1.0)
    assert snapshots(store, require(result.weight_set_id))


def test_burn_mode_pays_nobody_and_scores_nothing(store):
    accept(store, "alice", 2_100_000, 2.0)
    chain = FakeChain(hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000)
    config = WeightSetterConfig(netuid=NETUID, burn_mode=True, dry_run=False)
    result = step(chain, store, config, SCORING, PARAMS)
    assert result.action == "set"
    uids, weights = chain.submitted[0]
    # Burn mode burns the competition's share; the treasury's is not the competition's to burn.
    assert weights[uids.index(0)] == pytest.approx(SHARE)
    assert weights[uids.index(TREASURY_UID)] == pytest.approx(1.0 - SHARE)
    assert result.scoring is None
    assert snapshots(store, require(result.weight_set_id)) == []


def test_an_empty_round_pays_the_treasury_rather_than_skipping(store):
    # Nobody has been accepted yet. A validator must still set weights -- a zero vector
    # or a silent epoch reads as "no opinion", not as "pay nobody". The competition's
    # unpaid share goes to the treasury.
    chain = FakeChain(hotkeys={"burn": 0}, block=at_epoch_boundary(), since=1000)
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "set"
    uids, weights = chain.submitted[0]
    assert weights[uids.index(0)] == 0
    assert weights[uids.index(TREASURY_UID)] == pytest.approx(1.0)


# ── The loop around it ────────────────────────────────────────────────────


def test_the_loop_rereads_the_subnet_parameters_after_a_set(store):
    # Tempo and the rate limit can change between epochs; a worker holding a stale tempo
    # would set weights at the wrong moment for the rest of its life.
    accept(store, "alice", 2_100_000, 2.0)
    chain = FakeChain(hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000)
    ticks = {"n": 0}

    def sleep(_seconds):
        ticks["n"] += 1
        if ticks["n"] >= 2:
            raise KeyboardInterrupt

    run(chain, store, CONFIG, SCORING, sleep=sleep)
    assert chain.param_calls >= 2, "params were not re-read after setting"


def test_a_tick_that_raises_does_not_end_the_worker(store):
    class Exploding(FakeChain):
        def poll(self, netuid, uid):
            raise RuntimeError("node hiccup")

    chain = Exploding(hotkeys={"burn": 0})
    ticks = {"n": 0}

    def sleep(_seconds):
        ticks["n"] += 1
        if ticks["n"] >= 3:
            raise KeyboardInterrupt

    run(chain, store, CONFIG, SCORING, sleep=sleep)
    assert ticks["n"] == 3, "the loop kept going across the failures"


def test_a_wait_is_logged_once_not_every_twelve_seconds():
    # The loop spends almost all its time waiting; a line per tick would bury the ones
    # that matter.
    log = TickLog()
    lines = []
    from loguru import logger

    sink = logger.add(lambda m: lines.append(m), level="INFO")
    try:
        for _ in range(5):
            log.report(StepResult("wait", "", next_try_block=500, next_try_blocks=40))
        log.report(StepResult("wait", "", next_try_block=900, next_try_blocks=70))
    finally:
        logger.remove(sink)
    assert len(lines) == 2


def test_weight_setting_defaults_to_dry_run(monkeypatch):
    monkeypatch.delenv("WEIGHT_DRY_RUN", raising=False)
    assert WeightSetterConfig().dry_run
    assert WeightSetterConfig.from_env().dry_run
    monkeypatch.setenv("WEIGHT_DRY_RUN", "0")
    assert not WeightSetterConfig.from_env().dry_run
    monkeypatch.setenv("WEIGHT_DRY_RUN", "flase")
    with pytest.raises(ValueError, match="WEIGHT_DRY_RUN"):
        WeightSetterConfig.from_env()


# ── The treasury split ────────────────────────────────────────────────────


def test_the_treasury_uid_on_mainnet_is_a_code_constant(monkeypatch):
    assert WeightSetterConfig(netuid=NETUID).treasury_uid == TREASURY_UID
    assert WeightSetterConfig(netuid=NETUID, treasury_override=TREASURY_UID).treasury_uid == 121
    with pytest.raises(ValueError, match="code constant"):
        WeightSetterConfig(netuid=NETUID, treasury_override=7)
    monkeypatch.setenv("WEIGHT_TREASURY_UID", "7")
    with pytest.raises(ValueError, match="code constant"):
        WeightSetterConfig.from_env()


def test_off_mainnet_the_treasury_share_goes_where_it_is_told_or_burns():
    assert WeightSetterConfig(netuid=2, burn_uid=0).treasury_uid == 0
    assert WeightSetterConfig(netuid=2, burn_uid=0, treasury_override=3).treasury_uid == 3


def test_the_split_scales_the_competition_and_pays_the_treasury_the_rest():
    meta = MetagraphView(uids=(0, 5, TREASURY_UID), uid_by_hotkey={"x": 5})
    plan = split({"x": 0.5}, meta, treasury_uid=TREASURY_UID, competition_share=0.25)
    assert plan.submittable
    # x's half of the competition's quarter; the unclaimed half goes to the treasury.
    assert dict(zip(plan.uids, plan.weights, strict=True)) == pytest.approx(
        {0: 0.0, 5: 0.125, TREASURY_UID: 0.875}
    )
    everything = split({"x": 1.0}, meta, treasury_uid=TREASURY_UID, competition_share=1.0)
    assert dict(zip(everything.uids, everything.weights, strict=True))[TREASURY_UID] == 0.0
    failed = split(None, meta, treasury_uid=TREASURY_UID, reason="scoring failed: boom")
    assert failed.weights == (0.0, 0.0, 1.0) and "scoring failed" in failed.summary


def test_the_competition_share_on_mainnet_is_a_code_constant(monkeypatch):
    assert WeightSetterConfig(netuid=NETUID).competition_share == SHARE
    assert (
        WeightSetterConfig(netuid=NETUID, competition_share_override=0.2).competition_share == SHARE
    )
    with pytest.raises(ValueError, match="code constant"):
        WeightSetterConfig(netuid=NETUID, competition_share_override=0.3)
    monkeypatch.setenv("WEIGHT_COMPETITION_SHARE", "1.0")
    with pytest.raises(ValueError, match="code constant"):
        WeightSetterConfig.from_env()


def test_burn_mode_without_a_burn_uid_pays_the_treasury(store):
    chain = FakeChain(uids=(1, TREASURY_UID), block=at_epoch_boundary(), since=1000)
    config = WeightSetterConfig(netuid=NETUID, burn_mode=True, dry_run=False)
    result = step(chain, store, config, SCORING, PARAMS)
    assert result.action == "set"
    assert chain.submitted[0][1] == [0.0, 1.0]
    assert "burn uid 0 absent" in (weight_sets(store)[0].summary or "")


def test_a_pinned_treasury_hotkey_must_sit_at_the_treasury_uid_on_mainnet(store):
    accept(store, "alice", 2_100_000, 2.0)
    config = WeightSetterConfig(netuid=NETUID, treasury_hotkey="treasury", dry_run=False)
    moved = FakeChain(hotkeys={"alice": 1, "treasury": 2}, block=at_epoch_boundary())
    result = step(moved, store, config, SCORING, PARAMS)
    assert result.action == "skip" and "not the treasury uid" in result.reason
    assert moved.submitted == []
    home = FakeChain(hotkeys={"alice": 1, "treasury": TREASURY_UID}, block=at_epoch_boundary())
    assert step(home, store, config, SCORING, PARAMS).action == "set"


def test_default_budget_is_recorded_and_baseline_allocation_goes_to_collector(store):
    baseline_id = accept(store, "baseline-owner", 2_000_000, 2.0)
    accept(store, "miner", 2_050_000, 0.3)
    with store_pkg.session_scope(store.sessions) as session:
        baseline = session.get(models.Submission, baseline_id)
        assert baseline is not None
        baseline.hotkey = None
        baseline.baseline_key = "local:routing-baseline"
        baseline.baseline_active = True
    from db.admission import run as admit

    admit(store.scoring, persist=True, replay=True)
    chain = FakeChain(
        uids=(0, 1, 121),
        hotkeys={"miner": 1, "collector": 121},
        block=at_epoch_boundary(),
    )
    result = step(chain, store, WeightSetterConfig(dry_run=False), SCORING, PARAMS)
    assert result.action == "set", result.reason
    assert result.scoring is not None
    assert any(s.baseline_key for s in result.scoring.scores)
    _, weights = chain.submitted[0]
    assert weights[0] == 0
    assert weights[1] == pytest.approx(0.2 * result.scoring.weights["miner"])
    assert weights[2] == pytest.approx(1 - weights[1])
    assert weights[2] >= 0.8
    assert "competition_share=0.200000" in (weight_sets(store)[0].summary or "")


def test_api_snapshot_captures_public_membership_without_changing_scores(store):
    from dataclasses import replace

    sid = accept(store, "api-miner", 2_000_000, 0.4)
    queued, _ = store.submissions.add("queued-miner", "c" * 64)
    with store.sessions.begin() as session:
        diagnostic = models.Submission(digest="d" * 64)
        session.add(diagnostic)
        session.flush()
        test_id = diagnostic.id
    chain = FakeChain(block=at_epoch_boundary(), hotkeys={"api-miner": 1})
    points = store.scoring.scoring_inputs()
    expected = scoring.score(points, points, SCORING, eligible_hotkeys={"api-miner"})
    result = step(chain, store, replace(CONFIG, dry_run=True), SCORING, PARAMS)
    assert chain.submitted == []
    assert result.scoring is not None
    assert result.scoring.scores == expected.scores
    row = weight_sets(store)[0]
    payload = row.api_snapshot
    assert payload is not None
    assert payload["schema_version"] == 1
    import json
    saved = json.dumps(payload, sort_keys=True)
    # Diagnostic submissions never enter public snapshot membership.
    items = payload["items"]
    assert isinstance(items, list)
    assert {item["submission"]["id"] for item in items} == {sid, queued}
    assert test_id not in {item["submission"]["id"] for item in items}
    policy = payload["policy"]
    assert isinstance(policy, dict)
    assert policy["competition_share"] == SHARE
    assert policy["max_balanced_time_ratio"] == 10
    assert policy["max_mean_file_compression_pct"] == 40
    measured = next(item for item in items if item["submission"]["id"] == sid)
    assert measured["aggregation"]["statistics"]["intervals"] is not None
    assert measured["admission"]["outcome"] == "not_required"
    with store.sessions.begin() as session:
        sub = session.get(models.Submission, sid)
        sub.state = "error"
    assert json.dumps(weight_sets(store)[0].api_snapshot, sort_keys=True) == saved


def test_treasury_only_attempt_has_no_completed_api_snapshot(store):
    from dataclasses import replace

    chain = FakeChain(block=at_epoch_boundary())
    step(chain, store, replace(CONFIG, burn_mode=True, dry_run=True), SCORING, PARAMS)
    assert weight_sets(store)[0].api_snapshot is None
    assert chain.submitted == []
