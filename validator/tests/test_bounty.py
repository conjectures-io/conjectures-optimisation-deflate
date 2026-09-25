"""The submission bounty: what a pair has received, and when it stops being paid.

The rule itself (`scoring.bounty`) is pure and tested without a database; the ledger and
the weight setter's use of it run against the real store, with a fake chain supplying
each epoch's emission.
"""

from __future__ import annotations

import dataclasses as dc
import sys
from pathlib import Path
from typing import cast

import pytest
import sqlalchemy as sa
from test_weight_setter import (
    CONFIG,
    PARAMS,
    SCORING,
    FakeChain,
    accept,
    at_epoch_boundary,
    snapshots,
    weight_sets,
)

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import db as store_pkg  # noqa: E402
from chain.types import EpochEmission, NeuronEmission  # noqa: E402
from db.bounty_models import BountyAccrual  # noqa: E402
from scoring.bounty import (  # noqa: E402
    BOUNTY_CAPPED,
    RAO_PER_ALPHA,
    Ledger,
    Outlook,
    PaidSet,
    apply,
    attribute,
    bounty_alpha_from_env,
)
from scoring.combine import HotkeyScore, Scoring  # noqa: E402
from scoring.frontier import FrontierScore  # noqa: E402
from scoring.split import TREASURY_UID  # noqa: E402
from workers.weight_setter import step  # noqa: E402

A = RAO_PER_ALPHA


def neuron(uid, hotkey, alpha, incentive=0.1):
    return NeuronEmission(uid, hotkey, "cold-" + hotkey, int(alpha * A), incentive)


def epoch(epoch_block, *neurons, tempo=100, reveal=0):
    return EpochEmission(epoch_block, epoch_block + 1, tempo, reveal, tuple(neurons))


def row(sid: int, payable: float, *, hotkey: str | None = "alice", baseline: str | None = None):
    return HotkeyScore(
        hotkey, sid, 1.0, 35.0, True, payable, 0.0, baseline_key=baseline, payable_weight=payable
    )


def scored(*rows):
    return Scoring(tuple(rows), FrontierScore({}, {}, (), None), ())  # pyright: ignore[reportArgumentType]


# ── The rule ──────────────────────────────────────────────────────────────


def test_the_bounty_defaults_to_half_a_days_alpha_and_refuses_nonsense():
    assert bounty_alpha_from_env({}) == 3600.0
    assert bounty_alpha_from_env({"ALPHA_TOTAL_SUBMISSION_BOUNTY": "50"}) == 50.0
    for bad in ("0", "-1", "nan", "lots"):
        with pytest.raises(ValueError):
            bounty_alpha_from_env({"ALPHA_TOTAL_SUBMISSION_BOUNTY": bad})


def test_a_pair_below_the_bounty_keeps_its_weight_and_shows_its_total():
    result, caps = apply(
        scored(row(1, 0.5)),
        {1: Ledger(10 * A, 2 * A)},
        bounty_alpha=100,
        outlook=Outlook(miner_pool_rao=100 * A, horizon_epochs=2),
        competition_share=0.2,
    )
    # Projected: 2 epochs x max(2 observed, 0.5 x 0.2 x 100 = 10 expected) = 20; 10 + 20 <= 100.
    (s,) = result.scores
    assert caps == [] and s.payable_weight == 0.5 and s.bounty_rao == 10 * A
    assert s.bounty_capped is False and s.burn_reason is None


def test_a_pair_that_would_pass_the_bounty_is_zeroed_before_it_does():
    result, caps = apply(
        scored(row(1, 0.5)),
        {1: Ledger(85 * A, 2 * A)},
        bounty_alpha=100,
        outlook=Outlook(miner_pool_rao=100 * A, horizon_epochs=2),
        competition_share=0.2,
    )
    (s,) = result.scores
    assert s.payable_weight == 0 and s.burn_reason == BOUNTY_CAPPED and s.bounty_capped
    assert result.weights == {}  # so the treasury takes the share
    assert [(c.submission_id, c.earned_rao, c.projected_rao) for c in caps] == [(1, 85 * A, 20 * A)]


def test_a_capped_pair_stays_capped_after_its_rate_falls_to_zero():
    result, caps = apply(
        scored(row(1, 0.5)),
        {1: Ledger(90 * A, 0, capped=True)},
        bounty_alpha=3600,
        outlook=Outlook(),
        competition_share=0.2,
    )
    assert caps == [] and result.scores[0].payable_weight == 0 and result.scores[0].bounty_capped


def test_the_bounty_is_per_submission_and_never_touches_a_baseline():
    result, _ = apply(
        scored(row(1, 0.3), row(2, 0.3), row(3, 0.0, hotkey=None, baseline="optimal")),
        {1: Ledger(int(99.5 * A), A), 2: Ledger(0, 0)},
        bounty_alpha=100,
        outlook=Outlook(),
        competition_share=0.2,
    )
    first, second, baseline = result.scores
    assert first.payable_weight == 0 and second.payable_weight == 0.3
    assert baseline.bounty_rao is None and baseline.bounty_capped is False


def test_emission_is_credited_to_the_submissions_the_vector_in_effect_paid():
    in_effect = PaidSet(1, 100, {"alice": [(10, 0.3)], "bob": [(20, 0.1), (21, 0.3)]})
    newer = PaidSet(2, 200, {"alice": [(11, 0.3)], "carol": [(30, 0.2)]})
    e = epoch(
        205,
        neuron(1, "alice", 30),
        neuron(2, "bob", 10.000000001),
        neuron(3, "carol", 5),
        neuron(4, "dave", 7),  # paid by nobody here: not this competition's to count
        neuron(5, "erin", 0),
        reveal=1,
    )
    credits = attribute(e, [newer, in_effect])
    by_sid = {c.submission_id: c.alpha_rao for c in credits}
    # With a one-epoch reveal the vector read at 205 was set at or before block 104.
    assert by_sid[10] == 30 * A and 11 not in by_sid
    # bob's emission splits 1:3 by weight, and no rao is lost to rounding.
    assert by_sid[20] + by_sid[21] == int(10.000000001 * A)
    assert by_sid[20] == pytest.approx(2.5 * A, abs=1)
    # carol was paid only by the newer vector; it still covers her.
    assert by_sid[30] == 5 * A
    assert {c.coldkey for c in credits if c.hotkey == "alice"} == {"cold-alice"}
    assert all(c.hotkey != "dave" for c in credits)


def test_a_vector_set_after_the_epoch_is_never_credited_for_it():
    later = PaidSet(3, 300, {"alice": [(12, 0.3)]})
    assert attribute(epoch(250, neuron(1, "alice", 30)), [later]) == []


# ── The ledger and the weight setter ──────────────────────────────────────


def accruals(store) -> list[BountyAccrual]:
    with store_pkg.session_scope(store.sessions) as session:
        rows = list(session.scalars(sa.select(BountyAccrual)))
        for r in rows:
            session.expunge(r)
        return rows


def published(store, result) -> list[tuple[object, ...]]:
    # What the read API is given: the pass's api_snapshot, as the weight setter saved it.
    rows = [r for r in weight_sets(store) if r.id == result.weight_set_id]
    payload = rows[0].api_snapshot or {}
    section = cast(dict[str, list[dict[str, object]]], payload["bounty"])
    return [
        (i["submission_id"], i["earned_rao"], i["earned_alpha"], i["capped"])
        for i in section["submissions"]
    ]


def test_an_epoch_is_credited_once_and_the_cap_redirects_to_the_treasury(store):
    sid = accept(store, "alice", 2_100_000, 2.0)
    chain = FakeChain(hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000)
    first = step(chain, store, CONFIG, SCORING, PARAMS)
    assert first.action == "set" and first.scoring is not None
    paid = first.scoring.weights["alice"]
    assert paid > 0

    # The epoch after that vector: alice's uid received 40 alpha, the treasury the rest.
    chain.epoch = epoch(
        chain.block + 1,
        neuron(1, "alice", 40, 0.2),
        neuron(TREASURY_UID, "treasury", 160, 0.8),
    )
    second = step(chain, store, CONFIG, SCORING, PARAMS)
    third = step(chain, store, CONFIG, SCORING, PARAMS)  # the same epoch again
    assert [(a.submission_id, a.alpha_rao, a.coldkey) for a in accruals(store)] == [
        (sid, 40 * A, "cold-alice")
    ]
    assert published(store, second) == [(sid, 40 * A, 40.0, False)]
    assert third.scoring is not None and third.scoring.weights["alice"] == paid

    # 40 received plus one more epoch at 40 passes a 70 alpha bounty: zero, now.
    capped = step(chain, store, dc.replace(CONFIG, bounty_alpha=70), SCORING, PARAMS)
    assert capped.action == "set" and capped.scoring is not None
    assert capped.scoring.weights == {}
    uids, weights = chain.submitted[-1]
    assert weights[uids.index(1)] == 0
    assert weights[uids.index(TREASURY_UID)] == pytest.approx(1.0)
    (snap,) = snapshots(store, capped.weight_set_id or 0)
    assert snap.burn_reason == BOUNTY_CAPPED and snap.payable_weight == 0
    assert published(store, capped) == [(sid, 40 * A, 40.0, True)]

    # Sticky: restoring the default bounty does not reopen it.
    after = step(chain, store, CONFIG, SCORING, PARAMS)
    assert after.scoring is not None and after.scoring.weights == {}
    assert after.scoring.api_snapshot is not None
    policy = after.scoring.api_snapshot["policy"]
    assert isinstance(policy, dict) and policy["alpha_total_submission_bounty"] == 3600.0


def test_a_chain_read_failure_does_not_stop_scoring(store):
    accept(store, "alice", 2_100_000, 2.0)

    class Broken(FakeChain):
        def last_epoch_block(self, netuid: int) -> int:
            raise ConnectionError("node gone")

    chain = Broken(hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000)
    result = step(chain, store, CONFIG, SCORING, PARAMS)
    assert result.action == "set" and result.scoring is not None
    assert result.scoring.weights["alice"] > 0


def test_the_read_endpoints_show_what_a_submission_has_received(store, settings):
    from fastapi.testclient import TestClient

    from service.api import create_app

    sid = accept(store, "alice", 2_100_000, 2.0)
    chain = FakeChain(hotkeys={"burn": 0, "alice": 1}, block=at_epoch_boundary(), since=1000)
    step(chain, store, CONFIG, SCORING, PARAMS)
    chain.epoch = epoch(chain.block + 1, neuron(1, "alice", 12.5, 0.2))
    step(chain, store, CONFIG, SCORING, PARAMS)

    with TestClient(app=create_app(settings, store)) as client:
        view = client.get(f"/submissions/{sid}").json()
        board = client.get("/leaderboard").json()
    assert view["bounty_alpha"] == 12.5
    assert board["bounty_limit_alpha"] == 3600.0
    assert [r["bounty_alpha"] for r in board["ranking"] if r["submission"] == sid] == [12.5]
