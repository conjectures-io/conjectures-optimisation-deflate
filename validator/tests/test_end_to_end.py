"""Registration to weight vector, with only the chain and the gate faked.

Everything between is real: the API refuses an unregistered miner, the watcher's rows are
what admit them, the gate worker's outcome is what spends their registration, the scorer
reads what the gate wrote, and the weight setter pays it out and writes down why.
"""

from __future__ import annotations

import datetime as dt
import sys
from pathlib import Path

import pytest
import sqlalchemy as sa
from conftest import post_submission, submission_files

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

from test_weight_setter import FakeChain, at_epoch_boundary  # noqa: E402

import db as store_pkg  # noqa: E402
import scoring  # noqa: E402
from chain import watcher  # noqa: E402
from chain.types import NETUID, ChainHead, MetagraphSnapshot, NeuronInfo  # noqa: E402
from db import models  # noqa: E402
from db.adapters import DatabaseSnapshotSink  # noqa: E402
from service import sig  # noqa: E402
from workers.weight_setter import WeightSetterConfig, step  # noqa: E402

T0 = dt.datetime(2026, 10, 1, 12, 0, tzinfo=dt.timezone.utc)

ALICE = sig.load_keypair("//Alice")
BOB = sig.load_keypair("//Bob")


class SubnetAt:
    """A fake subnet the test registers hotkeys on, one block at a time."""

    def __init__(self) -> None:
        self.block = 1000
        self.neurons: list[NeuronInfo] = []

    def register(self, uid: int, hotkey: str) -> None:
        self.block += 100
        self.neurons = [n for n in self.neurons if n.uid != uid]
        self.neurons.append(
            NeuronInfo(
                uid=uid,
                hotkey=hotkey,
                coldkey=f"cold{uid}",
                stake=1.0,
                block_at_registration=self.block,
            )
        )

    def head(self) -> ChainHead:
        return ChainHead(block=self.block, timestamp=T0 + dt.timedelta(seconds=12 * self.block))

    def metagraph(self, netuid: int, block: int | None = None) -> MetagraphSnapshot:
        at = block if block is not None else self.block
        return MetagraphSnapshot(
            netuid=netuid,
            block=at,
            timestamp=T0 + dt.timedelta(seconds=12 * at),
            neurons=tuple(self.neurons),
        )


def block_time(block: int) -> dt.datetime:
    return T0 + dt.timedelta(seconds=12 * block)


def test_registration_to_weight_vector(client, store, settings, drain, tmp_path, clock):
    subnet = SubnetAt()
    sink = DatabaseSnapshotSink(store.registrations, block_time)

    # 1. Nobody is registered, so nobody can submit.
    refused = post_submission(client, ALICE, submission_files(tmp_path, "a0", "BYTES=2100000"))
    assert refused.status_code == 402 and "not registered" in refused.json()["detail"]["reason"]

    # 2. The watcher records two registrations, which is what admits them.
    subnet.register(1, ALICE.ss58_address)
    subnet.register(2, BOB.ss58_address)
    last = watcher.step(subnet, sink, NETUID, None)
    assert store.registrations.available_slots(ALICE.ss58_address) == 1
    assert store.registrations.available_slots(BOB.ss58_address) == 1

    # 3. Both submit. Alice compresses harder and slower; Bob is fast and a little worse,
    #    so both sit on the frontier and neither dominates the other.
    alice = post_submission(
        client, ALICE, submission_files(tmp_path, "alice", "BYTES=2100000 SECONDS=2.000")
    )
    clock["tick"](60)
    bob = post_submission(
        client, BOB, submission_files(tmp_path, "bob", "BYTES=2140000 SECONDS=0.300")
    )
    assert (alice.status_code, bob.status_code) == (200, 200)
    assert drain() == 2

    # 4. Both accepted, and each spent exactly one registration.
    board = client.get("/leaderboard").json()["ranking"]
    assert [r["hotkey"] for r in board] == [ALICE.ss58_address, BOB.ss58_address]
    with store_pkg.session_scope(store.sessions) as session:
        claims = session.execute(sa.select(models.EntitlementClaim)).scalars().all()
    assert len(claims) == 2
    assert store.registrations.available_slots(ALICE.ss58_address) == 0
    assert store.registrations.available_slots(BOB.ss58_address) == 0

    # 5. And so neither may submit again without registering again.
    again = post_submission(client, ALICE, submission_files(tmp_path, "a2", "BYTES=2000000"))
    assert again.status_code == 402

    # 6. Alice registers a second time; the watcher sees it and the slot is hers again.
    subnet.register(3, ALICE.ss58_address)
    watcher.step(subnet, sink, NETUID, last)
    assert store.registrations.available_slots(ALICE.ss58_address) == 1
    better = post_submission(
        client, ALICE, submission_files(tmp_path, "a3", "BYTES=2000000 SECONDS=2.100")
    )
    assert better.status_code == 200
    assert drain() == 1

    # 7. The scorer reads what the gate wrote: one point per hotkey, Alice's best.
    best = {s.hotkey: s for s in store.scoring.best_per_hotkey()}
    assert best[ALICE.ss58_address].bytes == 2_000_000
    assert best[BOB.ss58_address].bytes == 2_140_000

    # 8. The weight setter pays it out.
    chain = FakeChain(
        uids=(0, 1, 2),
        hotkeys={"burn": 0, ALICE.ss58_address: 1, BOB.ss58_address: 2},
        block=at_epoch_boundary(),
        since=1000,
    )
    result = step(
        chain,
        store,
        WeightSetterConfig(netuid=NETUID, burn_uid=0),
        scoring.ScoringConfig(),
        chain.params(NETUID),
    )
    assert result.action == "set", result.reason
    uids, weights = chain.submitted[0]
    assert uids == [0, 1, 2]
    assert sum(weights) == pytest.approx(1.0)
    # Both are paid, and by different components -- which is the whole reason there are
    # two. Alice holds both improvements (she beat the incumbent, then beat herself), so
    # the entire improvement share is hers. Bob is the knee of the frontier: nearly as
    # small as Alice at a seventh of the time, so the Pareto share is nearly all his.
    assert weights[1] > 0 and weights[2] > 0
    assert weights[1] == pytest.approx(0.40, abs=0.02)
    assert weights[2] == pytest.approx(0.60, abs=0.02)

    # 9. And the vector is on the record with its per-hotkey reasoning.
    with store_pkg.session_scope(store.sessions) as session:
        vector = session.execute(sa.select(models.WeightSet)).scalars().one()
        snaps = (
            session.execute(
                sa.select(models.ScoreSnapshot).where(
                    models.ScoreSnapshot.weight_set_id == vector.id
                )
            )
            .scalars()
            .all()
        )
        by_hotkey = {s.hotkey: s for s in snaps}
        assert vector.accepted is True and sum(vector.weights) == pytest.approx(1.0)
        assert set(by_hotkey) == {ALICE.ss58_address, BOB.ss58_address}
        assert by_hotkey[ALICE.ss58_address].on_frontier is True
        assert by_hotkey[BOB.ss58_address].on_frontier is True
        assert by_hotkey[BOB.ss58_address].improvement_weight == pytest.approx(0.0)
        assert by_hotkey[ALICE.ss58_address].improvement_weight == pytest.approx(0.4)
        assert sum(s.combined_weight for s in snaps) == pytest.approx(1.0)


def test_a_rejected_submission_costs_nothing_and_scores_nothing(client, store, drain, tmp_path):
    subnet = SubnetAt()
    sink = DatabaseSnapshotSink(store.registrations, block_time)
    subnet.register(1, ALICE.ss58_address)
    watcher.step(subnet, sink, NETUID, None)

    bad = post_submission(client, ALICE, submission_files(tmp_path, "bad", "REJECT"))
    assert bad.status_code == 200
    drain()
    assert store.registrations.available_slots(ALICE.ss58_address) == 1
    assert store.scoring.best_per_hotkey() == []

    good = post_submission(
        client, ALICE, submission_files(tmp_path, "good", "BYTES=2100000 SECONDS=1.000")
    )
    assert good.status_code == 200
    drain()
    assert store.registrations.available_slots(ALICE.ss58_address) == 0
    assert len(store.scoring.best_per_hotkey()) == 1
