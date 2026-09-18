"""One registration buys one accepted submission.

The rule lives in `entitlement_claims`' keys, so these tests push on the keys: a
rejection must not spend a slot, an acceptance must, and two acceptances racing for one
remaining slot must end with exactly one claim -- not with two miners paid for one
registration.
"""

from __future__ import annotations

import sys
import threading
from pathlib import Path

import pytest
import sqlalchemy as sa
from conftest import post_submission, register, submission_files
from sqlalchemy.exc import IntegrityError

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

import db as store_pkg  # noqa: E402
from db import SubmissionState, models  # noqa: E402
from db.registrations import NoSlot  # noqa: E402
from service import sig  # noqa: E402

ALICE = sig.load_keypair("//Alice")
BOB = sig.load_keypair("//Bob")


def claims(store) -> list[tuple[int, int]]:
    with store_pkg.session_scope(store.sessions) as session:
        return [
            (int(r.registration_id), int(r.submission_id))
            for r in session.execute(sa.select(models.EntitlementClaim)).scalars()
        ]


# ── The gate at the door ──────────────────────────────────────────────────


def test_an_unregistered_hotkey_cannot_submit(client, tmp_path):
    r = post_submission(client, ALICE, submission_files(tmp_path, "alice"))
    assert r.status_code == 402
    assert "not registered" in r.json()["detail"]["reason"]


def test_one_registration_admits_one_queued_submission(client, store, tmp_path):
    # The slot is not spent at submit time, but a miner may not queue more work than
    # they can pay for: the gate costs the validator the better part of an hour.
    register(store, ALICE.ss58_address)
    first = post_submission(client, ALICE, submission_files(tmp_path, "a1", "BYTES=2300000"))
    assert first.status_code == 200 and first.json()["slots_remaining"] == 1
    second = post_submission(client, ALICE, submission_files(tmp_path, "a2", "BYTES=2200000"))
    assert second.status_code == 402
    assert "register again" in second.json()["detail"]["reason"]


def test_a_second_registration_buys_a_second_submission(client, store, drain, tmp_path):
    register(store, ALICE.ss58_address, block=1000)
    a1 = post_submission(client, ALICE, submission_files(tmp_path, "a1", "BYTES=2300000"))
    assert a1.status_code == 200
    assert drain() == 1
    assert client.get(f"/submissions/{a1.json()['submission']}").json()["state"] == "accepted"
    # Spent. The next one needs another registration.
    assert post_submission(client, ALICE, submission_files(tmp_path, "a2")).status_code == 402
    register(store, ALICE.ss58_address, block=1100)
    a3 = post_submission(client, ALICE, submission_files(tmp_path, "a3", "BYTES=2200000"))
    assert a3.status_code == 200
    assert drain() == 1
    assert len(claims(store)) == 2


# ── What spends a slot, and what does not ─────────────────────────────────


def test_acceptance_spends_a_slot(client, store, drain, tmp_path):
    reg = register(store, ALICE.ss58_address)
    sid = post_submission(client, ALICE, submission_files(tmp_path, "a", "BYTES=2300000")).json()[
        "submission"
    ]
    assert store.registrations.available_slots(ALICE.ss58_address) == 1
    drain()
    assert claims(store) == [(reg, sid)]
    assert store.registrations.available_slots(ALICE.ss58_address) == 0


def test_rejection_is_a_free_retry(client, store, drain, tmp_path):
    register(store, ALICE.ss58_address)
    post_submission(client, ALICE, submission_files(tmp_path, "bad", "REJECT"))
    drain()
    assert claims(store) == []
    assert store.registrations.available_slots(ALICE.ss58_address) == 1
    # And the corrected submission goes through on the same registration.
    good = post_submission(client, ALICE, submission_files(tmp_path, "good", "BYTES=2300000"))
    assert good.status_code == 200
    drain()
    assert len(claims(store)) == 1


def test_a_validator_error_never_charges_the_miner(client, store, drain, tmp_path):
    register(store, ALICE.ss58_address)
    post_submission(client, ALICE, submission_files(tmp_path, "a", "MISCONFIGURED"))
    drain()
    assert claims(store) == []
    assert store.registrations.available_slots(ALICE.ss58_address) == 1


def test_slots_are_per_hotkey_not_shared(client, store, drain, tmp_path):
    register(store, ALICE.ss58_address, uid=1, block=1000)
    register(store, BOB.ss58_address, uid=2, block=1001)
    assert (
        post_submission(client, ALICE, submission_files(tmp_path, "a", "BYTES=2300000")).status_code
        == 200
    )
    assert (
        post_submission(client, BOB, submission_files(tmp_path, "b", "BYTES=2200000")).status_code
        == 200
    )
    drain()
    assert store.registrations.available_slots(ALICE.ss58_address) == 0
    assert store.registrations.available_slots(BOB.ss58_address) == 0
    assert len(claims(store)) == 2


def test_the_oldest_registration_is_spent_first(store):
    # Registrations are spent in the order they happened, so "which one paid for this"
    # is answerable and a re-registration cannot be spent before an older unused one.
    old = register(store, ALICE.ss58_address, block=1000)
    new = register(store, ALICE.ss58_address, block=2000)
    first, _ = store.submissions.add(ALICE.ss58_address, "a" * 64)
    second, _ = store.submissions.add(ALICE.ss58_address, "b" * 64)
    store.submissions.finish(first, SubmissionState.ACCEPTED, bytes=1)
    store.submissions.finish(second, SubmissionState.ACCEPTED, bytes=2)
    assert claims(store) == [(old, first), (new, second)]


# ── The invariant under concurrency ───────────────────────────────────────


def test_accepting_with_no_slot_left_fails_closed(store):
    # Reached only if the door check was bypassed or raced. A submission the gate
    # accepted but nobody can pay for is rejected, never paid for free.
    register(store, ALICE.ss58_address)
    first, _ = store.submissions.add(ALICE.ss58_address, "a" * 64)
    second, _ = store.submissions.add(ALICE.ss58_address, "b" * 64)
    assert store.submissions.finish(first, SubmissionState.ACCEPTED, bytes=1) == "accepted"
    assert store.submissions.finish(second, SubmissionState.ACCEPTED, bytes=2) == "rejected"
    row = store.submissions.get(second)
    assert "no unclaimed registration" in row.report
    assert len(claims(store)) == 1


def test_two_acceptances_racing_for_one_slot_produce_one_claim(store, database_url):
    """The real race, with real threads and real transactions.

    Two gate workers finish the same hotkey's submissions at the same moment with one
    registration between them. FOR UPDATE ... SKIP LOCKED hands the row to one of them;
    the other finds nothing free and fails closed. Exactly one claim, exactly one
    accepted submission -- whichever of the two won.
    """
    register(store, ALICE.ss58_address)
    ids = [store.submissions.add(ALICE.ss58_address, c * 64)[0] for c in ("a", "b")]

    stores = [store_pkg.connect(database_url) for _ in ids]
    barrier = threading.Barrier(len(ids))
    outcomes: dict[int, str] = {}

    def accept(i: int) -> None:
        barrier.wait()
        outcomes[ids[i]] = stores[i].submissions.finish(
            ids[i], SubmissionState.ACCEPTED, bytes=1000 + i
        )

    threads = [threading.Thread(target=accept, args=(i,)) for i in range(len(ids))]
    for t in threads:
        t.start()
    for t in threads:
        t.join(timeout=30)
    for s in stores:
        s.close()

    assert sorted(outcomes.values()) == ["accepted", "rejected"]
    assert len(claims(store)) == 1
    claimed_submission = claims(store)[0][1]
    assert outcomes[claimed_submission] == "accepted"


def test_the_database_itself_refuses_a_double_spend(store):
    # Belt and braces: even a direct insert cannot spend one registration twice.
    reg = register(store, ALICE.ss58_address)
    one, _ = store.submissions.add(ALICE.ss58_address, "a" * 64)
    two, _ = store.submissions.add(ALICE.ss58_address, "b" * 64)
    with store_pkg.session_scope(store.sessions) as session:
        session.add(models.EntitlementClaim(registration_id=reg, submission_id=one))
    with pytest.raises(IntegrityError):
        with store_pkg.session_scope(store.sessions) as session:
            session.add(models.EntitlementClaim(registration_id=reg, submission_id=two))


def test_claim_slot_raises_when_nothing_is_free(store):
    sub, _ = store.submissions.add(ALICE.ss58_address, "a" * 64)
    with pytest.raises(NoSlot):
        with store_pkg.session_scope(store.sessions) as session:
            store.registrations.claim_slot(session, ALICE.ss58_address, sub)
