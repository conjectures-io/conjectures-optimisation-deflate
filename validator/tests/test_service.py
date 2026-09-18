"""The submission service, end to end: submit, verify, rank.

Runs against a scratch Postgres database and a stub verifier, so it needs no toolchain.
The last test pushes the reference submissions through the real gate and skips without one.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest
from conftest import post_submission, register, submission_files

VALIDATOR = Path(__file__).resolve().parent.parent
REPO = VALIDATOR.parent
sys.path.insert(0, str(VALIDATOR))

from service import sig, worker  # noqa: E402

TEMPLATE = REPO / "miner/template"

ALICE = sig.load_keypair("//Alice")
BOB = sig.load_keypair("//Bob")
CHARLIE = sig.load_keypair("//Charlie")


def enrol(store, *keypairs, slots: int = 4):
    # Give each hotkey `slots` registrations: these tests are about the gate and the
    # board, not about running out of entitlement. test_entitlements.py covers that.
    for i, kp in enumerate(keypairs):
        for n in range(slots):
            register(store, kp.ss58_address, uid=i, block=1000 + i * 100 + n)


# ── The happy path ────────────────────────────────────────────────────────


def test_submit_verify_rank(client, store, drain, tmp_path):
    # Two miners; Bob compresses better; both accepted; Bob first.
    enrol(store, ALICE, BOB)
    ra = post_submission(client, ALICE, submission_files(tmp_path, "alice", "BYTES=2300000"))
    rb = post_submission(client, BOB, submission_files(tmp_path, "bob", "BYTES=2200000"))
    assert ra.status_code == 200 and rb.status_code == 200, ra.text + rb.text
    sa, sb = ra.json()["submission"], rb.json()["submission"]
    assert client.get(f"/submissions/{sa}").json()["state"] == "queued"
    assert client.get("/health").json()["queued"] == 2
    assert drain() == 2

    a = client.get(f"/submissions/{sa}").json()
    assert client.get(f"/submissions/{sb}").json()["state"] == "accepted"
    assert a["state"] == "accepted" and a["bytes"] == 2300000 and a["time_ratio"] == 4.0
    assert a["incumbent_bytes"] == 2153387 and "TOTAL" in a["report"]

    board = client.get("/leaderboard").json()
    assert board["incumbent_bytes"] == 2153387
    assert [x["submission"] for x in board["ranking"]] == [sb, sa]
    assert [x["rank"] for x in board["ranking"]] == [1, 2]
    assert board["ranking"][0]["vs_incumbent"] == round(2200000 / 2153387, 5)


def test_the_score_keeps_every_number_the_frontier_needs(client, store, drain, tmp_path):
    # raw bytes and absolute seconds, not just the ratios: the Pareto frontier is over
    # (seconds, bytes-as-a-percentage-of-raw) and cannot be built from the ratios alone.
    enrol(store, ALICE)
    rid = post_submission(
        client, ALICE, submission_files(tmp_path, "alice", "BYTES=2300000 SECONDS=0.400")
    ).json()["submission"]
    drain()
    row = store.submissions.get(rid)
    assert (row.raw_bytes, row.bytes, row.incumbent_bytes) == (8060939, 2300000, 2153387)
    assert (row.incumbent_seconds, row.parse_seconds, row.time_ratio) == (0.025, 0.400, 16.0)


def test_leaderboard_keeps_each_hotkeys_best_and_ties_go_to_the_earlier(
    client, store, drain, tmp_path, clock
):
    enrol(store, ALICE, BOB)
    post_submission(client, ALICE, submission_files(tmp_path, "a1", "BYTES=2300000"))
    clock["tick"](60)
    post_submission(client, BOB, submission_files(tmp_path, "b1", "BYTES=2200000"))
    clock["tick"](60)
    # Alice ties Bob, later: Bob keeps the rank.
    post_submission(client, ALICE, submission_files(tmp_path, "a2", "BYTES=2200000"))
    drain()
    ranking = client.get("/leaderboard").json()["ranking"]
    assert [x["hotkey"] for x in ranking] == [BOB.ss58_address, ALICE.ss58_address]
    assert [x["bytes"] for x in ranking] == [2200000, 2200000]


def test_same_files_again_return_the_same_submission(client, store, drain, tmp_path):
    enrol(store, ALICE)
    d = submission_files(tmp_path, "alice", "BYTES=2300000")
    first = post_submission(client, ALICE, d).json()
    drain()
    again = post_submission(client, ALICE, d).json()
    assert again["submission"] == first["submission"] and again["state"] == "accepted"


# ── What the gate refuses ─────────────────────────────────────────────────


def test_rejected_submission_is_reported_not_ranked(client, store, drain, tmp_path):
    enrol(store, ALICE)
    sid = post_submission(client, ALICE, submission_files(tmp_path, "alice", "REJECT")).json()[
        "submission"
    ]
    drain()
    s = client.get(f"/submissions/{sid}").json()
    assert s["state"] == "rejected" and "REJECTED at stage 4" in s["report"] and s["bytes"] is None
    assert client.get("/leaderboard").json()["ranking"] == []


def test_validator_error_stops_the_worker_and_blames_nobody(client, store, drain, tmp_path):
    # An exit code the gate does not define is the validator's problem: the submission
    # goes back on the queue untouched and the drain stops so an operator notices.
    enrol(store, ALICE, BOB)
    ida = post_submission(client, ALICE, submission_files(tmp_path, "a", "MISCONFIGURED")).json()[
        "submission"
    ]
    idb = post_submission(client, BOB, submission_files(tmp_path, "b", "BYTES=2200000")).json()[
        "submission"
    ]
    assert drain() == 0
    assert client.get(f"/submissions/{ida}").json()["state"] == "queued"
    assert client.get(f"/submissions/{idb}").json()["state"] == "queued"


def test_a_gate_that_never_finishes_is_a_rejection(client, store, drain, tmp_path, monkeypatch):
    enrol(store, ALICE)
    slow = tmp_path / "slow.py"
    slow.write_text("import time; print('stage 3 extract running'); time.sleep(5)")
    monkeypatch.setattr(worker, "VERIFY", slow)
    monkeypatch.setattr(worker, "TOTAL_TIMEOUT", 0.5)
    sid = post_submission(client, ALICE, submission_files(tmp_path, "alice")).json()["submission"]
    drain()
    s = client.get(f"/submissions/{sid}").json()
    assert s["state"] == "rejected" and "did not finish within" in s["report"]


def test_a_worker_that_died_mid_gate_is_reclaimed(client, store, settings, drain, tmp_path, clock):
    # A crashed worker leaves its row in `verifying` with nobody running it. Nothing else
    # would ever pick it up, so the next worker's sweep puts it back on the queue.
    enrol(store, ALICE)
    d = submission_files(tmp_path, "alice", "BYTES=2300000")
    sid = post_submission(client, ALICE, d).json()["submission"]
    assert store.submissions.claim_next("dead-worker").id == sid
    assert store.submissions.get(sid).state == "verifying"
    assert store.submissions.requeue_stale(settings.stale_claim_seconds) == 0  # still fresh
    clock["tick"](settings.stale_claim_seconds + 1)
    assert store.submissions.requeue_stale(settings.stale_claim_seconds) == 1
    assert client.get(f"/submissions/{sid}").json()["state"] == "queued"
    drain()
    assert client.get(f"/submissions/{sid}").json()["state"] == "accepted"


# ── Liveness and readiness ────────────────────────────────────────────────


def test_health_is_liveness_and_ready_is_the_store(client, store, tmp_path):
    enrol(store, ALICE)
    assert client.get("/health").json() == {"ok": True, "queued": 0, "speed_floor": 8.0}
    ready = client.get("/ready").json()
    assert ready["ok"] is True and ready["database"] is True
    post_submission(client, ALICE, submission_files(tmp_path, "alice"))
    assert client.get("/health").json()["queued"] == 1


# ── The real gate ─────────────────────────────────────────────────────────


def toolchain_present() -> bool:
    # Same probe as the gate tests.
    return (
        subprocess.run(
            [str(VALIDATOR / "verifier/init.sh"), "--check"], capture_output=True
        ).returncode
        == 0
    )


@pytest.mark.skipif(
    not toolchain_present(), reason="Charon, Aeneas or Lean missing - run `just init`"
)
def test_the_real_gate_ranks_the_reference_submissions(
    client, store, settings, tmp_path, monkeypatch
):
    # Three reference submissions through the real gate on the reference corpus.
    enrol(store, ALICE, BOB, CHARLIE)
    tree = tmp_path / "validator"
    shutil.copytree(
        VALIDATOR,
        tree,
        ignore=shutil.ignore_patterns(
            ".work", ".lake", "target", "corpus", "tests", "db", "__pycache__"
        ),
    )
    for rel in [".work", "lean/.lake", "slot/target", "harness/target"]:
        if (VALIDATOR / rel).exists():
            (tree / rel).parent.mkdir(parents=True, exist_ok=True)
            (tree / rel).symlink_to(VALIDATOR / rel, target_is_directory=True)
    (tree / "corpus").symlink_to(VALIDATOR / "corpus", target_is_directory=True)
    monkeypatch.setattr(worker, "VERIFY", tree / "verifier/verify.py")

    miners = [
        (ALICE, TEMPLATE),
        (BOB, REPO / "miner/examples/hash-chains"),
        (CHARLIE, REPO / "miner/examples/lazy"),
    ]
    for kp, d in miners:
        assert post_submission(client, kp, d).status_code == 200
    assert worker.drain(store, settings) == 3
    board = client.get("/leaderboard").json()
    assert board["incumbent_bytes"] == 2153387
    assert [x["bytes"] for x in board["ranking"]] == [2153387, 2239367, 2605048]
