"""Submissions queued through the platform API, whose files live in the database.

The conjectures platform API runs apart from the gate host and shares no disk with it, so it
queues a submission as a row plus its two files in `submission_files`. The gate worker writes
those into the submission directory verify.py reads. These pin that a platform-queued
submission is verified exactly like one queued here, and that the database copy -- the one the
submitter's signature covers -- is what the gate sees.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest
from conftest import REPO, register

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

import db as store_pkg  # noqa: E402
from db import SubmissionState, models  # noqa: E402
from service import sig, worker  # noqa: E402

ALICE = sig.load_keypair("//Alice")
TEMPLATE = REPO / "miner/template"


def _queue_through_the_platform(store, *, marker: str = "") -> int:
    """What the platform API's miniz adapter writes: a queued row and both files.

    The digest is the real one: the gate refuses stored content that does not match the digest
    the submitter signed, which is the property that makes the database copy trustworthy.
    """
    rust = (TEMPLATE / "parse.rs").read_bytes() + (f"\n// {marker}\n".encode() if marker else b"")
    lean = (TEMPLATE / "Parse.lean").read_bytes()
    sub_id, fresh = store.submissions.add(ALICE.ss58_address, sig.digest_of(rust, lean))
    assert fresh
    with store_pkg.session_scope(store.sessions) as session:
        session.add(models.SubmissionFile(submission_id=sub_id, name="parse.rs", content=rust))
        session.add(models.SubmissionFile(submission_id=sub_id, name="Parse.lean", content=lean))
    return sub_id


def test_files_are_read_back_by_name_and_absent_for_a_disk_queued_submission(store):
    platform = _queue_through_the_platform(store)
    local, _ = store.submissions.add(ALICE.ss58_address, "b" * 64)
    assert set(store.submissions.files(platform)) == {"parse.rs", "Parse.lean"}
    assert store.submissions.files(local) == {}


def test_materialize_writes_the_database_copy_over_anything_already_there(store, tmp_path):
    sub_id = _queue_through_the_platform(store, marker="FROM-THE-DATABASE")
    directory = tmp_path / str(sub_id)
    directory.mkdir()
    (directory / "parse.rs").write_text("// a stale copy from an earlier run\n")

    assert worker.materialize(store, sub_id, directory) is True
    assert "FROM-THE-DATABASE" in (directory / "parse.rs").read_text()
    assert (directory / "Parse.lean").read_bytes() == (TEMPLATE / "Parse.lean").read_bytes()


def test_materialize_leaves_a_disk_queued_submission_alone(store, tmp_path):
    sub_id, _ = store.submissions.add(ALICE.ss58_address, "c" * 64)
    assert worker.materialize(store, sub_id, tmp_path / str(sub_id)) is False
    assert not (tmp_path / str(sub_id)).exists()


def test_a_half_stored_submission_is_the_validators_problem_not_the_miners(store, settings):
    sub_id, _ = store.submissions.add(ALICE.ss58_address, "d" * 64)
    with store_pkg.session_scope(store.sessions) as session:
        session.add(models.SubmissionFile(submission_id=sub_id, name="parse.rs", content=b"x"))
    claimed = store.submissions.claim_next("w")
    assert claimed is not None and claimed.id == sub_id

    assert worker.score_one(store, settings, claimed) == SubmissionState.ERROR.value
    row = store.submissions.get(sub_id)
    assert row is not None
    # Back on the queue, uncharged, with no verdict recorded against the miner.
    assert (row.state, row.exit_code) == (SubmissionState.QUEUED.value, None)


@pytest.mark.parametrize(("marker", "state"), [("", "accepted"), ("REJECT", "rejected")])
def test_a_platform_queued_submission_is_verified_like_any_other(store, drain, marker, state):
    register(store, ALICE.ss58_address)
    sub_id = _queue_through_the_platform(store, marker=marker)
    assert drain() == 1
    row = store.submissions.get(sub_id)
    assert row is not None and row.state == state
