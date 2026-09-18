"""Several gate workers, one queue.

The gate is a ~45 minute subprocess, so a validator with more than one machine wants
more than one worker on the same queue. FOR UPDATE ... SKIP LOCKED is what makes that
safe; these tests are what says it is still true.
"""

from __future__ import annotations

import json
import sys
import threading
from copy import deepcopy
from pathlib import Path
from typing import cast

from conftest import register

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

import db as store_pkg  # noqa: E402
from db import SubmissionState  # noqa: E402
from service import sig, worker  # noqa: E402

ALICE = sig.load_keypair("//Alice")


def queue(store, n: int, hotkey: str | None = None) -> list[int]:
    return [store.submissions.add(hotkey or ALICE.ss58_address, f"{i:064x}")[0] for i in range(n)]


def test_a_claim_takes_the_oldest_and_marks_it_verifying(store, clock):
    ids = []
    for i in range(3):
        ids.append(store.submissions.add(ALICE.ss58_address, f"{i:064x}")[0])
        clock["tick"](60)
    first = store.submissions.claim_next("w1")
    assert first.id == ids[0] and first.state == "verifying" and first.worker_id == "w1"
    assert store.submissions.claim_next("w2").id == ids[1]


def test_a_claimed_submission_is_never_handed_out_twice(store):
    ids = queue(store, 1)
    assert store.submissions.claim_next("w1").id == ids[0]
    assert store.submissions.claim_next("w2") is None


def test_an_empty_queue_claims_nothing(store):
    assert store.submissions.claim_next("w1") is None


def test_two_workers_split_one_queue_with_no_overlap(store, database_url):
    """Eight submissions, two workers claiming in parallel: every id claimed once.

    Without SKIP LOCKED the second worker would block on the first worker's row and the
    two would fight over the head of the queue; with it they take different rows.
    """
    ids = set(queue(store, 8))
    stores = [store_pkg.connect(database_url) for _ in range(2)]
    taken: list[list[int]] = [[], []]
    barrier = threading.Barrier(2)

    def claim_all(i: int) -> None:
        barrier.wait()
        while (row := stores[i].submissions.claim_next(f"w{i}")) is not None:
            taken[i].append(row.id)

    threads = [threading.Thread(target=claim_all, args=(i,)) for i in range(2)]
    for t in threads:
        t.start()
    for t in threads:
        t.join(timeout=30)
    for s in stores:
        s.close()

    claimed = taken[0] + taken[1]
    assert sorted(claimed) == sorted(ids)
    assert len(claimed) == len(set(claimed)), "a submission was claimed by both workers"


def test_a_requeued_submission_is_claimable_again_and_costs_nothing(store):
    register(store, ALICE.ss58_address)
    sid = queue(store, 1)[0]
    assert store.submissions.claim_next("w1").id == sid
    store.submissions.requeue(sid)
    row = store.submissions.get(sid)
    assert row.state == "queued" and row.worker_id is None and row.claimed_at is None
    assert store.registrations.available_slots(ALICE.ss58_address) == 1


def test_finish_refuses_a_column_that_is_not_a_score(store):
    # A typo in a field name must fail loudly, not silently drop the number the whole
    # frontier is built from.
    sid = queue(store, 1)[0]
    try:
        store.submissions.finish(sid, SubmissionState.REJECTED, raw_byte=1)
    except ValueError as exc:
        assert "raw_byte" in str(exc)
    else:
        raise AssertionError("finish accepted an unknown column")


# ── Reading the gate's results file ───────────────────────────────────────


def results_file(tmp_path: Path, summary: dict[str, object]) -> Path:
    path = tmp_path / "results.json"
    path.write_text(json.dumps(summary))
    return path


SUMMARY: dict[str, object] = {
    "schema_version": 3,
    "candidates": ["submission"],
    "raw_bytes": 8060939,
    "methods": {
        "incumbent": {"output_bytes": 2153387, "parse_s": 0.520},
        "submission": {"output_bytes": 2115138, "parse_s": 2.230, "slowdown": 4.29},
    },
}


def test_the_results_reader_takes_every_number_scoring_needs(tmp_path):
    assert worker.scored(results_file(tmp_path, SUMMARY)) == {
        "raw_bytes": 8060939,
        "incumbent_bytes": 2153387,
        "bytes": 2115138,
        "incumbent_seconds": 0.520,
        "parse_seconds": 2.230,
        "time_ratio": 4.29,
    }


def test_the_results_reader_does_not_care_what_the_candidate_is_called(tmp_path):
    # `candidates` names it, so a rename in the gate cannot silently stop the store
    # recording a score.
    renamed = deepcopy(SUMMARY)
    methods = cast("dict[str, dict[str, object]]", renamed["methods"])
    renamed["candidates"] = ["my-submission"]
    methods["my-submission"] = methods.pop("submission")
    assert worker.scored(results_file(tmp_path, renamed))["bytes"] == 2115138


def test_a_half_measured_run_records_nothing(tmp_path):
    # All of it or none: a row with bytes but no timing is a point the frontier cannot
    # place, and db.scoring filters it out anyway, so storing one only hides the fault.
    for missing in ("parse_s", "output_bytes"):
        partial = deepcopy(SUMMARY)
        del cast("dict[str, dict[str, object]]", partial["methods"])["submission"][missing]
        assert worker.scored(results_file(tmp_path, partial)) == {}

    no_incumbent = deepcopy(SUMMARY)
    del cast("dict[str, object]", no_incumbent["methods"])["incumbent"]
    assert worker.scored(results_file(tmp_path, no_incumbent)) == {}


def test_a_missing_or_unusable_results_file_records_nothing(tmp_path):
    # A rejected submission never writes one, and that is not an error.
    assert worker.scored(tmp_path / "absent.json") == {}
    assert worker.scored(results_file(tmp_path, {"candidates": [], "methods": {}})) == {}
    assert worker.scored(results_file(tmp_path, {**SUMMARY, "candidates": ["gone"]})) == {}


def test_the_time_ratio_is_the_gates_own(tmp_path):
    # The floor was applied to the gate's slowdown; recomputing it here would be a
    # second opinion on the number the verdict already turned on.
    without = deepcopy(SUMMARY)
    del cast("dict[str, dict[str, object]]", without["methods"])["submission"]["slowdown"]
    assert "time_ratio" not in worker.scored(results_file(tmp_path, without))
