"""Local submissions use the real queue while diagnostics cannot affect competition."""

from dataclasses import replace

import pytest
from sqlalchemy import select

from db import SubmissionState, models
from db.scoring import _scorable  # pyright: ignore[reportPrivateUsage]
from scoring.admission import ordered_candidates
from tools import submission


def files(tmp_path):
    source = tmp_path / "input"
    source.mkdir()
    (source / "parse.rs").write_text("rust")
    (source / "Parse.lean").write_text("lean")
    return source


@pytest.mark.parametrize("baseline", [None, "my-parser"])
def test_queue_claim_finish_without_registration(store, tmp_path, baseline):
    source = files(tmp_path)
    sid = submission.enqueue(store, source, tmp_path / "stored", baseline)
    row = store.submissions.claim_next("worker")
    assert row.id == sid
    assert row.hotkey is None
    assert row.baseline_key == ("local:my-parser" if baseline else None)
    assert (tmp_path / "stored" / str(sid) / "parse.rs").read_text() == "rust"
    assert store.submissions.finish(sid, SubmissionState.ACCEPTED) == "accepted"
    payload = submission.status(store, sid)
    assert payload["kind"] == ("baseline" if baseline else "test")
    rendered = submission.summary(payload)
    assert f"Submission {sid}" in rendered
    assert "Preverification: not recorded" in rendered
    assert "Score:" in rendered
    assert "measured_source_sha256" not in rendered
    assert "statistics" not in rendered
    with store.sessions() as session:
        assert session.scalar(select(models.EntitlementClaim)) is None


def test_files_failure_leaves_no_queue_row(store, tmp_path, monkeypatch):
    def fail(*args):
        raise OSError("disk failed")

    monkeypatch.setattr(submission, "write_submission", fail)
    with pytest.raises(OSError, match="disk failed"):
        submission.enqueue(store, files(tmp_path), tmp_path / "stored")
    assert store.submissions.claim_next("worker") is None
    assert list((tmp_path / "stored").iterdir()) == []


def test_tests_excluded_from_all_scorable_reads(store):
    from test_weight_setter import accept

    sid = accept(store, "miner", 2100000, 1.0)
    # Retain otherwise valid verified evidence, remove only competition ownership.
    with store.sessions.begin() as session:
        row = session.get(models.Submission, sid)
        row.hotkey = None
    with store.sessions() as session:
        for preview in (False, True):
            assert not list(session.scalars(_scorable(select(models.Submission), preview=preview)))
    assert store.submissions.leaderboard() == []
    assert store.submissions.latest_incumbent_bytes() is None
    assert store.scoring.scoring_inputs() == []
    assert store.scoring.preview_inputs() == []


def test_local_baseline_order():
    from test_admission import point

    miner = point(1, 1, 30)
    local = replace(point(2, 2, 20), hotkey=None, baseline_key="local:custom")
    template = replace(point(3, 3, 10), hotkey=None, baseline_key="template")
    assert ordered_candidates([local, miner, template]) == [template, miner, local]


def test_baseline_name_cannot_be_reused(store, tmp_path):
    source = files(tmp_path)
    submission.enqueue(store, source, tmp_path / "stored", "custom")
    with pytest.raises(ValueError, match="already exists"):
        submission.enqueue(store, source, tmp_path / "stored", "custom")


def test_local_baseline_participates_and_burns(store):
    from test_weight_setter import accept

    import scoring
    from db.admission import run

    sid = accept(store, "operator", 2100000, 1.0)
    with store.sessions.begin() as session:
        row = session.get(models.Submission, sid)
        row.hotkey = None
        row.baseline_key = "local:operator-parser"
        row.baseline_active = True
    run(store.scoring, persist=True, replay=True)
    points = store.scoring.scoring_inputs()
    assert [p.submission_id for p in points] == [sid]
    result = scoring.score(points, points, scoring.ScoringConfig(), eligible_hotkeys=set())
    assert result.scores[0].on_frontier
    assert result.scores[0].burn_reason == "baseline"
    assert result.scores[0].payable_weight == 0


def test_status_reports_live_pending_instead_of_old_acceptance(store):
    from test_weight_setter import accept

    sid = accept(store, "miner", 2100000, 1.0)
    with store.sessions.begin() as session:
        session.add(
            models.Submission(
                hotkey=None,
                baseline_key="template",
                baseline_active=True,
                digest="a" * 64,
                state="queued",
            )
        )
    payload = submission.status(store, sid)
    assert payload["admission"]["details"]["outcome"] == "pending"
    assert payload["admission"]["details"]["reason_code"] == "awaiting-predecessor"
    rendered = submission.summary(payload)
    assert "gate passed" in rendered
    assert "pending — awaiting current baseline evidence" in rendered
    # Status is read-only: it does not erase the prior recorded decision.
    assert payload["admission"]["recorded_details"] is not None
