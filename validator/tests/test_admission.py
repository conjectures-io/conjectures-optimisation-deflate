"""Admission operates on geometry before payout eligibility."""

from dataclasses import replace
from datetime import datetime, timezone

import pytest

from db.scoring import ScoredSubmission
from scoring.admission import advance, ordered_candidates, select_reference


def point(sid, time, ratio, **kwargs):
    return ScoredSubmission(
        sid,
        f"miner{sid}",
        int(ratio * 10),
        1000,
        time,
        500,
        1,
        datetime(2026, 1, 1, tzinfo=timezone.utc),
        normalized_time_ratio=time,
        normalized_ratio_pct=ratio,
        **kwargs,
    )


def test_single_neighbor_and_equal_replacement():
    fast, middle, slow = point(1, 1, 50), point(2, 2, 30), point(3, 4, 20)
    candidate = point(4, 1.5, 30)
    assert select_reference([fast, middle, slow], candidate) == ("test", middle)
    assert advance([fast, middle, slow], candidate, "inconclusive") == [fast, middle, slow]
    assert advance([fast, middle, slow], candidate, "passed") == [fast, candidate, slow]
    # Improving multiple old points still requires the next better-compressing neighbor.
    candidate = point(4, 0.5, 25)
    assert select_reference([fast, middle, slow], candidate) == ("test", slow)
    assert advance([fast, middle, slow], candidate, "passed") == [candidate, slow]


@pytest.mark.parametrize(
    "time,ratio,outcome",
    [
        (1, 50, "dominated"),
        (2, 50, "dominated"),
        (3, 60, "dominated"),
        (4, 10, "not_required"),
        (1, 10, "not_required"),
        (0.9, 60, "test"),
        (0.9, 50, "test"),
    ],
)
def test_endpoints_duplicates_and_domination(time, ratio, outcome):
    assert select_reference([point(1, 1, 50)], point(2, time, ratio))[0] == outcome


def test_order_and_full_precision():
    a = point(1, 1, 30)
    b = point(2, 1, 30 - 1e-12)
    assert select_reference([a], b) == ("not_required", None)
    template = replace(a, baseline_key="template")
    lazy = replace(b, baseline_key="lazy")
    assert ordered_candidates([lazy, a, template]) == [template, lazy, a]
    with pytest.raises(ValueError, match="manifest"):
        ordered_candidates([replace(a, baseline_key="unknown")])


def run_row(rid, values, incumbent=None):
    from test_bench_storage import evidence

    from bench.storage import sha256
    from db.models import BenchmarkRun

    raw = evidence()
    raw[0]["measured_rounds"] = len(values)
    raw[0]["benchmark_provenance"] = {
        "engine_sha256": "1" * 64,
        "template_sha256": "2" * 64,
        "host_sha256": "3" * 64,
    }
    for offset, (name, samples) in enumerate(
        (
            ("incumbent", incumbent or [1.0] * len(values)),
            ("candidate", values),
        )
    ):
        raw[1]["methods"][name]["reps"] = [
            {
                "phase": "measured",
                "order_index": 2 * i + offset,
                "time_s": v * 0.8,
                "encode_s": v * 0.2,
                "total_s": v,
            }
            for i, v in enumerate(samples)
        ]
    return BenchmarkRun(
        id=rid,
        source_sha256="b" * 64,
        candidate_method="candidate",
        corpus="tiny",
        corpus_sha256=sha256([("a.txt", "c" * 64, 100)]),
        status="complete",
        raw_data=raw,
    )


@pytest.mark.parametrize(
    "values,outcome",
    [
        ([0.8] * 11, "passed"),
        ([1.0] * 11, "inconclusive"),
        ([1.2] * 11, "inconclusive"),
        ([0.5, 0.6, 0.7, 0.8, 0.9, 0.99, 1.2, 1.3, 1.4, 1.5, 1.6], "inconclusive"),
    ],
)
def test_bootstrap_outcomes(values, outcome):
    from db.admission_statistics import compare

    c, r = run_row(1, values), run_row(2, [1.0] * 11)
    answer = compare([c], [r], draws=300)
    assert answer["outcome"] == outcome
    assert answer == compare([c], [r], draws=300)
    assert answer["paired_file_observations"] == 2
    assert answer["shared_observations"] == 0


def test_shared_observations_and_independent_runs():
    from db.admission_statistics import compare

    a = run_row(1, [0.7, 0.8, 0.9, 1.0, 1.1])
    shared = compare([a], [a], draws=200)
    assert shared["lower_pct"] == shared["upper_pct"] == 0
    independent = compare([a], [run_row(2, [0.7, 0.8, 0.9, 1.0, 1.1])], draws=200)
    assert independent["lower_pct"] < 0 < independent["upper_pct"]


def test_content_matching_and_sparse_samples():
    from db.admission_statistics import compare

    a, b = run_row(1, [1.0] * 3), run_row(2, [1.0] * 3)
    b.raw_data[1]["sha256"] = "d" * 64
    with pytest.raises(ValueError, match="manifest"):
        compare([a], [b], draws=100)
    with pytest.raises(ValueError, match="repetitions"):
        compare([run_row(1, [1.0] * 2)], [run_row(2, [1.0] * 2)], draws=100)
    with pytest.raises(ValueError):
        compare([run_row(1, [0.0, 0.0, 1.0])], [a], draws=100)


def test_fixed_file_weights_heterogeneous_difficulty_and_reordering():
    from copy import deepcopy

    from bench.storage import sha256
    from db.admission_statistics import compare

    a, b = run_row(1, [0.4] * 3), run_row(2, [1.0] * 3)
    for row, value in ((a, 1100.0), (b, 1000.0)):
        second = deepcopy(row.raw_data[1])
        second.update(file="large", sha256="d" * 64, raw_bytes=100000)
        assert isinstance(second["methods"], dict)
        for name, seconds in (("candidate", value), ("incumbent", 1000.0)):
            for rep in second["methods"][name]["reps"]:
                rep.update(time_s=seconds, encode_s=0.0, total_s=seconds)
        row.raw_data.append(second)
        row.corpus_sha256 = sha256(
            sorted((f["file"], f["sha256"], f["raw_bytes"]) for f in row.raw_data[1:])
        )
    result = compare([a], [b], draws=100)
    assert result["gain_pct"] == pytest.approx(25.0)
    assert result["outcome"] == "passed"
    assert result["file_wins"] == 1  # One regression is allowed.
    b.raw_data[1:] = reversed(b.raw_data[1:])
    other = compare([a], [b], draws=100)
    assert other["gain_pct"] == result["gain_pct"]
    assert other["files"] == result["files"]


def test_simulation_sanity():
    import random

    from db.admission_statistics import compare

    rng = random.Random(31)
    null_passes = win_passes = 0
    for i in range(40):
        ref = [rng.lognormvariate(0, 0.08) for _ in range(11)]
        null = [rng.lognormvariate(0, 0.08) for _ in range(11)]
        r = run_row(2 * i + 1, ref)
        null_passes += compare([run_row(2 * i + 2, null)], [r], draws=200)["outcome"] == "passed"
        win_passes += (
            compare([run_row(2 * i + 2, [v * 0.75 for v in null])], [r], draws=200)["outcome"]
            == "passed"
        )
    # A smoke check for gross errors, not a claim of calibrated 5% finite-sample coverage.
    assert null_passes <= 10
    assert win_passes >= 35


def stored_point(session, rid, values):
    from db.aggregation import aggregate, evaluation_context
    from db.models import Submission

    row = run_row(rid, values)
    session.add(row)
    session.flush()
    agg = aggregate(session, [row])
    sub = Submission(hotkey=f"miner{rid}", digest=f"{rid:064x}")
    session.add(sub)
    session.flush()
    return point(
        sub.id,
        __import__("statistics").median(values),
        30,
        aggregation_id=agg.id,
        context=evaluation_context([row]),
        normalized_incumbent_ratio_pct=50,
    )


def test_db_decisions_idempotent_and_require_explicit_replay(store):
    from sqlalchemy import func, select

    from db.admission import evaluate, publication_lock
    from db.models import Submission, SubmissionAdmissionCheck

    with store.sessions.begin() as session:
        a = stored_point(session, 1, [1.0] * 11)
        b = stored_point(session, 2, [0.8] * 11)
        publication_lock(session)
        points = evaluate(session, [b, a], compute=True, persist=True)
        assert [p.admission["outcome"] for p in points] == ["not_required", "passed"]
        first_ids = [p.admission_check_id for p in points]
        assert first_ids == [
            p.admission_check_id for p in evaluate(session, [a, b], compute=True, persist=True)
        ]
        assert session.scalar(select(func.count()).select_from(SubmissionAdmissionCheck)) == 2
        # Removing the predecessor changes context and cannot silently promote b.
        stale = evaluate(session, [b], compute=True, persist=True)
        assert stale[0].admission["outcome"] == "pending"
        replayed = evaluate(session, [b], compute=True, persist=True, replay=True)
        assert replayed[0].admission["outcome"] == "not_required"
        assert replayed[0].admission_check_id not in first_ids
        assert session.get(SubmissionAdmissionCheck, first_ids[1]).outcome == "passed"
        assert (
            session.get(Submission, b.submission_id).admission_check_id
            == replayed[0].admission_check_id
        )


def test_db_concurrent_publication(store):
    from concurrent.futures import ThreadPoolExecutor

    from db.admission import evaluate, publication_lock

    with store.sessions.begin() as session:
        p = stored_point(session, 1, [1.0] * 3)

    def publish(_):
        with store.sessions.begin() as session:
            publication_lock(session)
            return evaluate(session, [p], compute=True, persist=True)[0].admission_check_id

    with ThreadPoolExecutor(max_workers=2) as pool:
        ids = list(pool.map(publish, range(2)))
    assert ids[0] == ids[1]


def test_db_baseline_prefix_is_required(store):
    from db.admission import evaluate

    with store.sessions.begin() as session:
        p = replace(stored_point(session, 1, [1.0] * 3), baseline_key="lazy")
        result = evaluate(session, [p], compute=True)
        assert result[0].admission["outcome"] == "pending"
        assert result[0].admission["reason_code"] == "awaiting-predecessor"


def test_exclusion_preserves_weights_geometry_and_recency():
    from scoring import ScoringConfig, score

    a = replace(
        point(1, 1, 40),
        baseline_key="template",
        hotkey=None,
        normalized_incumbent_ratio_pct=50,
        admission={"outcome": "not_required"},
    )
    b = replace(
        point(2, 2, 20), normalized_incumbent_ratio_pct=50, admission={"outcome": "not_required"}
    )
    # Appears to improve baseline compression, but uncertain speed vs the smaller neighbor.
    c = replace(
        point(3, 1.9, 21), normalized_incumbent_ratio_pct=50, admission={"outcome": "inconclusive"}
    )
    config = ScoringConfig()
    assert b.hotkey is not None and c.hotkey is not None
    original = score([a, b], [a, b], config, eligible_hotkeys={b.hotkey, c.hotkey})
    result = score([a, b, c], [a, b, c], config, eligible_hotkeys={b.hotkey, c.hotkey})
    assert result.frontier == original.frontier
    assert result.improvements == original.improvements
    assert result.weights == original.weights
    assert result.scores[-1].combined_weight == 0
    assert result.scores[-1].burn_reason == "admission-inconclusive"
    assert result.scores[0].burn_reason == "baseline"
    assert result.scores[0].pareto_weight > 0
    assert "admission_check_id" in result.snapshots()[0]
    assert "admission" not in result.snapshots()[0]


def test_report_payload_and_plots(store, tmp_path):
    from db.admission import evaluate
    from scoring import ScoringConfig, score
    from workers.admission_report import comparison_range, explanation, plot_admission

    with store.sessions.begin() as session:
        reference = stored_point(session, 1, [1.0] * 11)
        winner = stored_point(session, 2, [0.8] * 11)
        noisy = stored_point(session, 3, [0.4, 0.5, 0.6, 0.7, 0.75, 0.79, 0.85, 0.9, 1.0, 1.1, 1.2])
        points = evaluate(session, [reference, winner, noisy], compute=True)
    assert [p.admission["outcome"] for p in points] == ["not_required", "passed", "inconclusive"]
    for p in points[1:]:
        detail = p.admission
        assert detail["preview"]
        assert detail["frontier_before"]
        stats = detail["statistics"]
        assert stats["confidence"] == 0.95
        assert "90%" in stats["interval"]
        assert "95% interval" not in stats["interval"]
        assert stats["files"][0]["sha256"] == "c" * 64
        interval = comparison_range(detail)
        assert interval is not None
        assert interval[0] <= interval[1]
        assert interval[0] == pytest.approx(
            detail["reference"]["time_ratio"] * (1 - stats["upper_pct"] / 100)
        )
        assert "measured" in explanation(detail)
    result = score(points, points, ScoringConfig())
    plot_admission(result.scores, tmp_path)
    assert (tmp_path / "speed-admission.png").is_file()
    assert len(list((tmp_path / "admission").glob("*.png"))) == 2
    plot_admission([], tmp_path)
    assert not (tmp_path / "speed-admission.png").exists()
    assert not list((tmp_path / "admission").glob("*.png"))


def test_missing_decision_is_not_rewarded():
    from scoring import ScoringConfig, score

    p = replace(point(1, 1, 30), aggregation_id=42, normalized_incumbent_ratio_pct=50)
    result = score([p], [p], ScoringConfig())
    assert not result.frontier.frontier
    assert result.scores[0].combined_weight == 0
    assert result.scores[0].burn_reason == "admission-pending"


def test_cleared_pointer_still_requires_replay(store):
    from db.admission import evaluate, publication_lock
    from db.models import Submission

    with store.sessions.begin() as session:
        a = stored_point(session, 1, [1.0] * 3)
        b = stored_point(session, 2, [0.8] * 3)
        publication_lock(session)
        evaluate(session, [a, b], compute=True, persist=True)
        session.get(Submission, b.submission_id).admission_check_id = None
        assert (
            evaluate(session, [b], compute=True, persist=True)[0].admission["outcome"] == "pending"
        )
        assert (
            evaluate(session, [b], compute=True, persist=True, replay=True)[0].admission["outcome"]
            == "not_required"
        )


def test_invalidated_evidence_cannot_keep_current_decision(store):
    from datetime import datetime, timezone

    from db.admission import evaluate, publication_lock
    from db.models import BenchmarkRun

    with store.sessions.begin() as session:
        p = stored_point(session, 1, [1.0] * 3)
        publication_lock(session)
        evaluate(session, [p], compute=True, persist=True)
        row = session.get(BenchmarkRun, 1)
        row.invalidated_at = datetime.now(timezone.utc)
        row.invalidation_reason = "bad host"
        # Public entry points validate through _inputs before reading a decision.
        # Explicit evaluation must also reject an invalidated row, even for a matching pointer.
        result = evaluate(session, [p], compute=True, persist=True, replay=True)
        assert result[0].admission["outcome"] == "invalid_evidence"
