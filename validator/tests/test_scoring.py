"""The 60/40 rule: what each component pays, and what neither does.

All pure. Points and improvement events are built directly rather than through a database,
because the rule is arithmetic and the arithmetic is what is worth pinning down.
"""

from __future__ import annotations

import dataclasses as dc
import datetime as dt
import sys
from pathlib import Path
from typing import cast

import pytest

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

import scoring  # noqa: E402
from chain.types import MetagraphView  # noqa: E402
from db.scored import ScoredSubmission  # noqa: E402

T0 = dt.datetime(2026, 10, 1, 12, 0, tzinfo=dt.timezone.utc)
RAW = 8_060_939
INCUMBENT_BYTES = 2_153_387
INCUMBENT_SECONDS = 0.52


def sub(hotkey, byte_count, seconds, *, minutes=0, incumbent=INCUMBENT_BYTES, sid=None):
    # One accepted submission, reduced to what scoring reads.
    return ScoredSubmission(
        submission_id=sid if sid is not None else minutes + 1,
        hotkey=hotkey,
        bytes=byte_count,
        raw_bytes=RAW,
        time_s=seconds,
        incumbent_bytes=incumbent,
        incumbent_seconds=INCUMBENT_SECONDS,
        submitted_at=T0 + dt.timedelta(minutes=minutes),
    )


CONFIG = scoring.ScoringConfig()


# ── Configuration refuses nonsense ────────────────────────────────────────


def test_an_unknown_method_will_not_start_the_worker():
    with pytest.raises(ValueError, match="unknown scoring method"):
        scoring.ScoringConfig(method="whatever")


def test_the_shares_cannot_exceed_all_of_emission():
    with pytest.raises(ValueError, match="must not exceed 1"):
        scoring.ScoringConfig(pareto_share=0.7, improvement_share=0.5)


def test_what_neither_component_claims_is_the_burn_share():
    assert scoring.ScoringConfig().burn_share == pytest.approx(0.0)
    assert scoring.ScoringConfig(
        pareto_share=0.3, improvement_share=0.2
    ).burn_share == pytest.approx(0.5)


def test_the_environment_is_read_strictly():
    config = scoring.ScoringConfig.from_env(
        {"SCORING_METHOD": "diagonal-sweep-k1.0", "SCORING_PARETO_SHARE": "0.5"}
    )
    assert config.method == "diagonal-sweep-k1.0" and config.pareto_share == 0.5
    with pytest.raises(ValueError, match="not a number"):
        scoring.ScoringConfig.from_env({"SCORING_PARETO_SHARE": "most of it"})


# ── The 60%: the frontier ─────────────────────────────────────────────────


def test_the_frontier_share_sums_to_the_pareto_share():
    rows = [
        sub("a", 2_100_000, 2.0, sid=1),
        sub("b", 2_200_000, 0.5, sid=2),
        sub("c", 2_300_000, 0.25, sid=3),
    ]
    result = scoring.score_frontier(rows, CONFIG)
    assert sum(result.weights.values()) == pytest.approx(CONFIG.pareto_share)
    assert set(result.frontier) == {"1", "2", "3"}


def test_a_dominated_hotkey_earns_nothing_from_the_frontier():
    # `slow` is both slower and larger than `good`: there is no sense in which it bought
    # anything, so the Pareto component pays it zero.
    rows = [sub("good", 2_100_000, 0.5, sid=1), sub("slow", 2_300_000, 2.0, sid=2)]
    result = scoring.score_frontier(rows, CONFIG)
    assert result.weights["2"] == 0.0
    assert result.weights["1"] == pytest.approx(CONFIG.pareto_share)
    assert result.on_frontier("1") and not result.on_frontier("2")


def test_the_time_boundary_follows_the_newest_measurement():
    # The incumbent can be promoted mid-round, and then submissions disagree about its
    # time. The newest measurement describes the gate as it stands now.
    old = sub("a", 2_200_000, 0.5, minutes=0)
    new = sub("b", 2_100_000, 1.0, minutes=60)
    new = dc.replace(new, incumbent_seconds=0.25)
    bounds = scoring.boundaries_for([old, new], CONFIG.speed_floor)
    assert bounds.time_s == pytest.approx(8.0 * 0.25)


def test_an_empty_round_pays_nobody_from_the_frontier():
    result = scoring.score_frontier([], CONFIG)
    assert result.weights == {} and result.frontier == ()


# ── The 40%: recent improvement ───────────────────────────────────────────


def test_only_a_submission_that_beats_the_record_counts():
    history = [
        sub("a", 2_100_000, 0.5, minutes=0),  # beats the incumbent: an improvement
        sub("b", 2_150_000, 0.5, minutes=10),  # beats the incumbent but not a: no
        sub("c", 2_000_000, 0.5, minutes=20),  # beats a: an improvement
    ]
    events = scoring.improvement_events(history, CONFIG.improvement_threshold)
    assert [e.hotkey for e in events] == ["a", "c"]
    assert events[0].previous_best == INCUMBENT_BYTES
    assert events[1].previous_best == 2_100_000


def test_a_submission_worse_than_the_incumbent_never_counts():
    # The record starts at the baseline every miner is given, not at infinity: beating
    # nothing is not an advance.
    history = [sub("a", INCUMBENT_BYTES + 1000, 0.5)]
    assert scoring.improvement_events(history, CONFIG.improvement_threshold) == []


def test_an_improvement_under_the_threshold_is_noise_not_progress():
    just_under = int(INCUMBENT_BYTES * (1 - CONFIG.improvement_threshold / 2))
    just_over = int(INCUMBENT_BYTES * (1 - CONFIG.improvement_threshold * 2))
    assert (
        scoring.improvement_events([sub("a", just_under, 0.5)], CONFIG.improvement_threshold) == []
    )
    assert (
        len(scoring.improvement_events([sub("a", just_over, 0.5)], CONFIG.improvement_threshold))
        == 1
    )


def test_promoting_a_new_incumbent_raises_the_bar_rather_than_giving_one_away():
    # After a promotion the reported incumbent is smaller; the next submission has to
    # beat that, not the old record.
    history = [
        sub("a", 2_100_000, 0.5, minutes=0),
        sub("b", 2_090_000, 0.5, minutes=10, incumbent=2_000_000),
    ]
    events = scoring.improvement_events(history, CONFIG.improvement_threshold)
    assert [e.hotkey for e in events] == ["a"]


def test_the_decay_is_monotone_and_sums_to_one():
    shares = scoring.decay_shares(10, 0.6)
    assert sum(shares) == pytest.approx(1.0)
    assert shares == sorted(shares, reverse=True)
    assert shares[0] > 0.39 and shares[-1] < 0.01
    assert scoring.decay_shares(0, 0.6) == []


def test_the_newest_improvement_is_paid_most():
    history = [
        sub("old", 2_100_000, 0.5, minutes=0),
        sub("new", 2_000_000, 0.5, minutes=10),
    ]
    weights, events = scoring.score_improvements(history, CONFIG)
    assert sum(weights.values()) == pytest.approx(CONFIG.improvement_share)
    assert weights["new"] > weights["old"]
    assert [e.hotkey for e in events] == ["new", "old"]


def test_only_the_last_n_improvements_are_paid():
    history = [sub(f"h{i}", 2_200_000 - i * 10_000, 0.5, minutes=i, sid=i + 1) for i in range(15)]
    config = scoring.ScoringConfig(improvement_window=3)
    weights, events = scoring.score_improvements(history, config)
    assert len(events) == 3
    assert set(weights) == {"h14", "h13", "h12"}
    assert sum(weights.values()) == pytest.approx(config.improvement_share)


def test_several_improvements_from_one_hotkey_accumulate():
    history = [
        sub("a", 2_100_000, 0.5, minutes=0, sid=1),
        sub("a", 2_000_000, 0.5, minutes=10, sid=2),
        sub("b", 1_900_000, 0.5, minutes=20, sid=3),
    ]
    weights, _ = scoring.score_improvements(history, CONFIG)
    # Three events, two of them a's: a holds two decaying slots to b's one.
    assert sum(weights.values()) == pytest.approx(CONFIG.improvement_share)
    assert weights["a"] > 0 and weights["b"] > 0


def test_a_round_with_no_improvement_burns_the_share():
    # Nothing has beaten the incumbent, so there is no recent progress to reward, and
    # spreading it over the frontier would quietly turn 60/40 into something else.
    weights, events = scoring.score_improvements([sub("a", INCUMBENT_BYTES + 1, 0.5)], CONFIG)
    assert weights == {} and events == []


# ── Both together ─────────────────────────────────────────────────────────


def test_the_two_components_add_to_one_when_both_have_something_to_pay():
    best = [sub("a", 2_100_000, 2.0, sid=1), sub("b", 2_200_000, 0.5, sid=2)]
    result = scoring.score(best, best, CONFIG)
    assert sum(result.weights.values()) == pytest.approx(1.0)
    by_hotkey = {s.hotkey: s for s in result.scores}
    assert by_hotkey["a"].pareto_weight + by_hotkey["a"].improvement_weight == pytest.approx(
        by_hotkey["a"].combined_weight
    )


def test_a_hotkey_can_earn_from_recency_without_being_on_the_frontier():
    # This is why there are two components: `late` is dominated on the frontier but is
    # the most recent real improvement in bytes.
    best = [sub("fast", 2_150_000, 0.25, sid=1), sub("late", 2_100_000, 3.0, sid=2, minutes=10)]
    history = [best[0], best[1]]
    result = scoring.score(best, history, CONFIG)
    late = next(s for s in result.scores if s.hotkey == "late")
    assert late.improvement_weight > 0
    assert late.combined_weight > 0


def test_the_snapshot_carries_the_point_it_was_scored_on():
    best = [sub("a", 2_100_000, 2.0, sid=7)]
    result = scoring.score(best, best, CONFIG)
    snap = result.snapshots()[0]
    assert snap["hotkey"] == "a" and snap["submission_id"] == 7
    assert snap["time_s"] == 2.0
    assert snap["ratio_pct"] == pytest.approx(100.0 * 2_100_000 / RAW)
    assert snap["on_frontier"] is True
    assert snap["combined_weight"] == pytest.approx(
        cast(float, snap["pareto_weight"]) + cast(float, snap["improvement_weight"])
    )


# ── Onto the metagraph ────────────────────────────────────────────────────


def meta(**hotkeys_by_uid) -> MetagraphView:
    by_uid = {int(u.lstrip("u")): h for u, h in hotkeys_by_uid.items()}
    return MetagraphView(
        uids=tuple(sorted(by_uid)), uid_by_hotkey={h: u for u, h in by_uid.items()}
    )


def test_the_vector_covers_every_uid_and_sums_to_one():
    view = meta(u0="burn", u1="a", u2="b", u3="nobody")
    plan = scoring.to_vector({"a": 0.6, "b": 0.4}, view)
    assert plan.submittable and plan.uids == (0, 1, 2, 3)
    assert sum(plan.weights) == pytest.approx(1.0)
    assert plan.weights == pytest.approx((0.0, 0.6, 0.4, 0.0))


def test_a_deregistered_hotkeys_share_burns_rather_than_being_shared_out():
    # Redistributing it would quietly pay everyone else for someone else's work.
    view = meta(u0="burn", u1="a")
    plan = scoring.to_vector({"a": 0.6, "gone": 0.4}, view)
    assert plan.weights[view.uids.index(1)] == pytest.approx(0.6)
    assert plan.weights[view.uids.index(0)] == pytest.approx(0.4)
    assert "unregistered" in plan.summary


def test_nobody_scored_means_everything_burns():
    plan = scoring.to_vector({}, meta(u0="burn", u1="a"))
    assert plan.submittable and plan.weights == pytest.approx((1.0, 0.0))


def test_an_absent_burn_uid_makes_the_vector_unsubmittable():
    # Better to skip an epoch than to submit a vector that does not sum to one.
    plan = scoring.to_vector({"a": 0.6}, meta(u1="a", u2="b"), burn_uid=0)
    assert not plan.submittable and "burn uid 0 absent" in (plan.skip_reason or "")


def test_an_empty_metagraph_is_unsubmittable():
    plan = scoring.to_vector({"a": 1.0}, MetagraphView(uids=(), uid_by_hotkey={}))
    assert not plan.submittable and "no neurons" in (plan.skip_reason or "")


def test_the_burn_uid_is_never_paid_as_a_miner():
    # A validator's own hotkey holding the burn uid must not collect a miner's share on
    # top of the burn.
    view = meta(u0="burn", u1="a")
    plan = scoring.to_vector({"burn": 0.5, "a": 0.5}, view, burn_uid=0)
    assert plan.weights == pytest.approx((0.5, 0.5))


def test_eligibility_does_not_change_geometry_and_oldest_hotkey_point_is_paid():
    rows = [
        dc.replace(sub(None, 2_400_000, 0.1, sid=1), baseline_key="floor"),
        sub("miner", 2_300_000, 0.2, sid=2, minutes=1),
        sub("miner", 2_200_000, 0.4, sid=3, minutes=2),
        sub("gone", 2_160_000, 0.8, sid=4, minutes=3),
    ]
    a = scoring.score(rows, rows, CONFIG, eligible_hotkeys={"miner", "gone"})
    b = scoring.score(rows, rows, CONFIG, eligible_hotkeys={"miner"})
    assert a.frontier == b.frontier
    by_id = {s.submission_id: s for s in b.scores}
    assert by_id[1].burn_reason == "baseline" and by_id[1].payable_weight == 0
    assert by_id[2].payable_weight == by_id[2].pareto_weight
    assert by_id[3].burn_reason == "duplicate-hotkey" and by_id[3].payable_weight == 0
    assert by_id[4].burn_reason == "deregistered" and by_id[4].payable_weight == 0
    assert sum(b.weights.values()) + b.burn_weight == pytest.approx(1)


def test_exact_duplicate_coordinates_preserve_oldest_point():
    rows = [sub("later", 2_200_000, 0.5, sid=2, minutes=1), sub("first", 2_200_000, 0.5, sid=1)]
    result = scoring.score(rows, rows, CONFIG)
    assert result.frontier.frontier == ("1",)


def test_baselines_establish_record_without_recent_improvement_events():
    baseline = dc.replace(sub(None, 2_000_000, 1, sid=1), baseline_key="optimal")
    no_improvement = sub("miner", 2_050_000, 0.5, sid=2, minutes=1)
    assert scoring.improvement_events([baseline, no_improvement], 0.0025) == []
    result = scoring.score([baseline], [baseline], CONFIG, eligible_hotkeys=set())
    assert result.burn_weight == 1


def test_relative_time_drives_frontier_while_snapshots_keep_seconds():
    fast_absolute = dc.replace(sub("a", 100, 1, sid=1), normalized_time_ratio=2)
    fast_relative = dc.replace(sub("b", 100, 10, sid=2), normalized_time_ratio=0.5)
    points = [fast_absolute, fast_relative]
    result = scoring.score(points, points, CONFIG)
    assert result.frontier.frontier == ("2",)
    assert result.frontier.points["2"].time_s == 0.5
    assert result.frontier.bounds.time_s == CONFIG.speed_floor
    selected = next(s for s in result.scores if s.submission_id == 2)
    assert selected.normalized_time_ratio == 0.5 and selected.time_s == 10
    assert selected.as_snapshot()["time_s"] == 10
    assert "normalized_time_ratio" not in selected.as_snapshot()
    with pytest.raises(ValueError, match="absolute and relative"):
        scoring.score(points, [dc.replace(fast_absolute, normalized_time_ratio=None)], CONFIG)
