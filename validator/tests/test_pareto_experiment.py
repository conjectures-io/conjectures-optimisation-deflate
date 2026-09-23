"""Properties of experimental weights, independent of stored benchmark artifacts."""

import importlib.util
import math
from pathlib import Path

import pytest

from scoring.pareto import METHODS, Point, pareto_front


@pytest.fixture(scope="module")
def spike():
    path = Path(__file__).resolve().parents[2] / "scripts/pareto-weights.py"
    spec = importlib.util.spec_from_file_location("pareto_experiment", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_experiments_do_not_change_production_registry(spike):
    assert len(spike.SPIKE_METHODS) > len(METHODS)
    assert "local-global-total-gain" not in METHODS
    assert "local-global-improvement-space" not in METHODS


@pytest.mark.parametrize("target", ["fast", "elbow", "crawl"])
@pytest.mark.parametrize("count", [1, 4, 16])
@pytest.mark.parametrize("logarithmic", [False, True])
def test_copies_are_tradeoffs_and_keep_original_extremes(spike, target, count, logarithmic):
    base = spike.big_elbow()
    copied, owner = spike.add_near_copies(base, target, count, 1e-6)
    front = pareto_front(copied)
    assert len(front) == len(base) + count
    assert len(owner) == count + 1
    assert (front[0], front[-1]) == (base[0], base[-1])
    before = spike.improvement_space_weights(base, logarithmic=logarithmic)[target]
    weights = spike.improvement_space_weights(front, logarithmic=logarithmic)
    assert sum(weights[name] for name in owner) == pytest.approx(before, abs=2e-6)


def test_experimental_weights_are_finite_and_unit_invariant(spike):
    for name in (set(spike.SPIKE_METHODS) - set(METHODS)) | {"local-global-improvement-space-log"}:
        fn = spike.SPIKE_METHODS[name]
        assert fn([], spike.DEFAULT_BOUNDS) == {}
        assert fn([Point("only", 1, 30)], spike.DEFAULT_BOUNDS) == {"only": 1}
        for points in spike.scenarios().values():
            front = pareto_front(points)
            weights = fn(front, spike.DEFAULT_BOUNDS)
            assert set(weights) == {p.name for p in front}
            assert sum(weights.values()) == pytest.approx(1)
            assert all(math.isfinite(w) and w >= 0 for w in weights.values())
            rescaled = [Point(p.name, p.time_s * 1000, p.ratio_pct / 100) for p in front]
            assert fn(rescaled, spike.DEFAULT_BOUNDS) == pytest.approx(weights)


def test_total_gain_multiplier_does_not_solve_copy_inflation(spike):
    base = spike.big_elbow()
    copied, owner = spike.add_near_copies(base, "elbow", 16, 1e-6)
    fn = spike.SPIKE_METHODS["local-global-total-gain"]
    before = fn(base)["elbow"]
    after = fn(pareto_front(copied))
    assert sum(after[name] for name in owner) > before * 1.2


def test_local_global_multiplier_breaks_incremental_budget_conservation(spike):
    base = spike.big_elbow()
    copied, owner = spike.add_near_copies(base, "elbow", 4, 1e-6)
    fn = spike.SPIKE_METHODS["local-global-improvement-space"]
    before = fn(base, spike.DEFAULT_BOUNDS)["elbow"]
    after = fn(pareto_front(copied), spike.DEFAULT_BOUNDS)
    assert abs(sum(after[name] for name in owner) - before) > 0.01


def test_log_gains_favor_equal_absolute_improvements_at_lower_values(spike):
    front = [Point("fast", 1, 3), Point("middle", 2, 2), Point("small", 3, 1)]
    linear = spike.improvement_space_weights(front)
    log = spike.improvement_space_weights(front, logarithmic=True)
    assert log["fast"] == pytest.approx(0.5 * math.log(2) / math.log(3))
    assert log["small"] == pytest.approx(log["fast"])
    assert log["fast"] > linear["fast"]
    assert log["small"] > linear["small"]


def test_equal_proportional_improvements_receive_equal_axis_credit(spike):
    front = [Point("fast", 1, 4), Point("middle", 2, 2), Point("small", 4, 1)]
    assert spike.improvement_space_weights(front, logarithmic=True) == pytest.approx(
        {"fast": 0.25, "middle": 0.5, "small": 0.25}
    )
    norm = spike.normalizer_for("improvement-space-log", front, spike.DEFAULT_BOUNDS)
    assert norm(2, 2) == pytest.approx((0.5, 0.5))
    assert norm(1, 4) == pytest.approx((0, 1))
    assert norm(4, 1) == pytest.approx((1, 0))
    # Only the multiplier is logarithmic in the combined method.
    combined = spike.normalizer_for(
        "local-global-improvement-space-log", front, spike.DEFAULT_BOUNDS
    )
    assert combined(2, 2) == pytest.approx((1 / 3, 1 / 3))


@pytest.mark.parametrize("value", [0, -1, float("nan"), float("inf")])
@pytest.mark.parametrize("field", ["time", "ratio"])
def test_log_gains_reject_invalid_axes_even_for_singletons(spike, value, field):
    point = Point("bad", value if field == "time" else 1, value if field == "ratio" else 1)
    for name in ("improvement-space-log", "local-global-improvement-space-log"):
        with pytest.raises(ValueError, match="finite positive"):
            spike.SPIKE_METHODS[name]([point], spike.DEFAULT_BOUNDS)


def test_promoted_log_method_preserves_spike_weights_and_is_default(spike):
    from scoring.config import ScoringConfig
    from scoring.pareto import DEFAULT_METHOD, weigh

    assert DEFAULT_METHOD == "local-global-improvement-space-log"
    assert ScoringConfig.from_env({}).method == DEFAULT_METHOD
    assert spike.SPIKE_METHODS[DEFAULT_METHOD] is METHODS[DEFAULT_METHOD]
    expected = {
        "fast": 0.03825759074808355,
        "mid": 0.1323869862587783,
        "elbow": 0.8219246575419754,
        "crawl": 0.007430765451162787,
    }
    assert weigh(spike.big_elbow(), spike.DEFAULT_BOUNDS) == pytest.approx(expected)
