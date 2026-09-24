"""Reward-budget routing without a chain or database."""

from unittest.mock import Mock

import pytest

import scoring
from chain.types import MetagraphView
from scoring.routing import reward_vector
from workers.weight_setter import WeightSetterConfig, plan_for

TESTNET = 577
META = MetagraphView((0, 3, 121), {"burn": 0, "miner": 3, "collector": 121})


@pytest.mark.parametrize(
    "weights, expected",
    [({}, 0), ({"miner": 1}, 0.2), ({"miner": 0.25}, 0.05), ({"gone": 0.5, "miner": 0.25}, 0.05)],
)
def test_unpaid_allocations_go_to_collector(weights, expected):
    plan = reward_vector(weights, META, collector_uid=121, competition_share=0.2)
    assert plan.submittable
    assert plan.weights == pytest.approx((0, expected, 1 - expected))
    assert sum(plan.weights) == pytest.approx(1)


@pytest.mark.parametrize("share", [0, 0.2, 1])
def test_configurable_budget(share):
    plan = reward_vector({"miner": 1}, META, collector_uid=121, competition_share=share)
    assert plan.weights == pytest.approx((0, share, 1 - share))


@pytest.mark.parametrize("share", [-0.1, 1.1, float("nan"), float("inf")])
def test_invalid_budget_rejected(share):
    with pytest.raises(ValueError):
        WeightSetterConfig(netuid=TESTNET, competition_share_override=share)


@pytest.mark.parametrize(
    "weights", [{"miner": -1}, {"miner": float("nan")}, {"miner": float("inf")}, {"miner": 1.1}]
)
def test_invalid_scores_rejected(weights):
    with pytest.raises(ValueError):
        reward_vector(weights, META, collector_uid=121, competition_share=0.2)


def test_missing_hotkey_does_not_fall_back_to_uid():
    plan, result = plan_for(
        Mock(), META, WeightSetterConfig(treasury_hotkey="missing"), scoring.ScoringConfig()
    )
    assert not plan.submittable
    assert "treasury hotkey missing absent" in (plan.skip_reason or "")
    assert result is None


def test_hotkey_follows_uid_changes_off_mainnet_and_empty_round_goes_to_treasury():
    store = Mock()
    store.scoring.scoring_inputs.return_value = []
    meta = MetagraphView((0, 3, 121), {"collector": 3, "replacement": 121})
    config = WeightSetterConfig(netuid=TESTNET, treasury_hotkey="collector")
    plan, _ = plan_for(store, meta, config, scoring.ScoringConfig())
    assert plan.weights == (0, 1, 0)


def test_env_configuration(monkeypatch):
    # Off mainnet; the collector names are main's original spellings of the treasury ones.
    monkeypatch.setenv("NETUID", str(TESTNET))
    monkeypatch.setenv("WEIGHT_COLLECTOR_UID", "55")
    monkeypatch.setenv("WEIGHT_COLLECTOR_HOTKEY", " collector ")
    monkeypatch.setenv("WEIGHT_COMPETITION_SHARE", ".3")
    config = WeightSetterConfig.from_env()
    assert config.treasury_uid == 55
    assert config.treasury_hotkey == "collector"
    assert config.competition_share == 0.3
    monkeypatch.setenv("WEIGHT_TREASURY_UID", "56")
    with pytest.raises(ValueError, match="disagree"):
        WeightSetterConfig.from_env()
