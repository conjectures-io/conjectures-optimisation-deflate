"""Snapshot expiry preserves current API evidence and historical payout records."""

from dataclasses import replace
from datetime import datetime, timedelta, timezone
from unittest.mock import Mock

import pytest
import sqlalchemy as sa

from db import models
from workers import weight_setter


def test_cleanup_is_batched_preserves_latest_and_other_subnets(store):
    now = datetime.now(timezone.utc)
    old = now - timedelta(days=2)
    with store.engine.begin() as conn:
        ids = []
        for netuid, created_at, payload in (
            (66, old, {"policy": {}}),
            (66, old, {"policy": {}}),
            (66, now, {"policy": {}}),
            (67, old, {"policy": {}}),
            (66, old, None),  # JSON null must not count as a valid latest snapshot.
        ):
            ids.append(
                conn.execute(
                    sa.insert(models.WeightSet)
                    .values(
                        netuid=netuid,
                        block=1,
                        uids=[1],
                        weights=[1.0],
                        accepted=True,
                        created_at=created_at,
                        api_snapshot=payload,
                    )
                    .returning(models.WeightSet.id)
                ).scalar_one()
            )
        conn.execute(sa.insert(models.ScoreSnapshot).values(weight_set_id=ids[0]))

    prune = store.scoring.prune_api_snapshots
    assert prune(netuid=66, retention_seconds=3600, batch_size=1) == 1
    assert prune(netuid=66, retention_seconds=3600, batch_size=10) == 2
    assert prune(netuid=66, retention_seconds=3600, batch_size=10) == 0
    with store.engine.connect() as conn:
        assert conn.scalar(sa.select(sa.func.count()).select_from(models.WeightSet)) == 5
        assert conn.scalar(sa.select(sa.func.count()).select_from(models.ScoreSnapshot)) == 1
        assert (
            conn.scalar(
                sa.select(sa.func.count())
                .select_from(models.WeightSet)
                .where(models.WeightSet.api_snapshot.is_(None))
            )
            == 3
        )
        assert conn.scalar(sa.select(models.WeightSet.weights).where(models.WeightSet.id == ids[0]))
    # An old latest valid snapshot survives even when a newer row contains JSON null.
    with store.engine.begin() as conn:
        conn.execute(
            sa.update(models.WeightSet).where(models.WeightSet.id == ids[2]).values(created_at=old)
        )
    assert prune(netuid=66, retention_seconds=3600, batch_size=10) == 0
    assert prune(netuid=67, retention_seconds=3600, batch_size=10) == 0


def test_cleanup_cadence_and_failure_do_not_stop_ticks(monkeypatch):
    store = Mock()
    store.scoring.prune_api_snapshots.side_effect = [RuntimeError("lock timeout"), 2]
    step = Mock(return_value=weight_setter.StepResult("wait", "waiting"))
    monkeypatch.setattr(weight_setter, "step", step)
    ticks = 0
    clock = 0.0

    def sleep(_seconds):
        nonlocal ticks, clock
        ticks += 1
        clock += 100
        if ticks == 5:
            raise KeyboardInterrupt

    weight_setter.run(
        Mock(),
        store,
        weight_setter.WeightSetterConfig(),
        Mock(),
        sleep=sleep,
        monotonic=lambda: clock,
    )
    assert step.call_count == 5
    assert store.scoring.prune_api_snapshots.call_count == 2
    store.scoring.prune_api_snapshots.assert_called_with(
        netuid=66, retention_seconds=3600, batch_size=100
    )


def test_retention_configuration_from_environment(monkeypatch):
    monkeypatch.setenv("API_SNAPSHOT_RETENTION_SECONDS", "7200")
    monkeypatch.setenv("API_SNAPSHOT_CLEANUP_INTERVAL_SECONDS", "60")
    monkeypatch.setenv("API_SNAPSHOT_CLEANUP_BATCH_SIZE", "50")
    config = weight_setter.WeightSetterConfig.from_env()
    assert config.api_snapshot_retention_seconds == 7200
    assert config.api_snapshot_cleanup_interval_seconds == 60
    assert config.api_snapshot_cleanup_batch_size == 50


@pytest.mark.parametrize(
    "field",
    [
        "api_snapshot_retention_seconds",
        "api_snapshot_cleanup_interval_seconds",
        "api_snapshot_cleanup_batch_size",
    ],
)
def test_retention_settings_must_be_positive(field):
    with pytest.raises(ValueError, match="must be positive"):
        replace(weight_setter.WeightSetterConfig(), **{field: 0})
