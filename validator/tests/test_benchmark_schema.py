"""Benchmark evidence, reruns and legacy migration compatibility."""

# ruff: noqa: F811 -- imported pytest fixture

import pytest
import sqlalchemy as sa
from alembic import command
from sqlalchemy.exc import IntegrityError
from test_db_schema import (
    _alembic_config,  # pyright: ignore[reportPrivateUsage]
)
from test_db_schema import (
    migrated as migrated,
)

from db import models


def add(conn, model, **values):
    return conn.execute(sa.insert(model).values(**values).returning(model.id)).scalar_one()


def run(conn, corpus="a", raw=None, status="complete"):
    return add(
        conn,
        models.BenchmarkRun,
        source_sha256="a" * 64,
        candidate_method="candidate",
        corpus=corpus,
        corpus_sha256=corpus * 64,
        status=status,
        raw_data=raw if raw is not None else [],
    )


def compression_result(conn, rid, **overrides):
    values = dict(
        run_id=rid,
        file_index=0,
        method="candidate",
        file_path="f",
        file_sha256="b" * 64,
        raw_bytes=100,
        output_bytes=70,
        output_sha256="c" * 64,
        tokens_sha256="d" * 64,
        tokens_deterministic=True,
        succeeded=True,
    )
    values.update(overrides)
    conn.execute(sa.insert(models.BenchmarkCompressionResult).values(**values))


def aggregate(conn, *runs):
    aid = add(
        conn,
        models.BenchmarkAggregation,
        source_sha256="a" * 64,
        calculator_version="v1",
        raw_bytes=100,
        incumbent_bytes=80,
        bytes=70,
        incumbent_seconds=2,
        parse_seconds=1,
    )
    for rid in runs:
        conn.execute(
            sa.insert(models.BenchmarkAggregationInput).values(
                aggregation_id=aid,
                run_id=rid,
            )
        )
    return aid


def test_raw_roundtrip_and_sql_statistics(migrated):
    raw = [
        {
            "kind": "meta",
            "schema_version": 3,
            "cpu_model": "test",
            "warnings": [],
            "methods": {"candidate": {"source_sha256": "a" * 64}},
        },
        {
            "kind": "file",
            "file": "test.bin",
            "sha256": "b" * 64,
            "raw_bytes": 100,
            "methods": {
                "candidate": {
                    "output_bytes": 70,
                    "output_sha256": "c" * 64,
                    "tokens": 12,
                    "tokens_sha256": "d" * 64,
                    "deterministic": True,
                    "encode_s": 0.1,
                    "errors": [],
                    "reps": [
                        {"phase": "warmup", "order_index": 0, "time_s": 20},
                        {"phase": "measured", "order_index": 1, "time_s": 1},
                        {"phase": "measured", "order_index": 2, "time_s": 3},
                    ],
                },
                "reference": {"errors": ["failed"], "reps": []},
            },
        },
    ]
    engine = sa.create_engine(migrated)
    try:
        with engine.begin() as conn:
            rid = run(conn, raw=raw)
            compression_result(conn, rid, file_path="test.bin")
            for i, (phase, time) in enumerate([("warmup", 20), ("measured", 1), ("measured", 3)]):
                conn.execute(
                    sa.insert(models.BenchmarkSpeedSample).values(
                        run_id=rid,
                        file_index=0,
                        method="candidate",
                        repetition=i,
                        phase=phase,
                        order_index=i,
                        time_s=time,
                    )
                )
            assert conn.execute(sa.select(models.BenchmarkRun.raw_data)).scalar_one() == raw
            stddev = conn.execute(
                sa.text(
                    "SELECT stddev_pop(time_s) FROM benchmark_speed_samples "
                    "WHERE run_id=:r AND phase='measured'"
                ),
                {"r": rid},
            ).scalar_one()
            assert stddev == 1
            failed = run(conn, raw=[{"errors": ["engine crashed"]}], status="failed")
            assert failed != rid
    finally:
        engine.dispose()


def test_manual_rerun_preserves_previous_inputs_and_score_reference(migrated):
    engine = sa.create_engine(migrated)
    try:
        with engine.begin() as conn:
            first, second, replacement = run(conn), run(conn, "b"), run(conn, "b")
            old = aggregate(conn, first, second)
            new = aggregate(conn, first, replacement)
            sid = add(conn, models.Submission, hotkey="hot", digest="f" * 64, aggregation_id=old)
            wid = add(
                conn,
                models.WeightSet,
                netuid=1,
                block=1,
                uids=[],
                weights=[],
                accepted=False,
                dry_run=True,
            )
            add(
                conn,
                models.ScoreSnapshot,
                weight_set_id=wid,
                hotkey="hot",
                submission_id=sid,
                aggregation_id=old,
            )
            conn.execute(
                sa.update(models.Submission)
                .where(models.Submission.id == sid)
                .values(aggregation_id=new)
            )
            assert conn.execute(sa.select(models.ScoreSnapshot.aggregation_id)).scalar_one() == old
            inputs = conn.execute(
                sa.select(models.BenchmarkAggregationInput.run_id).where(
                    models.BenchmarkAggregationInput.aggregation_id == old
                )
            )
            assert set(inputs.scalars()) == {first, second}
        with pytest.raises(IntegrityError), engine.begin() as conn:
            conn.execute(sa.delete(models.BenchmarkRun).where(models.BenchmarkRun.id == second))
        with pytest.raises(IntegrityError), engine.begin() as conn:
            conn.execute(
                sa.delete(models.BenchmarkAggregation).where(models.BenchmarkAggregation.id == old)
            )
    finally:
        engine.dispose()


@pytest.mark.parametrize("time", [-1, float("nan"), float("inf")])
def test_invalid_timings_rejected(migrated, time):
    engine = sa.create_engine(migrated)
    try:
        with engine.begin() as conn:
            rid = run(conn)
            compression_result(conn, rid)
        with pytest.raises(IntegrityError), engine.begin() as conn:
            conn.execute(
                sa.insert(models.BenchmarkSpeedSample).values(
                    run_id=rid,
                    file_index=0,
                    method="candidate",
                    repetition=0,
                    phase="measured",
                    order_index=0,
                    time_s=time,
                )
            )
    finally:
        engine.dispose()


def test_upgrade_and_downgrade_preserve_legacy_rows(migrated):
    config = _alembic_config(migrated)
    command.downgrade(config, "0001")
    engine = sa.create_engine(migrated)
    try:
        with engine.begin() as conn:
            sid = conn.execute(
                sa.text(
                    "INSERT INTO submissions (hotkey, digest) VALUES ('hot', 'digest') RETURNING id"
                )
            ).scalar_one()
        command.upgrade(config, "head")
        with engine.begin() as conn:
            aid = aggregate(conn, run(conn))
            conn.execute(
                sa.update(models.Submission)
                .where(models.Submission.id == sid)
                .values(aggregation_id=aid)
            )
        command.downgrade(config, "0001")
        with engine.connect() as conn:
            assert (
                conn.execute(
                    sa.text("SELECT digest FROM submissions WHERE id=:i"), {"i": sid}
                ).scalar_one()
                == "digest"
            )
        command.upgrade(config, "head")
    finally:
        engine.dispose()


@pytest.mark.parametrize(
    "bad",
    [
        {"output_bytes": None},
        {"output_bytes": -1},
        {"raw_bytes": None},
        {"raw_bytes": -1},
        {"output_sha256": None},
        {"file_sha256": "wrong"},
        {"tokens_deterministic": False},
    ],
)
def test_successful_compression_requires_valid_sizes_and_hashes(migrated, bad):
    engine = sa.create_engine(migrated)
    try:
        with engine.begin() as conn:
            rid = run(conn)
        with pytest.raises(IntegrityError), engine.begin() as conn:
            compression_result(conn, rid, **bad)
    finally:
        engine.dispose()


def test_speed_sample_requires_matching_compression_result(migrated):
    engine = sa.create_engine(migrated)
    try:
        with engine.begin() as conn:
            rid = run(conn)
            compression_result(conn, rid)
        with pytest.raises(IntegrityError), engine.begin() as conn:
            conn.execute(
                sa.insert(models.BenchmarkSpeedSample).values(
                    run_id=rid,
                    file_index=0,
                    method="other",
                    repetition=0,
                    phase="measured",
                    order_index=0,
                    time_s=1,
                )
            )
    finally:
        engine.dispose()
