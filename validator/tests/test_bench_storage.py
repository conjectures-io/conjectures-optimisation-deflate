"""Import engine-shaped evidence, including retries and failed writes."""

from __future__ import annotations

import copy
import json
from concurrent.futures import ThreadPoolExecutor
from functools import partial
from typing import Any
from unittest.mock import Mock

import pytest
import sqlalchemy as sa
from sqlalchemy.exc import SQLAlchemyError

from bench import __main__ as cli
from bench import storage
from bench.artifacts import write_import_files
from bench.corpora import Corpus
from bench.driver import Measurement
from bench.errors import Malformed
from bench.results import parse
from db.models import BenchmarkCompressionResult, BenchmarkRun, BenchmarkSpeedSample


def evidence(candidate="candidate", time_s=0.2) -> list[dict[str, Any]]:  # pyright: ignore[reportExplicitAny]
    methods = {
        name: {"external": False, "source_sha256": char * 64, "lib_sha256": char * 64}
        for name, char in (("incumbent", "a"), (candidate, "b"))
    }
    return [
        {
            "kind": "meta",
            "schema_version": 4,
            "started_at_unix": 1700000000.0,
            "corpus": "tiny",
            "corpus_dir": "/no/longer/present",
            "os": "linux",
            "arch": "x86_64",
            "warmup_rounds": 0,
            "measured_rounds": 1,
            "methods": methods,
            "future_metadata": {"preserve": True},
        },
        {
            "kind": "file",
            "file": "a.txt",
            "sha256": "c" * 64,
            "raw_bytes": 100,
            "methods": {
                name: {
                    "external": False,
                    "output_bytes": 50,
                    "output_sha256": "d" * 64,
                    "tokens": 3,
                    "tokens_sha256": "e" * 64,
                    "deterministic": True,
                    "encode_s": 0.1,
                    "errors": [],
                    "reps": [
                        {
                            "phase": "measured",
                            "order_index": i,
                            "time_s": time_s,
                            "encode_s": 0.0,
                            "total_s": time_s,
                        }
                    ],
                }
                for i, name in enumerate(methods)
            },
        },
    ]


def save(tmp_path, raw):
    path = tmp_path / "run.jsonl"
    path.write_text("\n".join(json.dumps(record) for record in raw) + "\n")
    return path


def test_import_preserves_raw_data_and_retries_concurrently(store, tmp_path):
    raw = evidence()
    path = save(tmp_path, raw)
    with ThreadPoolExecutor(max_workers=2) as pool:
        ids = list(pool.map(partial(storage.import_file, store.engine), [path, path]))
    assert ids[0] == ids[1]
    path.write_text("\n".join(json.dumps(record, sort_keys=True) for record in raw))
    assert storage.import_file(store.engine, path) == ids[0]
    with store.engine.connect() as conn:
        assert conn.execute(sa.select(BenchmarkRun.raw_data)).scalar_one() == raw
        assert (
            conn.execute(sa.select(sa.func.count()).select_from(BenchmarkSpeedSample)).scalar() == 2
        )


def test_gate_import_links_run_to_submission_and_attempt(store, tmp_path):
    sid, _ = store.submissions.add("gate-audit", "f" * 64)
    run_id = storage.import_file(
        store.engine,
        save(tmp_path, evidence()),
        submission_id=sid,
        gate_attempt_token="attempt-1",
    )
    with store.sessions.begin() as session:
        run = session.get(BenchmarkRun, run_id)
        assert run.submission_id == sid
        assert run.gate_attempt_token == "attempt-1"


def test_uuid_collision_refused_and_new_execution_kept(store, tmp_path):
    raw = evidence()
    raw[0]["run_uuid"] = "00000000-0000-4000-8000-000000000001"
    first = storage.import_file(store.engine, save(tmp_path, raw))
    raw[0]["future_metadata"] = {"changed": True}
    with pytest.raises(Malformed, match="different data"):
        storage.import_file(store.engine, save(tmp_path, raw))
    raw[0]["run_uuid"] = "00000000-0000-4000-8000-000000000002"
    assert storage.import_file(store.engine, save(tmp_path, raw)) != first


def test_samples_and_run_are_one_transaction(store, tmp_path, monkeypatch):
    original = sa.Connection.execute

    def fail_samples(self, statement, *args, **kwargs):
        if getattr(getattr(statement, "table", None), "name", None) == "benchmark_speed_samples":
            raise RuntimeError("write interrupted")
        return original(self, statement, *args, **kwargs)

    monkeypatch.setattr(sa.Connection, "execute", fail_samples)
    with pytest.raises(RuntimeError, match="interrupted"):
        storage.import_file(store.engine, save(tmp_path, evidence()))
    with store.engine.connect() as conn:
        assert conn.execute(sa.select(sa.func.count()).select_from(BenchmarkRun)).scalar() == 0


def test_failed_candidate_evidence_is_retained(store, tmp_path):
    raw = evidence()
    raw[1]["methods"]["candidate"]["errors"] = ["parser failed"]
    raw[1]["methods"]["candidate"]["reps"] = []
    raw[1]["methods"]["candidate"]["output_bytes"] = None
    raw[1]["methods"]["candidate"]["output_sha256"] = None
    storage.import_file(store.engine, save(tmp_path, raw))
    with store.engine.connect() as conn:
        assert conn.execute(sa.select(BenchmarkRun.status)).scalar_one() == "failed"
        row = conn.execute(
            sa.select(
                BenchmarkCompressionResult.succeeded, BenchmarkCompressionResult.output_bytes
            ).where(BenchmarkCompressionResult.method == "candidate")
        ).one()
        assert tuple(row) == (False, None)


@pytest.mark.parametrize("problem", ["merged", "truncated", "nan", "negative", "missing_files"])
def test_rejects_incomplete_or_ambiguous_evidence(tmp_path, problem):
    raw = evidence()
    if problem == "merged":
        raw[0]["methods"]["other"] = copy.deepcopy(raw[0]["methods"]["candidate"])
    elif problem == "truncated":
        raw[1]["methods"]["candidate"]["reps"] = []
    elif problem in {"nan", "negative"}:
        raw[1]["methods"]["candidate"]["reps"][0]["time_s"] = (
            float("nan") if problem == "nan" else -1
        )
    else:
        raw.pop()
    with pytest.raises((Malformed, ValueError)):
        storage.read_artifact(save(tmp_path, raw))


def measurement(tmp_path):
    corpus = Corpus("tiny", tmp_path, True, {})
    runs = tuple(
        parse("\n".join(json.dumps(r) for r in evidence(name, timing)), corpus)
        for name, timing in (("first", 0.2), ("second", 0.9))
    )
    return Measurement(corpus, runs, tmp_path, False)


def test_artifacts_preserve_each_process_reference_and_unknown_fields(tmp_path):
    paths = write_import_files(measurement(tmp_path), tmp_path, 8.0)
    runs = [storage.read_artifact(path) for path in paths]
    assert [run.files[0].methods["incumbent"].reps[0].time_s for run, _ in runs] == [0.2, 0.9]
    assert all(raw[0]["future_metadata"] == {"preserve": True} for _, raw in runs)
    assert len({raw[0]["run_uuid"] for _, raw in runs}) == 2


def stub_benchmark(monkeypatch, tmp_path):
    monkeypatch.setattr(cli, "configure", Mock(return_value=None))
    monkeypatch.setattr(cli, "candidates", Mock(return_value={}))
    monkeypatch.setattr(cli, "corpus", Mock(return_value=None))
    benchmark = Mock(return_value=measurement(tmp_path))
    monkeypatch.setattr(cli, "run", benchmark)
    return benchmark


def test_local_bench_never_connects_to_db(monkeypatch, tmp_path):
    import db.engine

    stub_benchmark(monkeypatch, tmp_path)
    connect = Mock(side_effect=AssertionError("must stay offline"))
    monkeypatch.setattr(db.engine, "create_db_engine", connect)
    assert cli.main(["--quiet", "--runs-dir", str(tmp_path)]) == 0
    connect.assert_not_called()


def test_db_preflight_prevents_benchmark(monkeypatch, tmp_path):
    benchmark = stub_benchmark(monkeypatch, tmp_path)
    monkeypatch.setattr(storage, "preflight", Mock(side_effect=SQLAlchemyError()))
    assert cli.main(["--store-db", "--quiet"]) == 2
    benchmark.assert_not_called()


def test_db_failure_keeps_all_importable_artifacts(monkeypatch, tmp_path, capsys):
    stub_benchmark(monkeypatch, tmp_path)
    monkeypatch.setattr(storage, "preflight", Mock())
    monkeypatch.setattr(storage, "import_file", Mock(side_effect=SQLAlchemyError()))
    assert cli.main(["--store-db", "--quiet", "--runs-dir", str(tmp_path)]) == 2
    paths = list(tmp_path.glob("*.jsonl"))
    assert len(paths) == 2
    assert all(storage.read_artifact(path) for path in paths)
    assert "just bench-import" in capsys.readouterr().err


def test_db_cli_stores_all_candidates_and_import_retries(store, tmp_path, monkeypatch):
    import db.engine

    stub_benchmark(monkeypatch, tmp_path)
    monkeypatch.setattr(db.engine, "create_db_engine", Mock(return_value=store.engine))
    monkeypatch.setattr(storage, "create_db_engine", Mock(return_value=store.engine))
    assert cli.main(["--store-db", "--quiet", "--runs-dir", str(tmp_path)]) == 0
    paths = list(tmp_path.glob("*.jsonl"))
    assert storage.main([str(path) for path in paths]) == 0
    with store.engine.connect() as conn:
        assert conn.execute(sa.select(sa.func.count()).select_from(BenchmarkRun)).scalar() == 2
        assert (
            conn.execute(sa.select(sa.func.count()).select_from(BenchmarkSpeedSample)).scalar() == 4
        )


@pytest.mark.parametrize("value", [None, -1, True, "50", 2**63])
@pytest.mark.parametrize("method", ["candidate", "incumbent"])
def test_reject_invalid_successful_output_size(tmp_path, method, value):
    raw = evidence()
    raw[1]["methods"][method]["output_bytes"] = value
    with pytest.raises(Malformed):
        storage.read_artifact(save(tmp_path, raw))


def test_sql_compression_ratio_matches_evidence(store, tmp_path):
    raw = evidence()
    raw[1]["methods"]["candidate"]["output_bytes"] = 30
    storage.import_file(store.engine, save(tmp_path, raw))
    with store.engine.connect() as conn:
        ratio = conn.execute(
            sa.text(
                "SELECT sum(output_bytes)::numeric / sum(raw_bytes)"
                " FROM benchmark_compression_results WHERE method='candidate' AND succeeded"
            )
        ).scalar_one()
        assert float(ratio) == 0.3
        row = conn.execute(
            sa.select(
                BenchmarkCompressionResult.file_sha256,
                BenchmarkCompressionResult.tokens_deterministic,
            ).where(BenchmarkCompressionResult.method == "candidate")
        ).one()
        assert tuple(row) == ("c" * 64, None)  # Only one rep: no comparison.


@pytest.mark.parametrize("deterministic", [True, False])
def test_token_determinism_projection(store, tmp_path, deterministic):
    raw = evidence()
    raw[0]["measured_rounds"] = 2
    for result in raw[1]["methods"].values():
        result["reps"].append(
            {"phase": "measured", "order_index": 3, "time_s": 0.1, "encode_s": 0.0, "total_s": 0.1}
        )
    raw[1]["methods"]["candidate"]["deterministic"] = deterministic
    storage.import_file(store.engine, save(tmp_path, raw))
    with store.engine.connect() as conn:
        row = conn.execute(
            sa.select(
                BenchmarkCompressionResult.tokens_deterministic,
                BenchmarkCompressionResult.succeeded,
            ).where(BenchmarkCompressionResult.method == "candidate")
        ).one()
        assert tuple(row) == (deterministic, deterministic)


def test_imported_verification_claims_cannot_certify_submission(store, tmp_path):
    sid, _ = store.submissions.add("untrusted-import", "f" * 64)
    raw = evidence()
    raw[0].update(
        {
            "submission_id": sid,
            "source_sha256": "b" * 64,
            "verifier_fingerprint": "a" * 64,
            "static_verified_at": "2026-09-22T00:00:00Z",
            "lean_verified_at": "2026-09-22T00:00:00Z",
            "measured_source_sha256": "b" * 64,
        }
    )
    storage.import_file(store.engine, save(tmp_path, raw))
    row = store.submissions.get(sid)
    assert row.source_sha256 is None
    assert row.verifier_fingerprint is None
    assert row.static_verified_at is None
    assert row.lean_verified_at is None
    assert row.measured_source_sha256 is None
