"""Compression scoring includes downstream cost, preserving paired repetitions."""

import copy
import json
from datetime import datetime, timezone

import pytest
from sqlalchemy import select
from test_bench_storage import evidence, save

from bench import report, verdict
from bench.corpora import Corpus
from bench.driver import Measurement
from bench.errors import Malformed
from bench.results import parse
from bench.storage import import_file
from db.aggregation import aggregate, publish, reduce_runs, timing_statistics
from db.models import BenchmarkRun, BenchmarkSpeedSample, Submission
from verifier.identity import required_fingerprint


def paired_evidence():
    raw = evidence()
    raw[0]["measured_rounds"] = 3
    raw[0]["warmup_rounds"] = 1
    raw[0]["benchmark_provenance"] = {
        "engine_sha256": "1" * 64,
        "template_sha256": "2" * 64,
        "host_sha256": "3" * 64,
    }
    # Candidate's median parse=2, encode=2, but median of their paired sum=101.
    # Incumbent's parse=10 (slower!) yet total=11 (over 8x faster).
    for name, pairs in (
        ("candidate", [(1, 100), (2, 2), (100, 1)]),
        ("incumbent", [(10, 1)] * 3),
    ):
        raw[1]["methods"][name]["reps"] = [
            {"phase": "warmup", "order_index": 0, "time_s": 999, "encode_s": 999, "total_s": 1998}
        ] + [
            {
                "phase": "measured",
                "order_index": i + 1,
                "time_s": p,
                "encode_s": e,
                "total_s": p + e,
            }
            for i, (p, e) in enumerate(pairs)
        ]
    return raw


def test_median_of_paired_totals_drives_gate_and_reports(tmp_path):
    corpus = Corpus("tiny", tmp_path, True, {})
    run = parse("\n".join(json.dumps(r) for r in paired_evidence()), corpus)
    total = run.totals("candidate")
    assert (total.parse_s, total.encode_s, total.total_s) == (2, 2, 101)
    decision = verdict.judge(run, "candidate")
    assert decision.accepted and decision.slowdown == pytest.approx(101 / 11)
    measured = Measurement(corpus, (run,), tmp_path, False)
    summary = report.summary(measured)
    methods = summary["methods"]
    assert isinstance(methods, dict)
    assert methods["candidate"]["total_s"] == 101
    assert methods["candidate"]["encode_s"] == 2
    assert "encode" in report.table(measured) and "101.000s" in report.table(measured)
    restored = parse("\n".join(json.dumps(r) for r in report.records(measured)), corpus)
    assert restored.totals("candidate") == total


def test_database_stores_stages_and_scores_total_time(store, tmp_path):
    raw = paired_evidence()
    rid = import_file(store.engine, save(tmp_path, raw))
    with store.sessions.begin() as session:
        samples = list(
            session.scalars(
                select(BenchmarkSpeedSample)
                .where(
                    BenchmarkSpeedSample.run_id == rid,
                    BenchmarkSpeedSample.method == "candidate",
                    BenchmarkSpeedSample.phase == "measured",
                )
                .order_by(BenchmarkSpeedSample.repetition)
            )
        )
        assert [(s.time_s, s.encode_s, s.total_s) for s in samples] == [
            (1, 100, 101),
            (2, 2, 4),
            (100, 1, 101),
        ]
        row = session.get(BenchmarkRun, rid)
        total = reduce_runs([row])
        assert (total.parse_seconds, total.compression_seconds, total.incumbent_seconds) == (
            2,
            101,
            11,
        )
        stats = timing_statistics([row], draws=100)
        assert isinstance(stats["files"], list)
        candidate = next(f for f in stats["files"] if f["method"] == "candidate")
        assert (
            candidate["median_s"] == 101
            and candidate["lz77_median_s"] == candidate["encode_median_s"] == 2
        )
        assert candidate["sample_std_s"] == pytest.approx(97 / 3**0.5)
        assert isinstance(stats["intervals"], dict)
        assert "compression_seconds" in stats["intervals"]
        result = aggregate(session, [row])
        sub = Submission(
            hotkey="miner",
            digest="f" * 64,
            state="accepted",
            source_sha256="b" * 64,
            proof_sha256="e" * 64,
            verifier_fingerprint=required_fingerprint(),
            static_verified_at=datetime.now(timezone.utc),
            lean_verified_at=datetime.now(timezone.utc),
        )
        session.add(sub)
        session.flush()
        publish(session, sub.id, result.id)
    points = store.scoring.scoring_inputs()
    assert len(points) == 1
    assert points[0].time_s == 101 and points[0].incumbent_seconds == 11
    assert points[0].pareto_time == pytest.approx(101 / 11)


@pytest.mark.parametrize("problem", ["missing", "negative", "nonfinite", "sum", "missing_encoder"])
def test_bad_stage_timings_rejected(tmp_path, problem):
    raw = paired_evidence()
    rep = raw[1]["methods"]["candidate"]["reps"][1]
    if problem == "missing":
        del rep["total_s"]
    elif problem == "missing_encoder":
        del rep["encode_s"]
    elif problem == "negative":
        rep["encode_s"] = -1
    elif problem == "nonfinite":
        rep["total_s"] = float("inf")
    else:
        rep["total_s"] = rep["time_s"]
    with pytest.raises(Malformed):
        parse("\n".join(json.dumps(r) for r in raw), Corpus("tiny", tmp_path, False, {}))


def test_legacy_evidence_preserved_but_cannot_score(store, tmp_path):
    raw = paired_evidence()
    raw[0]["schema_version"] = 3
    for result in raw[1]["methods"].values():
        for rep in result["reps"]:
            del rep["encode_s"], rep["total_s"]
    original = copy.deepcopy(raw)
    rid = import_file(store.engine, save(tmp_path, raw))
    with store.sessions() as session:
        row = session.get(BenchmarkRun, rid)
        assert row.raw_data == original and row.status == "complete"
        with pytest.raises(ValueError, match="rebenchmark legacy"):
            reduce_runs([row])
        samples = list(session.scalars(select(BenchmarkSpeedSample)))
        assert all(s.total_s is None and s.encode_s is None for s in samples)
