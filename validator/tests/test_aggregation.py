"""Explicit corpus selection must not silently change evaluation evidence."""

from datetime import datetime, timezone

import pytest

from db.aggregation import CorpusIdentity, select_runs
from db.models import BenchmarkRun


def add_run(
    session, *, name="tiny", digest="c", started: int | None = 10, status="complete", invalid=False
):
    row = BenchmarkRun(
        source_sha256="b" * 64,
        candidate_method="candidate",
        corpus=name,
        corpus_sha256=digest * 64,
        status=status,
        raw_data=[],
        started_at=datetime.fromtimestamp(started, timezone.utc) if started else None,
        invalidated_at=datetime.now(timezone.utc) if invalid else None,
        invalidation_reason="bad host" if invalid else None,
    )
    session.add(row)
    session.flush()
    return row


def test_latest_measured_not_latest_imported(store):
    with store.sessions.begin() as session:
        newest = add_run(session, started=20)
        add_run(session, started=10)
        add_run(session, started=None)
        add_run(session, started=30, invalid=True)
        add_run(session, started=40, status="failed")
        selected = select_runs(session, "b" * 64, [CorpusIdentity("tiny", "c" * 64)])
        assert [r.id for r in selected] == [newest.id]


def test_explicit_legacy_and_exact_corpus_selection(store):
    with store.sessions.begin() as session:
        first = add_run(session, started=None)
        second = add_run(session, name="other", digest="d")
        wanted = [CorpusIdentity("tiny", "c" * 64), CorpusIdentity("other", "d" * 64)]
        assert {r.id for r in select_runs(session, "b" * 64, wanted, [second.id, first.id])} == {
            first.id,
            second.id,
        }
        with pytest.raises(ValueError, match="timestamped"):
            select_runs(session, "b" * 64, wanted)
        with pytest.raises(ValueError, match="exact requested"):
            select_runs(session, "b" * 64, [CorpusIdentity("tiny", "e" * 64)], [first.id])
        with pytest.raises(ValueError, match="source mismatch"):
            select_runs(session, "a" * 64, [wanted[0]], [first.id])


def test_explicit_failed_and_duplicate_selection_rejected(store):
    with store.sessions.begin() as session:
        row = add_run(session, status="failed")
        wanted = [CorpusIdentity("tiny", "c" * 64)]
        with pytest.raises(ValueError, match="failed or invalidated"):
            select_runs(session, "b" * 64, wanted, [row.id])
        with pytest.raises(ValueError, match="uniquely named"):
            select_runs(session, "b" * 64, wanted * 2)
        with pytest.raises(ValueError, match="exactly one"):
            select_runs(session, "b" * 64, wanted, [row.id, row.id])


def test_corpus_identity_requires_hash():
    with pytest.raises(ValueError, match="SHA-256"):
        CorpusIdentity("tiny", "unknown")


def test_evidence_validation_requires_repeated_determinism(tmp_path):
    from test_bench_storage import evidence

    from bench.storage import sha256
    from db.aggregation import validate_evidence

    raw = evidence()
    row = BenchmarkRun(
        id=1,
        source_sha256="b" * 64,
        candidate_method="candidate",
        corpus="tiny",
        corpus_sha256=sha256([("a.txt", "c" * 64, 100)]),
        status="complete",
        raw_data=raw,
    )
    with pytest.raises(ValueError, match="determinism"):
        validate_evidence(row)
    raw[0]["measured_rounds"] = 2
    for result in raw[1]["methods"].values():
        result["reps"].append(
            {"phase": "measured", "order_index": 2, "time_s": 0.3, "encode_s": 0.0, "total_s": 0.3}
        )
    assert validate_evidence(row).meta.measured_rounds == 2
    raw[1]["methods"]["candidate"]["reps"].pop()
    with pytest.raises(ValueError, match="incomplete"):
        validate_evidence(row)


def measured_row(session, name="one", offset=0):
    from test_bench_storage import evidence

    from bench.storage import sha256

    raw = evidence()
    raw[0]["corpus"] = name
    raw[0]["measured_rounds"] = 3
    raw[0]["warmup_rounds"] = 1
    raw[0]["benchmark_provenance"] = {
        "engine_sha256": "1" * 64,
        "template_sha256": "2" * 64,
        "host_sha256": "3" * 64,
    }
    raw[1]["sha256"] = ("c" if name == "one" else "d") * 64
    for method, values in (("candidate", [1.0, 3.0, 8.0]), ("incumbent", [2.0, 4.0, 9.0])):
        raw[1]["methods"][method]["output_bytes"] = 30 if method == "candidate" else 50
        raw[1]["methods"][method]["reps"] = [
            {
                "phase": "warmup",
                "order_index": 0,
                "time_s": 999.0,
                "encode_s": 0.0,
                "total_s": 999.0,
            }
        ] + [
            {
                "phase": "measured",
                "order_index": i + 1,
                "time_s": v + offset,
                "encode_s": 0.0,
                "total_s": v + offset,
            }
            for i, v in enumerate(values)
        ]
    row = BenchmarkRun(
        source_sha256="b" * 64,
        candidate_method="candidate",
        corpus=name,
        corpus_sha256=sha256([("a.txt", raw[1]["sha256"], 100)]),
        status="complete",
        raw_data=raw,
    )
    session.add(row)
    session.flush()
    return row


def test_reduction_and_uncertainty(store):
    from db.aggregation import reduce_runs, timing_statistics

    with store.sessions.begin() as session:
        rows = [measured_row(session), measured_row(session, "two", 1)]
        total = reduce_runs(rows)
        assert (total.raw_bytes, total.bytes, total.incumbent_bytes) == (200, 60, 100)
        assert (total.parse_seconds, total.incumbent_seconds) == (7.0, 9.0)
        assert total.ratio_pct == 30
        stats = timing_statistics(rows, draws=100)
        assert stats == timing_statistics(rows, draws=100)
        assert isinstance(stats["files"], list)
        assert stats["files"][0]["sample_std_s"] > 0
        assert isinstance(stats["intervals"], dict)
        assert (
            stats["intervals"]["compression_seconds"][0]
            <= 7
            <= stats["intervals"]["compression_seconds"][1]
        )
        prov = rows[1].raw_data[0]["benchmark_provenance"]
        assert isinstance(prov, dict)
        prov["host_sha256"] = "changed"
        with pytest.raises(ValueError, match="incompatible"):
            reduce_runs(rows)


def test_concurrent_aggregation_is_idempotent(store):
    from concurrent.futures import ThreadPoolExecutor

    from db.aggregation import aggregate

    with store.sessions.begin() as session:
        rid = measured_row(session).id

    def create(_):
        with store.sessions.begin() as session:
            return aggregate(session, [session.get(BenchmarkRun, rid)]).id

    with ThreadPoolExecutor(max_workers=2) as pool:
        ids = list(pool.map(create, range(2)))
    assert ids[0] == ids[1]


def test_publish_checks_verification_and_invalidation(store):
    from db.aggregation import aggregate, publish
    from db.models import Submission
    from verifier.identity import required_fingerprint

    with store.sessions.begin() as session:
        run = measured_row(session)
        result = aggregate(session, [run])
        sub = Submission(hotkey="miner", digest="f" * 64)
        session.add(sub)
        session.flush()
        with pytest.raises(ValueError, match="verification"):
            publish(session, sub.id, result.id)
        sub.source_sha256 = "b" * 64
        sub.proof_sha256 = "e" * 64
        sub.verifier_fingerprint = required_fingerprint()
        sub.static_verified_at = sub.lean_verified_at = datetime.now(timezone.utc)
        session.flush()
        publish(session, sub.id, result.id)
        assert sub.aggregation_id == result.id
        assert sub.parse_seconds == 3
        run.invalidated_at = datetime.now(timezone.utc)
        run.invalidation_reason = "host"
        session.flush()
        with pytest.raises(ValueError, match="invalidated"):
            publish(session, sub.id, result.id)


def test_old_verifier_stamp_keeps_published_scoring_evidence(store):
    from db.aggregation import aggregate, publish
    from db.models import Submission
    from verifier.identity import required_fingerprint

    with store.sessions.begin() as session:
        run = measured_row(session)
        result = aggregate(session, [run])
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
        sid = sub.id
    assert [p.submission_id for p in store.scoring.scoring_inputs()] == [sid]

    with store.sessions.begin() as session:
        session.get(Submission, sid).verifier_fingerprint = "0" * 64
    points = store.scoring.scoring_inputs()
    assert [p.submission_id for p in points] == [sid]
    assert points[0].verification_current is False


@pytest.mark.parametrize(
    "problem",
    ["source", "manifest", "incumbent", "failed", "invalidated", "nan", "missing-provenance"],
)
def test_invalid_evidence_cannot_be_aggregated(store, problem):
    from db.aggregation import reduce_runs

    with store.sessions.begin() as session:
        row = measured_row(session)
        if problem == "source":
            row.source_sha256 = "f" * 64
        elif problem == "manifest":
            row.corpus_sha256 = "f" * 64
        elif problem == "incumbent":
            methods = row.raw_data[0]["methods"]
            assert isinstance(methods, dict)
            del methods["incumbent"]
        elif problem == "failed":
            row.status = "failed"
        elif problem == "invalidated":
            row.invalidated_at = datetime.now(timezone.utc)
            row.invalidation_reason = "bad host"
        elif problem == "nan":
            methods = row.raw_data[1]["methods"]
            assert isinstance(methods, dict)
            methods["candidate"]["reps"][1]["time_s"] = float("nan")
        else:
            del row.raw_data[0]["benchmark_provenance"]
        with pytest.raises(ValueError):
            reduce_runs([row])
        session.rollback()


def test_balanced_compression_ratios(store):
    from copy import deepcopy

    from bench.storage import sha256
    from db.aggregation import compression_statistics, reduce_runs

    with store.sessions.begin() as session:
        one = measured_row(session)
        two = measured_row(session, "two")
        large = deepcopy(one.raw_data[1])
        large["file"] = "large.txt"
        large["sha256"] = "e" * 64
        large["raw_bytes"] = 10000
        methods = large["methods"]
        assert isinstance(methods, dict)
        methods["candidate"]["output_bytes"] = 9000
        methods["incumbent"]["output_bytes"] = 8000
        one.raw_data.append(large)
        methods = two.raw_data[1]["methods"]
        assert isinstance(methods, dict)
        methods["candidate"]["output_bytes"] = 10
        for row in (one, two):
            row.corpus_sha256 = sha256(
                sorted((f["file"], f["sha256"], f["raw_bytes"]) for f in row.raw_data[1:])
            )
        values = reduce_runs([one, two])
        # Corpus one: mean(30%, 90%) = 60%; corpus two: 10%.
        assert values.ratio_pct == pytest.approx(35)
        assert values.incumbent_ratio_pct == pytest.approx(57.5)
        assert values.byte_weighted_ratio_pct == pytest.approx(100 * 9040 / 10200)
        stats = compression_statistics([two, one])
        assert stats["ratio_pct"] == values.ratio_pct
        corpora = stats["corpora"]
        assert isinstance(corpora, list)
        assert [c["ratio_pct"] for c in corpora] == [60, 10]


def test_empty_files_excluded_from_ratio(store):
    from bench.storage import sha256
    from db.aggregation import reduce_runs

    with store.sessions.begin() as session:
        row = measured_row(session)
        row.raw_data[1]["raw_bytes"] = 0
        row.corpus_sha256 = sha256([("a.txt", "c" * 64, 0)])
        with pytest.raises(ValueError, match="nonempty files"):
            reduce_runs([row])


def test_recency_uses_balanced_ratio():
    from dataclasses import replace

    from db.scored import ScoredSubmission
    from scoring.improvement import improvement_events

    baseline = ScoredSubmission(
        submission_id=1,
        hotkey=None,
        bytes=10,
        raw_bytes=100,
        time_s=1,
        incumbent_bytes=50,
        incumbent_seconds=1,
        submitted_at=datetime(2026, 1, 1, tzinfo=timezone.utc),
        baseline_key="baseline",
        normalized_ratio_pct=40,
        normalized_incumbent_ratio_pct=50,
    )
    candidate = replace(
        baseline,
        submission_id=2,
        hotkey="miner",
        baseline_key=None,
        bytes=20,
        normalized_ratio_pct=30,
    )
    # More total bytes, but a better balanced ratio: it improves the record.
    events = improvement_events([baseline, candidate], 0.01)
    assert len(events) == 1
    assert events[0].relative_gain == pytest.approx(0.25)
    assert events[0].metric == "ratio_pct"
    assert candidate.ratio_pct == 30
    assert candidate.byte_weighted_ratio_pct == 20


@pytest.mark.parametrize("invalid", ["revoked", "source", "unverified", "context"])
def test_preview_recalculates_historical_evidence_without_publication(store, invalid):
    from sqlalchemy import func, select
    from sqlalchemy.orm.attributes import flag_modified

    from bench.storage import sha256
    from db.aggregation import CALCULATOR_VERSION, aggregate, publish
    from db.models import BenchmarkAggregation, Submission
    from verifier.identity import required_fingerprint

    with store.sessions.begin() as session:
        runs = [measured_row(session), measured_row(session, "two")]
        runs[1].raw_data[1]["raw_bytes"] = 1000
        flag_modified(runs[1], "raw_data")
        runs[1].corpus_sha256 = sha256([("a.txt", "d" * 64, 1000)])
        result = aggregate(session, runs)
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
        # Simulate a published pre-formula-change aggregation and its old verification.
        result.calculator_version = "compression-median-v3"
        assert result.context is not None
        result.context = {
            **{k: v for k, v in result.context.items() if k != "compression"},
            "calculator": "compression-median-v3",
        }
        sub.verifier_fingerprint = "0" * 64
        aid, sid, rid = result.id, sub.id, runs[0].id

    assert store.scoring.scoring_inputs() == []
    points = store.scoring.preview_inputs()
    assert len(points) == 1
    assert points[0].ratio_pct == pytest.approx((30 + 3) / 2)
    assert points[0].byte_weighted_ratio_pct == pytest.approx(100 * 60 / 1100)
    assert points[0].verification_current is False
    assert points[0].context["calculator"] == CALCULATOR_VERSION
    assert store.scoring.preview_inputs(aggregation_ids=[aid]) == points
    with store.sessions.begin() as session:
        # Preview neither rewrites historical results nor updates verification stamps.
        assert session.scalar(select(func.count()).select_from(BenchmarkAggregation)) == 1
        saved = session.get(BenchmarkAggregation, aid)
        sub = session.get(Submission, sid)
        assert saved.calculator_version == "compression-median-v3"
        assert sub.verifier_fingerprint == "0" * 64
        assert sub.aggregation_id == aid
        if invalid == "revoked":
            run = session.get(BenchmarkRun, rid)
            run.invalidated_at = datetime.now(timezone.utc)
            run.invalidation_reason = "unreliable measurement"
        elif invalid == "source":
            sub.source_sha256 = "a" * 64
        elif invalid == "unverified":
            sub.lean_verified_at = None
        else:
            saved.context = {**saved.context, "corpora": [["different", "c" * 64]]}
    assert store.scoring.preview_inputs() == []
    with pytest.raises(ValueError, match="requested aggregation"):
        store.scoring.preview_inputs(aggregation_ids=[aid])


def test_relative_timing_balances_files_and_corpora(store):
    from copy import deepcopy

    from bench.storage import sha256
    from db.aggregation import reduce_runs, timing_statistics

    with store.sessions.begin() as session:
        one = measured_row(session)
        two = measured_row(session, "two")
        large = deepcopy(one.raw_data[1])
        large["file"], large["sha256"], large["raw_bytes"] = "large", "e" * 64, 100000
        one.raw_data.append(large)
        # First corpus: file ratios 2 and 0.5. Second corpus: file ratio 3.
        for record, candidate, incumbent in (
            (one.raw_data[1], 2.0, 1.0),
            (large, 500.0, 1000.0),
            (two.raw_data[1], 30.0, 10.0),
        ):
            methods = record["methods"]
            assert isinstance(methods, dict)
            for name, time in (("candidate", candidate), ("incumbent", incumbent)):
                for rep in methods[name]["reps"]:
                    rep.update(time_s=time, encode_s=0.0, total_s=time)
        for row in (one, two):
            row.corpus_sha256 = sha256(
                sorted((f["file"], f["sha256"], f["raw_bytes"]) for f in row.raw_data[1:])
            )
        values = reduce_runs([one, two])
        assert values.balanced_time_ratio == pytest.approx(((2 + 0.5) / 2 + 3) / 2)
        assert values.compression_seconds == 532
        assert values.time_ratio == pytest.approx(532 / 1011)
        stats = timing_statistics([one, two], draws=100)
        intervals = stats["intervals"]
        assert isinstance(intervals, dict)
        assert intervals["balanced_time_ratio"] == pytest.approx([2.125, 2.125])


def test_relative_timing_rejects_zero_file_incumbent(store):
    from db.aggregation import reduce_runs

    with store.sessions.begin() as session:
        row = measured_row(session)
        methods = row.raw_data[1]["methods"]
        assert isinstance(methods, dict)
        for rep in methods["incumbent"]["reps"]:
            rep.update(time_s=0.0, encode_s=0.0, total_s=0.0)
        with pytest.raises(ValueError, match="positive"):
            reduce_runs([row])
