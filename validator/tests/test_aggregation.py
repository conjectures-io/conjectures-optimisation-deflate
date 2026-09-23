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
        result["reps"].append({"phase": "measured", "order_index": 2, "time_s": 0.3})
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
            {"phase": "warmup", "order_index": 0, "time_s": 999.0}
        ] + [
            {"phase": "measured", "order_index": i + 1, "time_s": v + offset}
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
        assert stats["intervals"]["parse_seconds"][0] <= 7 <= stats["intervals"]["parse_seconds"][1]
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
