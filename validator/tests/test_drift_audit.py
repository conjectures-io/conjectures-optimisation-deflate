"""Completed audit results and drift warnings survive worker restarts."""

from __future__ import annotations

import hashlib

from loguru import logger
from sqlalchemy import select

from db.drift import DriftDb
from db.models import GateResult, ObservedState


def test_only_finished_gate_attempts_have_audit_rows(store):
    source, proof = b"source", b"proof"
    sid, _ = store.submissions.add("drift-test", hashlib.sha256(source + proof).hexdigest())
    claimed = store.submissions.claim_next("gate-a")
    assert claimed is not None and claimed.id == sid
    with store.sessions.begin() as session:
        assert list(session.scalars(select(GateResult))) == []

    observed = {"files": {"verifier/verify.py": "a" * 64}}
    assert claimed.verification_attempt is not None
    store.drift.finished_gate(sid, claimed.verification_attempt, "full", 0, observed)
    with store.sessions.begin() as session:
        rows = list(session.scalars(select(GateResult)))
        assert len(rows) == 1
        assert rows[0].observed == observed

    store.submissions.requeue_interrupted("gate-a")
    store.drift.finished_gate(sid, claimed.verification_attempt, "full", 1, observed)
    with store.sessions.begin() as session:
        assert len(list(session.scalars(select(GateResult)))) == 1


def test_drift_warning_is_once_per_transition_across_restarts(store):
    warnings: list[str] = []
    sink = logger.add(lambda message: warnings.append(str(message)), level="WARNING")
    first = {"corpora": {"stage1": {"corpus_sha256": "a" * 64}}, "host": "host-a"}
    second = {"corpora": {"stage1": {"corpus_sha256": "b" * 64}}, "host": "host-a"}
    try:
        store.drift.observe("benchmark", first)
        store.drift.observe("benchmark", first)
        assert warnings == []
        restarted = DriftDb(store.sessions)
        restarted.observe("benchmark", second)
        restarted.observe("benchmark", second)
        assert len(warnings) == 1
        assert "corpora.stage1.corpus_sha256" in warnings[0]
        with store.sessions.begin() as session:
            assert session.get(ObservedState, "benchmark").details == second
            assert session.get(ObservedState, "benchmark").observed_at is not None
        restarted.observe("benchmark", first)
        assert len(warnings) == 2
    finally:
        logger.remove(sink)
