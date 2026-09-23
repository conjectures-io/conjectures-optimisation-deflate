"""Admission publication, explicit replay and read-only historical previews.

The identity includes the complete ordered prefix, not just the selected neighbor.
A changed prefix cannot silently reuse later decisions. Ordinary scoring only reads
matching current pointers; only explicit replay may rewrite an existing context.
"""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

from sqlalchemy import select, text

from bench.storage import sha256
from scoring.admission import (
    ADMITTED,
    BASELINE_ORDER,
    BASELINE_ORDER_VERSION,
    POLICY_VERSION,
    advance,
    ordered_candidates,
    select_reference,
)

from .admission_statistics import compare, evidence_files
from .models import (
    BenchmarkAggregation,
    BenchmarkAggregationInput,
    BenchmarkRun,
    Submission,
    SubmissionAdmissionCheck,
)

if TYPE_CHECKING:
    from .scoring import ScoredSubmission, ScoringDb


LOCK_KEY = 771002001


def publication_lock(session):
    session.execute(text("SELECT pg_advisory_xact_lock(:key)"), {"key": LOCK_KEY})


def runs_for(session, aggregation_id):
    return list(
        session.scalars(
            select(BenchmarkRun)
            .join(
                BenchmarkAggregationInput,
                BenchmarkAggregationInput.run_id == BenchmarkRun.id,
            )
            .where(BenchmarkAggregationInput.aggregation_id == aggregation_id)
            .order_by(BenchmarkRun.id)
        )
    )


def point_payload(point):
    return {
        "submission_id": point.submission_id,
        "aggregation_id": point.aggregation_id,
        "label": point.baseline_key or point.hotkey or str(point.submission_id),
        "time_ratio": point.pareto_time,
        "compression_pct": point.ratio_pct,
        "admission_check_id": point.admission_check_id,
    }


def evaluate(session, points, *, compute=False, persist=False, replay=False):
    """Evaluate an ordered context. Callers hold publication_lock before persisted reads.

    compute=True is a preview or initial publication. An existing pointer in a
    different context requires replay=True. Reading never runs new comparisons.
    """
    if persist and not compute:
        raise ValueError("publication requires computation")
    ordered = ordered_candidates(points)
    frontier, result, prefix = [], [], []
    names = {p.baseline_key for p in ordered if p.baseline_key}
    baseline_context = (
        bool(names)
        or session.scalar(select(Submission.id).where(Submission.baseline_active).limit(1))
        is not None
    )
    missing = next(
        (i for i, name in enumerate(BASELINE_ORDER) if name not in names), len(BASELINE_ORDER)
    )
    blocked = False
    for point in ordered:
        sub = session.get(Submission, point.submission_id)
        if sub is None:
            raise ValueError("submission missing")
        awaiting_baseline = (
            baseline_context
            and (point.baseline_key is None or BASELINE_ORDER.index(point.baseline_key) > missing)
            and missing < len(BASELINE_ORDER)
        )
        if awaiting_baseline or blocked:
            detail = {
                "outcome": "pending",
                "reason_code": "awaiting-predecessor",
                "candidate": point_payload(point),
                "preview": compute and not persist,
            }
            result.append(replace(point, admission=detail))
            if persist:
                sub.admission_check_id = None
            continue
        runs = runs_for(session, point.aggregation_id)
        if not runs or any(r.status != "complete" or r.invalidated_at is not None for r in runs):
            detail = {
                "outcome": "invalid_evidence",
                "reason_code": "evaluation-error",
                "error": "missing, failed or invalidated benchmark evidence",
                "candidate": point_payload(point),
                "preview": compute and not persist,
            }
            result.append(replace(point, admission=detail))
            blocked = True
            if persist:
                sub.admission_check_id = None
            continue
        # Raw hashes make evidence edits invalidate a pointer even if summary numbers match.
        evidence = [[r.id, sha256(r.raw_data)] for r in runs]
        identity = [
            POLICY_VERSION,
            BASELINE_ORDER_VERSION,
            point.context,
            point.submission_id,
            point.aggregation_id,
            evidence,
            prefix,
        ]
        key = sha256(identity)
        current = (
            session.get(SubmissionAdmissionCheck, sub.admission_check_id)
            if sub.admission_check_id
            else None
        )
        check = current if current is not None and current.decision_key == key else None
        has_history = (
            current is not None
            or session.scalar(
                select(SubmissionAdmissionCheck.id)
                .where(SubmissionAdmissionCheck.submission_id == point.submission_id)
                .limit(1)
            )
            is not None
        )
        if check is None and (not compute or (has_history and not replay)):
            detail = {
                "outcome": "pending",
                "reason_code": "explicit-replay-required",
                "candidate": point_payload(point),
                "preview": compute and not persist,
            }
            result.append(replace(point, admission=detail))
            blocked = True
            continue
        if check is None:
            check = session.scalar(
                select(SubmissionAdmissionCheck).where(
                    SubmissionAdmissionCheck.decision_key == key,
                )
            )
        if check is not None:
            detail = dict(check.details)
        else:
            try:
                # Validate minimum repetitions even for first/record-compression points.
                evidence_files(runs)
                outcome, reference = select_reference(frontier, point)
                stats = (
                    compare(runs, runs_for(session, reference.aggregation_id))
                    if reference
                    else None
                )
            except ValueError as exc:
                detail = {
                    "outcome": "invalid_evidence",
                    "reason_code": "evaluation-error",
                    "error": str(exc),
                    "candidate": point_payload(point),
                    "preview": compute and not persist,
                }
                result.append(replace(point, admission=detail))
                blocked = True
                if persist:
                    sub.admission_check_id = None
                continue
            if stats is not None:
                outcome = stats["outcome"]
            reason = {
                "passed": "speed-advantage-established",
                "inconclusive": "speed-advantage-uncertain",
                "not_required": "no-slower-better-compressing-neighbor",
                "dominated": "dominated-or-duplicate",
            }[outcome]
            detail = {
                "schema_version": 1,
                "outcome": outcome,
                "reason_code": reason,
                "policy_version": POLICY_VERSION,
                "baseline_order_version": BASELINE_ORDER_VERSION,
                "candidate": point_payload(point),
                "reference": point_payload(reference) if reference else None,
                "frontier_before": [point_payload(p) for p in frontier],
                "prefix": list(prefix),
                "evaluation_context": point.context,
                "evidence": evidence,
                "statistics": stats,
                "historical_verification": point.verification_current is False,
            }
            if persist:
                check = SubmissionAdmissionCheck(
                    submission_id=point.submission_id,
                    candidate_aggregation_id=point.aggregation_id,
                    reference_aggregation_id=reference.aggregation_id if reference else None,
                    decision_key=key,
                    policy_version=POLICY_VERSION,
                    outcome=outcome,
                    reason_code=reason,
                    details=detail,
                )
                session.add(check)
                session.flush()
        if persist:
            sub.admission_check_id = check.id
        updated = replace(
            point,
            admission_check_id=check.id if check else None,
            admission={**detail, "preview": compute and not persist, "decision_key": key},
        )
        result.append(updated)
        prefix.append(key)
        frontier = advance(frontier, updated, detail["outcome"])
    return result


def run(
    scoring_db: ScoringDb, *, persist=False, replay=False, historical=False
) -> list[ScoredSubmission]:
    """Publish under one lock/transaction, or compute a read-only snapshot preview."""
    with scoring_db._sessions.begin() as session:
        if persist:
            publication_lock(session)
            # Protect evidence and pointers against concurrent updates during publication.
            for model in (Submission, BenchmarkAggregation, BenchmarkRun):
                list(session.scalars(select(model).order_by(model.id).with_for_update()))
        points = scoring_db._inputs(None, None, preview=historical, session=session)
        return evaluate(session, points, compute=True, persist=persist, replay=replay)


def admitted(point):
    # Pure legacy callers have no persisted evidence; production DB rows always get a status.
    if point.admission is None:
        return point.aggregation_id is None
    return point.admission.get("outcome") in ADMITTED
