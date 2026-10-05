"""Immutable public evidence for a completed scoring pass, without raw samples or source."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Sequence
from datetime import datetime, timezone
from typing import cast

from sqlalchemy import select
from sqlalchemy.orm import Session

from .models import BenchmarkAggregation, Submission, SubmissionAdmissionCheck
from .scored import ScoredSubmission


def public_aggregation(row: BenchmarkAggregation | None) -> dict[str, object] | None:
    if row is None:
        return None
    stats = dict(row.statistics or {})
    # Only aggregate plotting data belongs in this view. Private file names don't.
    stats.pop("files", None)
    for key in ("relative_timing", "compression"):
        raw = stats.get(key)
        if isinstance(raw, dict):
            stats[key] = {k: v for k, v in cast(dict[str, object], raw).items() if k != "corpora"}
    return {
        "id": row.id,
        "statistics": stats,
        "context": row.context,
        "calculator_version": row.calculator_version,
        "raw_bytes": row.raw_bytes,
        "bytes": row.bytes,
        "parse_seconds": row.parse_seconds,
        "compression_seconds": row.compression_seconds,
        "source_sha256": row.source_sha256,
    }


def public_admission(detail: dict[str, object]) -> dict[str, object]:
    result = dict(detail)
    raw = result.get("statistics")
    if isinstance(raw, dict):
        stats = dict(cast(dict[str, object], raw))
        files = stats.pop("files", None)
        stats["file_count"] = len(cast(list[object], files)) if isinstance(files, list) else None
        result["statistics"] = stats
    return result


def build_snapshot(
    session: Session,
    points: Sequence[ScoredSubmission],
    policy: dict[str, object],
) -> dict[str, object]:
    by_id = {p.submission_id: p for p in points}
    items: list[dict[str, object]] = []
    rows = session.scalars(
        select(Submission)
        .where(Submission.hotkey.is_not(None) | Submission.baseline_active)
        .order_by(Submission.id)
    )
    corpora: set[str] = set()
    observed: list[list[object]] = []
    for row in rows:
        observed.append(
            [
                row.id,
                row.state,
                row.aggregation_id,
                row.admission_check_id,
                row.source_sha256,
                row.verifier_fingerprint,
                row.baseline_active,
            ]
        )
        point = by_id.get(row.id)
        aggregation = (
            session.get(BenchmarkAggregation, row.aggregation_id) if row.aggregation_id else None
        )
        decision = (
            public_admission(dict(point.admission or {}))
            if point
            else {"outcome": "pending", "reason_code": "awaiting-current-scoring-evidence"}
        )
        if point and point.context:
            pairs = cast(list[list[str]], point.context.get("corpora", []))
            corpora.update(pair[0] for pair in pairs)
        if point and point.admission_check_id:
            check = session.get(SubmissionAdmissionCheck, point.admission_check_id)
            if check:
                decision["created_at"] = check.created_at.isoformat()
        reference = cast(dict[str, object], decision.get("reference") or {})
        reference_id = reference.get("aggregation_id")
        reference_aggregation = (
            session.get(BenchmarkAggregation, reference_id)
            if isinstance(reference_id, int)
            else None
        )
        items.append(
            {
                "submission": {
                    "id": row.id,
                    "hotkey": row.hotkey,
                    "baseline_key": row.baseline_key,
                    "baseline_active": row.baseline_active,
                    "submitted_at": row.submitted_at.isoformat(),
                    "state": row.state,
                    "aggregation_id": row.aggregation_id,
                    # Do not expose a stale stored pointer as the decision used by the scorer.
                    "admission_check_id": point.admission_check_id if point else None,
                    "source_sha256": row.source_sha256,
                    "verifier_fingerprint": row.verifier_fingerprint,
                },
                "aggregation": public_aggregation(aggregation),
                "reference_aggregation": public_aggregation(reference_aggregation),
                "admission": decision,
                "scoring_input": point is not None,
            }
        )
    effective = {**policy, "required_corpora": sorted(corpora)}
    effective["admission_policy_version"] = policy["version"]
    effective["version"] = (
        "compression-policy-"
        + hashlib.sha256(
            json.dumps(
                [effective, sorted({json.dumps(p.context, sort_keys=True) for p in points})],
                sort_keys=True,
            ).encode()
        ).hexdigest()[:16]
    )
    return {
        "schema_version": 1,
        "computed_at": datetime.now(timezone.utc).isoformat(),
        "verifier_fingerprint": None,
        "observed_submissions": observed,
        "items": items,
        "policy": effective,
    }
