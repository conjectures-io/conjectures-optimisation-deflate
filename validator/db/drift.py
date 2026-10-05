"""Completed gate audit and one warning per observed-state transition."""

from __future__ import annotations

import hashlib
import json
from collections.abc import Mapping
from typing import cast, final

from loguru import logger
from sqlalchemy import select, text
from sqlalchemy.orm import Session, sessionmaker

import db.clock as clock

from .engine import session_scope
from .models import GateResult, ObservedState, Submission


def _digest(details: Mapping[str, object]) -> str:
    return hashlib.sha256(json.dumps(details, sort_keys=True).encode()).hexdigest()


def _changed_paths(
    old: Mapping[str, object], new: Mapping[str, object], prefix: str = ""
) -> list[str]:
    changed: list[str] = []
    for name in sorted(old.keys() | new.keys()):
        path = f"{prefix}.{name}" if prefix else name
        before, after = old.get(name), new.get(name)
        if before == after:
            continue
        if isinstance(before, dict) and isinstance(after, dict):
            changed.extend(
                _changed_paths(
                    cast(dict[str, object], before), cast(dict[str, object], after), path
                )
            )
        else:
            changed.append(path)
    return changed


@final
class DriftDb:
    def __init__(self, sessions: sessionmaker[Session]) -> None:
        self._sessions = sessions

    def finished_gate(
        self,
        submission_id: int,
        attempt_token: str,
        stage: str,
        exit_code: int,
        observed: dict[str, object],
    ) -> None:
        """No row is made until a gate invocation has an ordinary final verdict."""
        with session_scope(self._sessions) as session:
            submission = session.get(Submission, submission_id, with_for_update=True)
            if submission is None or submission.verification_attempt != attempt_token:
                return  # A superseded worker may not record an outcome for the new claim.
            existing = session.scalar(
                select(GateResult.id).where(
                    GateResult.submission_id == submission_id,
                    GateResult.attempt_token == attempt_token,
                    GateResult.stage == stage,
                )
            )
            if existing is None:
                session.add(
                    GateResult(
                        submission_id=submission_id,
                        attempt_token=attempt_token,
                        stage=stage,
                        exit_code=exit_code,
                        observed=observed,
                    )
                )

    def observe(self, key: str, details: Mapping[str, object]) -> None:
        """Persist the last seen value so ordinary restarts do not repeat a warning."""
        digest = _digest(details)
        previous: dict[str, object] | None = None
        first_drift = False
        with session_scope(self._sessions) as session:
            lock = int(hashlib.sha256(key.encode()).hexdigest()[:15], 16)
            session.execute(text("SELECT pg_advisory_xact_lock(:key)"), {"key": lock})
            row = session.get(ObservedState, key, with_for_update=True)
            if row is None:
                session.add(ObservedState(key=key, digest=digest, details=dict(details)))
                first_drift = key == "verifier" and bool(details.get("pin_drift"))
            elif row.digest != digest:
                previous = row.details
                row.digest = digest
                row.details = dict(details)
                row.observed_at = clock.now()
        if previous is not None:
            changed = _changed_paths(previous, details)
            logger.warning(
                "[drift] {} changed: {}; old={} new={}",
                key,
                ", ".join(changed),
                _digest(previous),
                digest,
            )
        elif first_drift:
            changed = details.get("pin_drift")
            paths = cast(list[object], changed) if isinstance(changed, list) else []
            logger.warning(
                "[drift] initial verifier checkout differs from PINS.json: {}",
                ", ".join(str(item) for item in paths),
            )
