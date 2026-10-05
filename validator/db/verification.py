"""Trusted milestone writer with attempt-token compare-and-swap protection."""

from __future__ import annotations

import datetime as dt
import hashlib
import uuid
from typing import final

from sqlalchemy.orm import Session, sessionmaker

import db.clock as clock
import db.models as models

from .engine import session_scope


class StaleAttempt(RuntimeError):
    pass


@final
class VerificationDb:
    def __init__(self, sessions: sessionmaker[Session]):
        self.sessions = sessions

    def begin(
        self,
        sub_id: int,
        source: bytes,
        proof: bytes,
        fingerprint: str,
        *,
        lean_only: bool = False,
        reuse: bool = False,
        expected_claim: dt.datetime | None = None,
        expected_attempt: str | None = None,
    ) -> tuple[str, bool]:
        del fingerprint  # Historical API argument; identity no longer controls reuse.
        source_hash = hashlib.sha256(source).hexdigest()
        proof_hash = hashlib.sha256(proof).hexdigest()
        digest = hashlib.sha256(source + proof).hexdigest()
        with session_scope(self.sessions) as session:
            row = session.get(models.Submission, sub_id, with_for_update=True)
            if row is None or row.digest != digest:
                raise ValueError("stored submission content does not match its signed digest")
            if expected_claim is not None and row.claimed_at != expected_claim:
                raise StaleAttempt("worker claim was superseded before verification started")
            if expected_attempt is not None and row.verification_attempt != expected_attempt:
                raise StaleAttempt("queue claim token was superseded")
            same = row.source_sha256 == source_hash and row.proof_sha256 == proof_hash
            if lean_only and not (same and row.static_verified_at is not None):
                raise ValueError("matching successful static prevalidation is required")
            cached = reuse and same and row.lean_verified_at is not None
            token = expected_attempt or uuid.uuid4().hex
            row.verification_attempt = token
            row.source_sha256 = source_hash
            row.proof_sha256 = proof_hash
            # Keep a completed result until its replacement finishes. In particular,
            # a hotfix must not erase verification or an existing published score.
            return token, cached

    def publish(
        self, sub_id: int, token: str, milestone: str, fingerprint: str | None = None
    ) -> None:
        if milestone not in ("static", "lean", "full", "measured"):
            raise ValueError("unknown verification milestone")
        with session_scope(self.sessions) as session:
            row = session.get(models.Submission, sub_id, with_for_update=True)
            if row is None or row.verification_attempt != token:
                raise StaleAttempt("verification attempt has been superseded")
            if milestone == "static":
                row.static_verified_at = clock.now()
            elif milestone == "lean":
                if row.static_verified_at is None:
                    raise ValueError("Lean success requires static success")
                row.lean_verified_at = clock.now()
            elif milestone == "full":
                completed = clock.now()
                row.static_verified_at = completed
                row.lean_verified_at = completed
            else:
                if row.lean_verified_at is None:
                    raise ValueError("official measurements require Lean success")
                row.measured_source_sha256 = row.source_sha256
            if fingerprint is None and milestone in ("static", "lean", "full"):
                # Retain the API used by standalone static/Lean commands. The value
                # is read only when that stage has actually completed.
                from verifier.identity import fingerprint as current_fingerprint

                fingerprint = current_fingerprint()
            if fingerprint is not None:
                row.verifier_fingerprint = fingerprint
