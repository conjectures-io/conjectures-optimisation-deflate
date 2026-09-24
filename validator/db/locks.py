"""Advisory lock keys shared across writers that must serialize against each other.

Pulled out of admission.py so aggregation.py's publish() (which must hold the same
lock as admission's publication step) does not need to import admission.py itself --
admission.py already imports admission_statistics.py, which imports aggregation.py, so
that edge would otherwise be a real cycle.
"""

from __future__ import annotations

from sqlalchemy import text
from sqlalchemy.orm import Session

PUBLICATION_LOCK_KEY = 771002001


def publication_lock(session: Session) -> None:
    session.execute(text("SELECT pg_advisory_xact_lock(:key)"), {"key": PUBLICATION_LOCK_KEY})
