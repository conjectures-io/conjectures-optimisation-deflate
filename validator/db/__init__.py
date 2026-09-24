"""The validator's store: one Postgres database, one Store, four repositories.

    from db import connect
    store = connect()
    store.submissions.add(hotkey, digest)
    store.registrations.available_slots(hotkey)

`Store` owns the engine, so a process creates exactly one and hands it around; the
repositories are thin and hold nothing but the session factory.
"""

from __future__ import annotations

from typing import final

from sqlalchemy import Engine, literal, select

from .clock import iso, now
from .engine import create_db_engine, database_url, session_factory, session_scope
from .ratelimit import RateLimiter
from .registrations import NoSlot, RegistrationsDb
from .scoring import ScoredSubmission, ScoringDb
from .status import PENDING, TERMINAL, SubmissionState
from .submissions import SubmissionsDb
from .verification import VerificationDb

__all__ = [
    "NoSlot",
    "PENDING",
    "RateLimiter",
    "RegistrationsDb",
    "ScoredSubmission",
    "ScoringDb",
    "Store",
    "SubmissionState",
    "SubmissionsDb",
    "TERMINAL",
    "connect",
    "create_db_engine",
    "database_url",
    "iso",
    "now",
    "session_factory",
    "session_scope",
]

# Defaults for the write limiter; the service overrides them from its settings.
RATE_LIMIT = 10
RATE_WINDOW_SECONDS = 60


@final
class Store:
    def __init__(
        self,
        engine: Engine,
        *,
        rate_limit: int = RATE_LIMIT,
        rate_window_seconds: int = RATE_WINDOW_SECONDS,
    ) -> None:
        self.engine = engine
        self.sessions = session_factory(engine)
        self.submissions = SubmissionsDb(self.sessions)
        self.verification = VerificationDb(self.sessions)
        self.registrations = RegistrationsDb(self.sessions)
        self.scoring = ScoringDb(self.sessions)
        self.rate = RateLimiter(self.sessions, limit=rate_limit, window_seconds=rate_window_seconds)

    def ping(self) -> bool:
        # Is the database actually reachable? Used by /ready, which must fail when the
        # process is alive but cannot serve.
        with self.engine.connect() as conn:
            return conn.execute(select(literal(1))).scalar_one() == 1

    def close(self) -> None:
        self.engine.dispose()


def connect(
    url: str | None = None,
    *,
    echo: bool = False,
    rate_limit: int = RATE_LIMIT,
    rate_window_seconds: int = RATE_WINDOW_SECONDS,
) -> Store:
    # Open the store against `url`, or the environment-resolved default.
    return Store(
        create_db_engine(url, echo=echo),
        rate_limit=rate_limit,
        rate_window_seconds=rate_window_seconds,
    )
