"""The validator schema. These models are the source of truth; the Alembic revisions
under deploy/migrate/alembic/versions/ are the deploy path, and test_db_schema.py
fails if the two drift apart."""

from __future__ import annotations

import datetime as dt

from sqlalchemy import (
    BigInteger,
    Boolean,
    CheckConstraint,
    DateTime,
    Float,
    ForeignKey,
    Index,
    Integer,
    Text,
    UniqueConstraint,
    func,
)
from sqlalchemy.dialects.postgresql import JSONB
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column, relationship

from .status import STATE_VALUES


class Base(DeclarativeBase):
    pass


def _in_list(values: tuple[str, ...]) -> str:
    # Render a tuple of strings as a SQL IN list body: 'a', 'b', 'c'.
    return ", ".join(f"'{v}'" for v in values)


class Registration(Base):
    """One uid's hot/cold key assignment on the subnet, as of the block it registered at.

    A history, not a per-block dump: the chain watcher appends a row only when a uid's
    (hot, cold) pair differs from the last one recorded for it. Each row is therefore one
    real registration event -- and one submission slot (see EntitlementClaim).
    """

    __tablename__ = "registrations"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    uid: Mapped[int] = mapped_column(Integer, nullable=False)
    ss58_hot: Mapped[str] = mapped_column(Text, nullable=False)
    ss58_cold: Mapped[str] = mapped_column(Text, nullable=False)
    # The block this uid *registered* at (its on-chain BlockAtRegistration), never the
    # block the watcher happened to observe it from -- so the row stays correct across
    # watcher downtime and the initial backfill.
    block: Mapped[int] = mapped_column(BigInteger, nullable=False)
    # On-chain wall-clock time (UTC) of `block`: when the registration became true.
    block_date: Mapped[dt.datetime] = mapped_column(DateTime(timezone=True), nullable=False)
    # When the watcher wrote the row, stamped by the database. Distinguishes "true
    # on-chain at" from "observed and stored at".
    inserted_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )

    claim: Mapped[EntitlementClaim | None] = relationship(back_populates="registration")

    __table_args__ = (
        UniqueConstraint("uid", "block", name="uq_registrations_uid_block"),
        Index("ix_registrations_uid", "uid"),
        Index("ix_registrations_ss58_hot", "ss58_hot"),
    )


class Submission(Base):
    """One signed upload of parse.rs + Parse.lean, and what the gate made of it."""

    __tablename__ = "submissions"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    hotkey: Mapped[str] = mapped_column(Text, nullable=False)
    # sha256(parse.rs || Parse.lean), hex -- what the miner signed, and the submission's
    # identity. The same files from the same hotkey are the same submission.
    digest: Mapped[str] = mapped_column(Text, nullable=False)
    submitted_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )
    state: Mapped[str] = mapped_column(Text, nullable=False, server_default="queued")
    exit_code: Mapped[int | None] = mapped_column(Integer)
    # The gate's full stdout: the stage report a miner reads to find out what failed.
    report: Mapped[str | None] = mapped_column(Text)

    # --- the score, as the harness measured it -------------------------------
    # Uncompressed corpus size. Needed for the Pareto frontier's ratio axis, which is
    # bytes as a percentage of raw; without it a submission cannot be scored.
    raw_bytes: Mapped[int | None] = mapped_column(BigInteger)
    incumbent_bytes: Mapped[int | None] = mapped_column(BigInteger)
    bytes: Mapped[int | None] = mapped_column(BigInteger)
    # Absolute parse seconds for both sides; time_ratio is their quotient, kept because
    # it is what the speed floor is enforced on and what miners are shown.
    incumbent_seconds: Mapped[float | None] = mapped_column(Float)
    parse_seconds: Mapped[float | None] = mapped_column(Float)
    time_ratio: Mapped[float | None] = mapped_column(Float)

    # --- queue bookkeeping ---------------------------------------------------
    # Which gate worker holds it, and when it was claimed, started and finished. A row
    # whose claim is older than the gate's own timeout is stale and gets requeued.
    worker_id: Mapped[str | None] = mapped_column(Text)
    claimed_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))
    finished_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))

    claim: Mapped[EntitlementClaim | None] = relationship(back_populates="submission")

    __table_args__ = (
        UniqueConstraint("hotkey", "digest", name="uq_submissions_hotkey_digest"),
        CheckConstraint(f"state IN ({_in_list(STATE_VALUES)})", name="ck_submissions_state"),
        Index("ix_submissions_hotkey", "hotkey"),
        # The queue scan: oldest queued first, arrival order.
        Index("ix_submissions_state_submitted_at", "state", "submitted_at", "id"),
    )


class EntitlementClaim(Base):
    """One registration spent on one accepted submission.

    This table *is* the "one registration buys one submission" rule. registration_id is
    the primary key, so a registration can be spent at most once; submission_id is
    unique, so a submission spends at most one. The invariant belongs to the database,
    not to application arithmetic: two accepts racing for the same last slot end in a
    unique violation, not in two payouts.
    """

    __tablename__ = "entitlement_claims"

    registration_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("registrations.id", ondelete="CASCADE"), primary_key=True
    )
    submission_id: Mapped[int] = mapped_column(
        BigInteger,
        ForeignKey("submissions.id", ondelete="CASCADE"),
        nullable=False,
        unique=True,
    )
    claimed_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )

    registration: Mapped[Registration] = relationship(back_populates="claim")
    submission: Mapped[Submission] = relationship(back_populates="claim")


class WeightSet(Base):
    """Every set_weights attempt, accepted or not -- so a disputed epoch stays
    reconstructable from the validator's own records."""

    __tablename__ = "weight_sets"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    netuid: Mapped[int] = mapped_column(Integer, nullable=False)
    block: Mapped[int] = mapped_column(BigInteger, nullable=False)
    # The vector as submitted, uid-aligned. JSONB rather than two arrays so the pair can
    # never come apart, and so a reader needs no join to see what was set.
    uids: Mapped[list[int]] = mapped_column(JSONB, nullable=False)
    weights: Mapped[list[float]] = mapped_column(JSONB, nullable=False)
    summary: Mapped[str | None] = mapped_column(Text)
    accepted: Mapped[bool] = mapped_column(Boolean, nullable=False)
    # Set when the chain refused the vector, or when the worker skipped submitting it.
    error: Mapped[str | None] = mapped_column(Text)
    # True when the worker computed the vector but deliberately did not submit it.
    dry_run: Mapped[bool] = mapped_column(Boolean, nullable=False, server_default="false")
    created_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )

    __table_args__ = (Index("ix_weight_sets_created_at", "created_at"),)


class ScoreSnapshot(Base):
    """One hotkey's scoring inputs and outputs for one weight_sets row.

    Written alongside the vector it explains, so "why did this hotkey get this weight"
    is answerable months later without re-running the scorer against data that has
    since moved.
    """

    __tablename__ = "score_snapshots"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    weight_set_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("weight_sets.id", ondelete="CASCADE"), nullable=False
    )
    hotkey: Mapped[str] = mapped_column(Text, nullable=False)
    # The submission the hotkey was scored on (their best accepted at the time).
    submission_id: Mapped[int | None] = mapped_column(
        BigInteger, ForeignKey("submissions.id", ondelete="SET NULL")
    )
    # The point as the scorer saw it; kept because the frontier is computed from these
    # two numbers and nothing else.
    time_s: Mapped[float | None] = mapped_column(Float)
    ratio_pct: Mapped[float | None] = mapped_column(Float)
    on_frontier: Mapped[bool] = mapped_column(Boolean, nullable=False, server_default="false")
    # The two components and their sum, each already scaled by its share of emission.
    pareto_weight: Mapped[float] = mapped_column(Float, nullable=False, server_default="0")
    improvement_weight: Mapped[float] = mapped_column(Float, nullable=False, server_default="0")
    combined_weight: Mapped[float] = mapped_column(Float, nullable=False, server_default="0")

    __table_args__ = (
        Index("ix_score_snapshots_weight_set_id", "weight_set_id"),
        Index("ix_score_snapshots_hotkey", "hotkey"),
    )


class RateLimitWindow(Base):
    """A fixed-window write counter per subject (a hotkey, or an IP for unsigned reads).

    In Postgres rather than in process memory so the limit holds across every API worker
    and survives a restart -- an in-memory counter is a limit per process per uptime,
    which is no limit at all behind more than one worker.
    """

    __tablename__ = "rate_limit_windows"

    subject: Mapped[str] = mapped_column(Text, primary_key=True)
    # Start of the window this counter covers, truncated to the window length.
    window_start: Mapped[dt.datetime] = mapped_column(DateTime(timezone=True), primary_key=True)
    hits: Mapped[int] = mapped_column(Integer, nullable=False, server_default="0")

    __table_args__ = (Index("ix_rate_limit_windows_window_start", "window_start"),)
