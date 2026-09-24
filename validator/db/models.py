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
    ForeignKeyConstraint,
    Index,
    Integer,
    Text,
    UniqueConstraint,
    func,
    text,
)
from sqlalchemy.dialects.postgresql import JSONB
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column, relationship
from sqlalchemy.sql.schema import SchemaItem

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

    __tablename__: str = "registrations"

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

    __table_args__: tuple[SchemaItem, ...] = (
        UniqueConstraint("uid", "block", name="uq_registrations_uid_block"),
        Index("ix_registrations_uid", "uid"),
        Index("ix_registrations_ss58_hot", "ss58_hot"),
    )


class Submission(Base):
    """One signed upload of parse.rs + Parse.lean, and what the gate made of it."""

    __tablename__: str = "submissions"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    aggregation_id: Mapped[int | None] = mapped_column(
        BigInteger,
        ForeignKey(
            "benchmark_aggregations.id", ondelete="RESTRICT", name="fk_submission_aggregation"
        ),
    )
    admission_check_id: Mapped[int | None] = mapped_column(
        BigInteger,
        ForeignKey(
            "submission_admission_checks.id",
            ondelete="RESTRICT",
            name="fk_submission_admission",
            use_alter=True,
        ),
    )
    hotkey: Mapped[str | None] = mapped_column(Text, nullable=True)
    baseline_key: Mapped[str | None] = mapped_column(Text)
    baseline_active: Mapped[bool] = mapped_column(Boolean, nullable=False, server_default="false")
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

    source_sha256: Mapped[str | None] = mapped_column(Text)
    proof_sha256: Mapped[str | None] = mapped_column(Text)
    verifier_fingerprint: Mapped[str | None] = mapped_column(Text)
    verification_attempt: Mapped[str | None] = mapped_column(Text)
    static_verified_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))
    lean_verified_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))
    # Only the trusted gate can bind its measurements to a verification identity.
    measured_source_sha256: Mapped[str | None] = mapped_column(Text)

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
    compression_seconds: Mapped[float | None] = mapped_column(Float)
    time_ratio: Mapped[float | None] = mapped_column(Float)

    # --- queue bookkeeping ---------------------------------------------------
    # Which gate worker holds it, and when it was claimed, started and finished. A row
    # whose claim is older than the gate's own timeout is stale and gets requeued.
    worker_id: Mapped[str | None] = mapped_column(Text)
    claimed_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))
    finished_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))

    claim: Mapped[EntitlementClaim | None] = relationship(back_populates="submission")

    __table_args__: tuple[SchemaItem, ...] = (
        UniqueConstraint("hotkey", "digest", name="uq_submissions_hotkey_digest"),
        UniqueConstraint("baseline_key", "digest", name="uq_submission_baseline_digest"),
        CheckConstraint("hotkey IS NULL OR baseline_key IS NULL", name="ck_submission_owner"),
        CheckConstraint(
            "NOT baseline_active OR baseline_key IS NOT NULL", name="ck_submission_baseline_active"
        ),
        Index(
            "uq_active_baseline",
            "baseline_key",
            unique=True,
            postgresql_where=text("baseline_active"),
        ),
        CheckConstraint(
            "lean_verified_at IS NULL OR static_verified_at IS NOT NULL",
            name="ck_submission_lean_requires_static",
        ),
        CheckConstraint(
            "static_verified_at IS NULL OR (source_sha256 IS NOT NULL AND "
            "proof_sha256 IS NOT NULL AND verifier_fingerprint IS NOT NULL)",
            name="ck_submission_verification_identity",
        ),
        *[
            CheckConstraint(
                f"{name} IS NULL OR {name} ~ '^[0-9a-f]{{64}}$'", name=f"ck_submission_{name}"
            )
            for name in (
                "source_sha256",
                "proof_sha256",
                "verifier_fingerprint",
                "measured_source_sha256",
            )
        ],
        Index("ix_submissions_source_sha256", "source_sha256"),
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

    __tablename__: str = "entitlement_claims"

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

    __tablename__: str = "weight_sets"

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

    __table_args__: tuple[SchemaItem, ...] = (Index("ix_weight_sets_created_at", "created_at"),)


class ScoreSnapshot(Base):
    """One hotkey's scoring inputs and outputs for one weight_sets row.

    Written alongside the vector it explains, so "why did this hotkey get this weight"
    is answerable months later without re-running the scorer against data that has
    since moved.
    """

    __tablename__: str = "score_snapshots"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    weight_set_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("weight_sets.id", ondelete="CASCADE"), nullable=False
    )
    aggregation_id: Mapped[int | None] = mapped_column(
        BigInteger,
        ForeignKey(
            "benchmark_aggregations.id", ondelete="RESTRICT", name="fk_scoresnapshot_aggregation"
        ),
    )
    admission_check_id: Mapped[int | None] = mapped_column(
        BigInteger,
        ForeignKey("submission_admission_checks.id", ondelete="RESTRICT"),
    )
    hotkey: Mapped[str | None] = mapped_column(Text, nullable=True)
    baseline_key: Mapped[str | None] = mapped_column(Text)
    burn_reason: Mapped[str | None] = mapped_column(Text)
    payable_weight: Mapped[float] = mapped_column(Float, nullable=False, server_default="0")
    # Point identity independent of payout ownership.
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

    __table_args__: tuple[SchemaItem, ...] = (
        Index("ix_score_snapshots_weight_set_id", "weight_set_id"),
        Index("ix_score_snapshots_hotkey", "hotkey"),
    )


class RateLimitWindow(Base):
    """A fixed-window write counter per subject (a hotkey, or an IP for unsigned reads).

    In Postgres rather than in process memory so the limit holds across every API worker
    and survives a restart -- an in-memory counter is a limit per process per uptime,
    which is no limit at all behind more than one worker.
    """

    __tablename__: str = "rate_limit_windows"

    subject: Mapped[str] = mapped_column(Text, primary_key=True)
    # Start of the window this counter covers, truncated to the window length.
    window_start: Mapped[dt.datetime] = mapped_column(DateTime(timezone=True), primary_key=True)
    hits: Mapped[int] = mapped_column(Integer, nullable=False, server_default="0")

    __table_args__: tuple[SchemaItem, ...] = (
        Index("ix_rate_limit_windows_window_start", "window_start"),
    )


class BenchmarkRun(Base):
    """One candidate on one corpus, with its paired incumbent and references.

    raw_data is the original JSONL evidence. Compression results and speed samples
    are its SQL projections; writers must insert all three atomically.
    """

    __tablename__: str = "benchmark_runs"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    run_key: Mapped[str | None] = mapped_column(Text)
    source_sha256: Mapped[str] = mapped_column(Text, nullable=False)
    candidate_method: Mapped[str] = mapped_column(Text, nullable=False)
    corpus: Mapped[str] = mapped_column(Text, nullable=False)
    corpus_sha256: Mapped[str] = mapped_column(Text, nullable=False)
    status: Mapped[str] = mapped_column(Text, nullable=False)
    created_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )
    started_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))
    finished_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))
    invalidated_at: Mapped[dt.datetime | None] = mapped_column(DateTime(timezone=True))
    invalidation_reason: Mapped[str | None] = mapped_column(Text)
    raw_data: Mapped[list[dict[str, object]]] = mapped_column(JSONB, nullable=False)

    __table_args__: tuple[SchemaItem, ...] = (
        UniqueConstraint("run_key", name="uq_benchmark_runs_run_key"),
        CheckConstraint("source_sha256 ~ '^[0-9a-f]{64}$'", name="ck_benchmark_runs_source"),
        CheckConstraint("corpus_sha256 ~ '^[0-9a-f]{64}$'", name="ck_benchmark_runs_corpus"),
        CheckConstraint("status IN ('complete', 'failed')", name="ck_benchmark_runs_status"),
        CheckConstraint("jsonb_typeof(raw_data) = 'array'", name="ck_benchmark_runs_raw"),
        CheckConstraint(
            "(invalidated_at IS NULL) = (invalidation_reason IS NULL)",
            name="ck_benchmark_runs_invalidation",
        ),
        Index("ix_benchmark_runs_lookup", "source_sha256", "corpus_sha256", "created_at", "id"),
    )


class BenchmarkCompressionResult(Base):
    """One method's compression result on one input file, independent of timing reps."""

    __tablename__: str = "benchmark_compression_results"

    run_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("benchmark_runs.id", ondelete="CASCADE"), primary_key=True
    )
    file_index: Mapped[int] = mapped_column(Integer, primary_key=True)
    method: Mapped[str] = mapped_column(Text, primary_key=True)
    file_path: Mapped[str] = mapped_column(Text, nullable=False)
    file_sha256: Mapped[str] = mapped_column(Text, nullable=False)
    raw_bytes: Mapped[int] = mapped_column(BigInteger, nullable=False)
    output_bytes: Mapped[int | None] = mapped_column(BigInteger)
    output_sha256: Mapped[str | None] = mapped_column(Text)
    tokens_sha256: Mapped[str | None] = mapped_column(Text)
    # None means no repeated token comparison was available (e.g. external references).
    tokens_deterministic: Mapped[bool | None] = mapped_column(Boolean)
    succeeded: Mapped[bool] = mapped_column(Boolean, nullable=False)

    __table_args__: tuple[SchemaItem, ...] = (
        CheckConstraint("file_index >= 0", name="ck_benchmark_compression_results_index"),
        CheckConstraint(
            "raw_bytes >= 0 AND (output_bytes IS NULL OR output_bytes >= 0)",
            name="ck_benchmark_compression_results_bytes",
        ),
        CheckConstraint(
            "file_sha256 ~ '^[0-9a-f]{64}$'",
            name="ck_benchmark_compression_results_file_hash",
        ),
        CheckConstraint(
            "output_sha256 IS NULL OR output_sha256 ~ '^[0-9a-f]{64}$'",
            name="ck_benchmark_compression_results_output_hash",
        ),
        CheckConstraint(
            "tokens_sha256 IS NULL OR tokens_sha256 ~ '^[0-9a-f]{64}$'",
            name="ck_benchmark_compression_results_tokens_hash",
        ),
        CheckConstraint(
            "NOT succeeded OR (output_bytes IS NOT NULL AND output_sha256 IS NOT NULL"
            " AND tokens_deterministic IS DISTINCT FROM FALSE)",
            name="ck_benchmark_compression_results_success",
        ),
    )


class BenchmarkSpeedSample(Base):
    """One repetition with LZ77, encoding and total timings; legacy totals are NULL."""

    __tablename__: str = "benchmark_speed_samples"

    run_id: Mapped[int] = mapped_column(BigInteger, primary_key=True)
    file_index: Mapped[int] = mapped_column(Integer, primary_key=True)
    method: Mapped[str] = mapped_column(Text, primary_key=True)
    repetition: Mapped[int] = mapped_column(Integer, primary_key=True)
    phase: Mapped[str] = mapped_column(Text, nullable=False)
    order_index: Mapped[int] = mapped_column(BigInteger, nullable=False)
    time_s: Mapped[float] = mapped_column(Float, nullable=False)
    encode_s: Mapped[float | None] = mapped_column(Float)
    total_s: Mapped[float | None] = mapped_column(Float)

    __table_args__: tuple[SchemaItem, ...] = (
        ForeignKeyConstraint(
            ["run_id", "file_index", "method"],
            [
                "benchmark_compression_results.run_id",
                "benchmark_compression_results.file_index",
                "benchmark_compression_results.method",
            ],
            ondelete="CASCADE",
            name="fk_benchmark_speed_samples_result",
        ),
        CheckConstraint(
            "file_index >= 0 AND repetition >= 0 AND order_index >= 0",
            name="ck_benchmark_speed_samples_indices",
        ),
        CheckConstraint("phase IN ('warmup', 'measured')", name="ck_benchmark_speed_samples_phase"),
        CheckConstraint(
            "time_s >= 0 AND time_s < 'Infinity'::float8", name="ck_benchmark_speed_samples_time"
        ),
        CheckConstraint(
            "encode_s >= 0 AND encode_s < 'Infinity'::float8",
            name="ck_benchmark_speed_samples_encode",
        ),
        CheckConstraint(
            "total_s >= time_s AND total_s < 'Infinity'::float8",
            name="ck_benchmark_speed_samples_total",
        ),
    )


class BenchmarkAggregation(Base):
    """One successful calculation over explicitly recorded run inputs."""

    __tablename__: str = "benchmark_aggregations"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    source_sha256: Mapped[str] = mapped_column(Text, nullable=False)
    calculator_version: Mapped[str] = mapped_column(Text, nullable=False)
    input_key: Mapped[str | None] = mapped_column(Text, unique=True)
    context: Mapped[dict[str, object] | None] = mapped_column(JSONB)
    statistics: Mapped[dict[str, object] | None] = mapped_column(JSONB)
    created_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )
    raw_bytes: Mapped[int] = mapped_column(BigInteger, nullable=False)
    incumbent_bytes: Mapped[int] = mapped_column(BigInteger, nullable=False)
    bytes: Mapped[int] = mapped_column(BigInteger, nullable=False)
    incumbent_seconds: Mapped[float] = mapped_column(Float, nullable=False)
    parse_seconds: Mapped[float] = mapped_column(Float, nullable=False)
    compression_seconds: Mapped[float | None] = mapped_column(Float)

    __table_args__: tuple[SchemaItem, ...] = (
        CheckConstraint(
            "source_sha256 ~ '^[0-9a-f]{64}$'", name="ck_benchmark_aggregations_source"
        ),
        CheckConstraint(
            "raw_bytes > 0 AND incumbent_bytes >= 0 AND bytes >= 0",
            name="ck_benchmark_aggregations_bytes",
        ),
        CheckConstraint(
            "incumbent_seconds > 0 AND incumbent_seconds < 'Infinity'::float8 "
            "AND parse_seconds >= 0 AND parse_seconds < 'Infinity'::float8",
            name="ck_benchmark_aggregations_time",
        ),
        CheckConstraint(
            "compression_seconds >= 0 AND compression_seconds < 'Infinity'::float8",
            name="ck_benchmark_aggregations_compression",
        ),
    )


class BenchmarkAggregationInput(Base):
    """The exact runs used, preserved when later runs or aggregations are created."""

    __tablename__: str = "benchmark_aggregation_inputs"

    aggregation_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("benchmark_aggregations.id", ondelete="CASCADE"), primary_key=True
    )
    run_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("benchmark_runs.id", ondelete="RESTRICT"), primary_key=True
    )

    __table_args__: tuple[SchemaItem, ...] = (
        Index("ix_benchmark_aggregation_inputs_run_id", "run_id"),
    )


class SubmissionAdmissionCheck(Base):
    """Immutable admission evidence; submissions explicitly select their current decision."""

    __tablename__: str = "submission_admission_checks"
    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    submission_id: Mapped[int] = mapped_column(
        BigInteger,
        ForeignKey("submissions.id", ondelete="RESTRICT"),
        nullable=False,
    )
    candidate_aggregation_id: Mapped[int] = mapped_column(
        BigInteger,
        ForeignKey("benchmark_aggregations.id", ondelete="RESTRICT"),
        nullable=False,
    )
    reference_aggregation_id: Mapped[int | None] = mapped_column(
        BigInteger,
        ForeignKey("benchmark_aggregations.id", ondelete="RESTRICT"),
    )
    decision_key: Mapped[str] = mapped_column(Text, nullable=False, unique=True)
    policy_version: Mapped[str] = mapped_column(Text, nullable=False)
    outcome: Mapped[str] = mapped_column(Text, nullable=False)
    reason_code: Mapped[str] = mapped_column(Text, nullable=False)
    details: Mapped[dict[str, object]] = mapped_column(JSONB, nullable=False)
    created_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True),
        nullable=False,
        server_default=func.now(),
    )
    __table_args__: tuple[SchemaItem, ...] = (
        CheckConstraint(
            "outcome IN ('passed', 'inconclusive', 'not_required', 'dominated')",
            name="ck_admission_outcome",
        ),
        CheckConstraint(
            "(outcome IN ('passed', 'inconclusive')) = (reference_aggregation_id IS NOT NULL)",
            name="ck_admission_reference",
        ),
        Index("ix_admission_submission", "submission_id"),
    )
