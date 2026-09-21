"""Raw benchmark runs, timing samples and explicit aggregation inputs."""

import sqlalchemy as sa
from alembic import op
from sqlalchemy.dialects import postgresql

revision = "0002"
down_revision = "0001"
branch_labels = None
depends_on = None


def upgrade() -> None:
    op.create_table(
        "benchmark_aggregations",
        sa.Column("id", sa.BigInteger(), autoincrement=True, nullable=False),
        sa.Column("source_sha256", sa.Text(), nullable=False),
        sa.Column("calculator_version", sa.Text(), nullable=False),
        sa.Column(
            "created_at",
            sa.DateTime(timezone=True),
            server_default=sa.text("now()"),
            nullable=False,
        ),
        sa.Column("raw_bytes", sa.BigInteger(), nullable=False),
        sa.Column("incumbent_bytes", sa.BigInteger(), nullable=False),
        sa.Column("bytes", sa.BigInteger(), nullable=False),
        sa.Column("incumbent_seconds", sa.Float(), nullable=False),
        sa.Column("parse_seconds", sa.Float(), nullable=False),
        sa.CheckConstraint(
            "incumbent_seconds > 0 AND incumbent_seconds < 'Infinity'::float8"
            " AND parse_seconds >= 0 AND parse_seconds < 'Infinity'::float8",
            name="ck_benchmark_aggregations_time",
        ),
        sa.CheckConstraint(
            "source_sha256 ~ '^[0-9a-f]{64}$'", name="ck_benchmark_aggregations_source"
        ),
        sa.CheckConstraint(
            "raw_bytes > 0 AND incumbent_bytes >= 0 AND bytes >= 0",
            name="ck_benchmark_aggregations_bytes",
        ),
        sa.PrimaryKeyConstraint("id"),
    )
    op.create_table(
        "benchmark_runs",
        sa.Column("id", sa.BigInteger(), autoincrement=True, nullable=False),
        sa.Column("source_sha256", sa.Text(), nullable=False),
        sa.Column("candidate_method", sa.Text(), nullable=False),
        sa.Column("corpus", sa.Text(), nullable=False),
        sa.Column("corpus_sha256", sa.Text(), nullable=False),
        sa.Column("status", sa.Text(), nullable=False),
        sa.Column(
            "created_at",
            sa.DateTime(timezone=True),
            server_default=sa.text("now()"),
            nullable=False,
        ),
        sa.Column("started_at", sa.DateTime(timezone=True), nullable=True),
        sa.Column("finished_at", sa.DateTime(timezone=True), nullable=True),
        sa.Column("invalidated_at", sa.DateTime(timezone=True), nullable=True),
        sa.Column("invalidation_reason", sa.Text(), nullable=True),
        sa.Column("raw_data", postgresql.JSONB(astext_type=sa.Text()), nullable=False),
        sa.CheckConstraint("corpus_sha256 ~ '^[0-9a-f]{64}$'", name="ck_benchmark_runs_corpus"),
        sa.CheckConstraint("jsonb_typeof(raw_data) = 'array'", name="ck_benchmark_runs_raw"),
        sa.CheckConstraint("source_sha256 ~ '^[0-9a-f]{64}$'", name="ck_benchmark_runs_source"),
        sa.CheckConstraint("status IN ('complete', 'failed')", name="ck_benchmark_runs_status"),
        sa.CheckConstraint(
            "(invalidated_at IS NULL) = (invalidation_reason IS NULL)",
            name="ck_benchmark_runs_invalidation",
        ),
        sa.PrimaryKeyConstraint("id"),
    )
    op.create_index(
        "ix_benchmark_runs_lookup",
        "benchmark_runs",
        ["source_sha256", "corpus_sha256", "created_at", "id"],
        unique=False,
    )
    op.create_table(
        "benchmark_aggregation_inputs",
        sa.Column("aggregation_id", sa.BigInteger(), nullable=False),
        sa.Column("run_id", sa.BigInteger(), nullable=False),
        sa.ForeignKeyConstraint(
            ["aggregation_id"], ["benchmark_aggregations.id"], ondelete="CASCADE"
        ),
        sa.ForeignKeyConstraint(["run_id"], ["benchmark_runs.id"], ondelete="RESTRICT"),
        sa.PrimaryKeyConstraint("aggregation_id", "run_id"),
    )
    op.create_index(
        "ix_benchmark_aggregation_inputs_run_id",
        "benchmark_aggregation_inputs",
        ["run_id"],
        unique=False,
    )
    op.create_table(
        "benchmark_measurements",
        sa.Column("run_id", sa.BigInteger(), nullable=False),
        sa.Column("file_index", sa.Integer(), nullable=False),
        sa.Column("method", sa.Text(), nullable=False),
        sa.Column("repetition", sa.Integer(), nullable=False),
        sa.Column("file_path", sa.Text(), nullable=False),
        sa.Column("phase", sa.Text(), nullable=False),
        sa.Column("order_index", sa.BigInteger(), nullable=False),
        sa.Column("time_s", sa.Float(), nullable=False),
        sa.CheckConstraint(
            "phase IN ('warmup', 'measured')", name="ck_benchmark_measurements_phase"
        ),
        sa.CheckConstraint(
            "time_s >= 0 AND time_s < 'Infinity'::float8", name="ck_benchmark_measurements_time"
        ),
        sa.CheckConstraint(
            "file_index >= 0 AND repetition >= 0 AND order_index >= 0",
            name="ck_benchmark_measurements_indices",
        ),
        sa.ForeignKeyConstraint(["run_id"], ["benchmark_runs.id"], ondelete="CASCADE"),
        sa.PrimaryKeyConstraint("run_id", "file_index", "method", "repetition"),
    )
    op.add_column("score_snapshots", sa.Column("aggregation_id", sa.BigInteger(), nullable=True))
    op.create_foreign_key(
        "fk_scoresnapshot_aggregation",
        "score_snapshots",
        "benchmark_aggregations",
        ["aggregation_id"],
        ["id"],
        ondelete="RESTRICT",
    )
    op.add_column("submissions", sa.Column("aggregation_id", sa.BigInteger(), nullable=True))
    op.create_foreign_key(
        "fk_submission_aggregation",
        "submissions",
        "benchmark_aggregations",
        ["aggregation_id"],
        ["id"],
        ondelete="RESTRICT",
    )


def downgrade() -> None:
    op.drop_constraint("fk_submission_aggregation", "submissions", type_="foreignkey")
    op.drop_column("submissions", "aggregation_id")
    op.drop_constraint("fk_scoresnapshot_aggregation", "score_snapshots", type_="foreignkey")
    op.drop_column("score_snapshots", "aggregation_id")
    op.drop_table("benchmark_measurements")
    op.drop_index(
        "ix_benchmark_aggregation_inputs_run_id", table_name="benchmark_aggregation_inputs"
    )
    op.drop_table("benchmark_aggregation_inputs")
    op.drop_index("ix_benchmark_runs_lookup", table_name="benchmark_runs")
    op.drop_table("benchmark_runs")
    op.drop_table("benchmark_aggregations")
