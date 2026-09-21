"""Raw runs, compression results, speed samples and aggregation inputs."""

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
        sa.Column("run_key", sa.Text(), nullable=True),
        sa.UniqueConstraint("run_key", name="uq_benchmark_runs_run_key"),
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
        "benchmark_compression_results",
        sa.Column("run_id", sa.BigInteger(), nullable=False),
        sa.Column("file_index", sa.Integer(), nullable=False),
        sa.Column("method", sa.Text(), nullable=False),
        sa.Column("file_path", sa.Text(), nullable=False),
        sa.Column("file_sha256", sa.Text(), nullable=False),
        sa.Column("raw_bytes", sa.BigInteger(), nullable=False),
        sa.Column("output_bytes", sa.BigInteger(), nullable=True),
        sa.Column("output_sha256", sa.Text(), nullable=True),
        sa.Column("tokens_sha256", sa.Text(), nullable=True),
        sa.Column("tokens_deterministic", sa.Boolean(), nullable=True),
        sa.Column("succeeded", sa.Boolean(), nullable=False),
        sa.ForeignKeyConstraint(["run_id"], ["benchmark_runs.id"], ondelete="CASCADE"),
        sa.PrimaryKeyConstraint("run_id", "file_index", "method"),
        sa.CheckConstraint("file_index >= 0", name="ck_benchmark_compression_results_index"),
        sa.CheckConstraint(
            "raw_bytes >= 0 AND (output_bytes IS NULL OR output_bytes >= 0)",
            name="ck_benchmark_compression_results_bytes",
        ),
        sa.CheckConstraint(
            "file_sha256 ~ '^[0-9a-f]{64}$'",
            name="ck_benchmark_compression_results_file_hash",
        ),
        sa.CheckConstraint(
            "output_sha256 IS NULL OR output_sha256 ~ '^[0-9a-f]{64}$'",
            name="ck_benchmark_compression_results_output_hash",
        ),
        sa.CheckConstraint(
            "tokens_sha256 IS NULL OR tokens_sha256 ~ '^[0-9a-f]{64}$'",
            name="ck_benchmark_compression_results_tokens_hash",
        ),
        sa.CheckConstraint(
            "NOT succeeded OR (output_bytes IS NOT NULL AND output_sha256 IS NOT NULL"
            " AND tokens_deterministic IS DISTINCT FROM FALSE)",
            name="ck_benchmark_compression_results_success",
        ),
    )
    op.create_table(
        "benchmark_speed_samples",
        sa.Column("run_id", sa.BigInteger(), nullable=False),
        sa.Column("file_index", sa.Integer(), nullable=False),
        sa.Column("method", sa.Text(), nullable=False),
        sa.Column("repetition", sa.Integer(), nullable=False),
        sa.Column("phase", sa.Text(), nullable=False),
        sa.Column("order_index", sa.BigInteger(), nullable=False),
        sa.Column("time_s", sa.Float(), nullable=False),
        sa.CheckConstraint(
            "phase IN ('warmup', 'measured')", name="ck_benchmark_speed_samples_phase"
        ),
        sa.CheckConstraint(
            "time_s >= 0 AND time_s < 'Infinity'::float8", name="ck_benchmark_speed_samples_time"
        ),
        sa.CheckConstraint(
            "file_index >= 0 AND repetition >= 0 AND order_index >= 0",
            name="ck_benchmark_speed_samples_indices",
        ),
        sa.ForeignKeyConstraint(
            ["run_id", "file_index", "method"],
            [
                "benchmark_compression_results.run_id",
                "benchmark_compression_results.file_index",
                "benchmark_compression_results.method",
            ],
            ondelete="CASCADE",
            name="fk_benchmark_speed_samples_result",
        ),
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
    op.drop_table("benchmark_speed_samples")
    op.drop_table("benchmark_compression_results")
    op.drop_index(
        "ix_benchmark_aggregation_inputs_run_id", table_name="benchmark_aggregation_inputs"
    )
    op.drop_table("benchmark_aggregation_inputs")
    op.drop_index("ix_benchmark_runs_lookup", table_name="benchmark_runs")
    op.drop_table("benchmark_runs")
    op.drop_table("benchmark_aggregations")
