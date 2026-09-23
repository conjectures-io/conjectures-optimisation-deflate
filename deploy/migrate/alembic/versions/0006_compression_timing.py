"""Repeated encoding and total compression timings, preserving legacy evidence."""

import sqlalchemy as sa
from alembic import op

revision = "0006"
down_revision = "0005"
branch_labels = None
depends_on = None


def upgrade():
    # No backfill: v3's single encoding sample cannot reconstruct paired totals.
    for table in ("submissions", "benchmark_aggregations"):
        op.add_column(table, sa.Column("compression_seconds", sa.Float(), nullable=True))
    for name in ("encode_s", "total_s"):
        op.add_column("benchmark_speed_samples", sa.Column(name, sa.Float(), nullable=True))
    op.create_check_constraint(
        "ck_benchmark_speed_samples_encode",
        "benchmark_speed_samples",
        "encode_s >= 0 AND encode_s < 'Infinity'::float8",
    )
    op.create_check_constraint(
        "ck_benchmark_speed_samples_total",
        "benchmark_speed_samples",
        "total_s >= time_s AND total_s < 'Infinity'::float8",
    )
    op.create_check_constraint(
        "ck_benchmark_aggregations_compression",
        "benchmark_aggregations",
        "compression_seconds >= 0 AND compression_seconds < 'Infinity'::float8",
    )


def downgrade():
    op.drop_constraint("ck_benchmark_aggregations_compression", "benchmark_aggregations")
    op.drop_constraint("ck_benchmark_speed_samples_total", "benchmark_speed_samples")
    op.drop_constraint("ck_benchmark_speed_samples_encode", "benchmark_speed_samples")
    for name in ("total_s", "encode_s"):
        op.drop_column("benchmark_speed_samples", name)
    for table in ("benchmark_aggregations", "submissions"):
        op.drop_column(table, "compression_seconds")
