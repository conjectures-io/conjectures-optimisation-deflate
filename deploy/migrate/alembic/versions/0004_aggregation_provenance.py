"""Aggregation identity, comparison context and timing uncertainty."""

import sqlalchemy as sa
from alembic import op
from sqlalchemy.dialects.postgresql import JSONB

revision = "0004"
down_revision = "0003"
branch_labels = None
depends_on = None


def upgrade():
    op.add_column("benchmark_aggregations", sa.Column("input_key", sa.Text(), nullable=True))
    op.create_unique_constraint(
        "benchmark_aggregations_input_key_key", "benchmark_aggregations", ["input_key"]
    )
    for name in ("context", "statistics"):
        op.add_column("benchmark_aggregations", sa.Column(name, JSONB(), nullable=True))


def downgrade():
    for name in ("statistics", "context", "input_key"):
        op.drop_column("benchmark_aggregations", name)
