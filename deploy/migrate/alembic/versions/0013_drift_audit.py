"""Finished gate results and last observed drift identities.

Revision ID: 0013
Revises: 0012
"""

import sqlalchemy as sa
from alembic import op
from sqlalchemy.dialects.postgresql import JSONB

revision = "0013"
down_revision = "0012"
branch_labels = None
depends_on = None


def upgrade() -> None:
    op.add_column(
        "benchmark_runs",
        sa.Column(
            "submission_id", sa.BigInteger(), sa.ForeignKey("submissions.id", ondelete="RESTRICT")
        ),
    )
    op.add_column("benchmark_runs", sa.Column("gate_attempt_token", sa.Text()))
    op.create_index("ix_benchmark_runs_submission", "benchmark_runs", ["submission_id", "id"])
    op.create_table(
        "gate_results",
        sa.Column("id", sa.BigInteger(), primary_key=True, autoincrement=True),
        sa.Column(
            "submission_id",
            sa.BigInteger(),
            sa.ForeignKey("submissions.id", ondelete="RESTRICT"),
            nullable=False,
        ),
        sa.Column("attempt_token", sa.Text(), nullable=False),
        sa.Column("stage", sa.Text(), nullable=False),
        sa.Column("exit_code", sa.Integer(), nullable=False),
        sa.Column("observed", JSONB(), nullable=False),
        sa.Column(
            "finished_at", sa.DateTime(timezone=True), nullable=False, server_default=sa.func.now()
        ),
        sa.UniqueConstraint(
            "submission_id", "attempt_token", "stage", name="uq_gate_result_attempt"
        ),
    )
    op.create_index("ix_gate_results_submission", "gate_results", ["submission_id", "finished_at"])
    op.create_table(
        "observed_states",
        sa.Column("key", sa.Text(), primary_key=True),
        sa.Column("digest", sa.Text(), nullable=False),
        sa.Column("details", JSONB(), nullable=False),
        sa.Column(
            "observed_at", sa.DateTime(timezone=True), nullable=False, server_default=sa.func.now()
        ),
    )


def downgrade() -> None:
    op.drop_table("observed_states")
    op.drop_index("ix_gate_results_submission", table_name="gate_results")
    op.drop_table("gate_results")
    op.drop_index("ix_benchmark_runs_submission", table_name="benchmark_runs")
    op.drop_column("benchmark_runs", "gate_attempt_token")
    op.drop_column("benchmark_runs", "submission_id")
