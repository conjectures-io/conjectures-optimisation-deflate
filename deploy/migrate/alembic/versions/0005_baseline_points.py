"""Operator baseline revisions and per-point payout audit."""

import sqlalchemy as sa
from alembic import op

revision = "0005"
down_revision = "0004"
branch_labels = None
depends_on = None


def upgrade():
    op.alter_column("submissions", "hotkey", existing_type=sa.Text(), nullable=True)
    op.add_column("submissions", sa.Column("baseline_key", sa.Text(), nullable=True))
    op.add_column(
        "submissions",
        sa.Column("baseline_active", sa.Boolean(), nullable=False, server_default="false"),
    )
    op.create_unique_constraint(
        "uq_submission_baseline_digest", "submissions", ["baseline_key", "digest"]
    )
    op.create_check_constraint(
        "ck_submission_owner", "submissions", "(baseline_key IS NULL) = (hotkey IS NOT NULL)"
    )
    op.create_check_constraint(
        "ck_submission_baseline_active",
        "submissions",
        "NOT baseline_active OR baseline_key IS NOT NULL",
    )
    op.create_index(
        "uq_active_baseline",
        "submissions",
        ["baseline_key"],
        unique=True,
        postgresql_where=sa.text("baseline_active"),
    )
    op.alter_column("score_snapshots", "hotkey", existing_type=sa.Text(), nullable=True)
    for name in ("baseline_key", "burn_reason"):
        op.add_column("score_snapshots", sa.Column(name, sa.Text(), nullable=True))
    op.add_column(
        "score_snapshots",
        sa.Column("payable_weight", sa.Float(), nullable=False, server_default="0"),
    )


def downgrade():
    # Refuse rather than delete operator evidence to satisfy the old NOT NULL schema.
    conn = op.get_bind()
    if conn.scalar(sa.text("SELECT count(*) FROM submissions WHERE hotkey IS NULL")) or conn.scalar(
        sa.text("SELECT count(*) FROM score_snapshots WHERE hotkey IS NULL")
    ):
        raise RuntimeError("baseline evidence exists; export/remove it explicitly before downgrade")
    for name in ("payable_weight", "burn_reason", "baseline_key"):
        op.drop_column("score_snapshots", name)
    op.alter_column("score_snapshots", "hotkey", existing_type=sa.Text(), nullable=False)
    op.drop_index("uq_active_baseline", table_name="submissions")
    for name in (
        "ck_submission_owner",
        "ck_submission_baseline_active",
        "uq_submission_baseline_digest",
    ):
        op.drop_constraint(name, "submissions")
    for name in ("baseline_active", "baseline_key"):
        op.drop_column("submissions", name)
    op.alter_column("submissions", "hotkey", existing_type=sa.Text(), nullable=False)
