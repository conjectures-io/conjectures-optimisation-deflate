"""The submission bounty ledger: epochs read, alpha credited, submissions capped.

Each pass's per-submission totals are published in weight_sets.api_snapshot["bounty"];
score_snapshots is unchanged, and a capped row carries burn_reason 'bounty-cap'.

Revision ID: 0012
Revises: 0011
"""

import sqlalchemy as sa
from alembic import op

revision = "0012"
down_revision = "0011"
branch_labels = None
depends_on = None


def upgrade() -> None:
    op.create_table(
        "bounty_epochs",
        sa.Column("netuid", sa.Integer(), primary_key=True),
        sa.Column("epoch_block", sa.BigInteger(), primary_key=True),
        sa.Column("observed_block", sa.BigInteger(), nullable=False),
        sa.Column("tempo", sa.Integer(), nullable=False),
        sa.Column("reveal_epochs", sa.Integer(), nullable=False),
        sa.Column("miner_pool_rao", sa.BigInteger(), nullable=False),
        sa.Column(
            "created_at", sa.DateTime(timezone=True), nullable=False, server_default=sa.func.now()
        ),
    )
    op.create_table(
        "bounty_accruals",
        sa.Column("id", sa.BigInteger(), primary_key=True, autoincrement=True),
        sa.Column("netuid", sa.Integer(), nullable=False),
        sa.Column("epoch_block", sa.BigInteger(), nullable=False),
        sa.Column(
            "submission_id",
            sa.BigInteger(),
            sa.ForeignKey("submissions.id", ondelete="RESTRICT"),
            nullable=False,
        ),
        sa.Column("hotkey", sa.Text(), nullable=False),
        sa.Column("coldkey", sa.Text(), nullable=False),
        sa.Column("uid", sa.Integer(), nullable=False),
        sa.Column("alpha_rao", sa.BigInteger(), nullable=False),
        sa.Column(
            "weight_set_id",
            sa.BigInteger(),
            sa.ForeignKey("weight_sets.id", ondelete="RESTRICT"),
            nullable=False,
        ),
        sa.Column(
            "created_at", sa.DateTime(timezone=True), nullable=False, server_default=sa.func.now()
        ),
        sa.ForeignKeyConstraint(
            ["netuid", "epoch_block"],
            ["bounty_epochs.netuid", "bounty_epochs.epoch_block"],
            ondelete="RESTRICT",
        ),
        sa.UniqueConstraint("netuid", "epoch_block", "submission_id", "uid"),
        sa.CheckConstraint("alpha_rao >= 0", name="ck_bounty_accrual_nonnegative"),
    )
    op.create_index("ix_bounty_accruals_submission", "bounty_accruals", ["submission_id"])
    op.create_table(
        "bounty_caps",
        sa.Column(
            "submission_id",
            sa.BigInteger(),
            sa.ForeignKey("submissions.id", ondelete="RESTRICT"),
            primary_key=True,
        ),
        sa.Column("hotkey", sa.Text(), nullable=False),
        sa.Column("earned_rao", sa.BigInteger(), nullable=False),
        sa.Column("projected_rao", sa.BigInteger(), nullable=False),
        sa.Column("bounty_rao", sa.BigInteger(), nullable=False),
        sa.Column(
            "created_at", sa.DateTime(timezone=True), nullable=False, server_default=sa.func.now()
        ),
    )


def downgrade() -> None:
    op.drop_table("bounty_caps")
    op.drop_index("ix_bounty_accruals_submission", table_name="bounty_accruals")
    op.drop_table("bounty_accruals")
    op.drop_table("bounty_epochs")
