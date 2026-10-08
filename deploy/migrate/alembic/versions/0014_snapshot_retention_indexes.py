"""Partial indexes for latest API snapshots and batched expiry.

Revision ID: 0014
Revises: 0013
"""

import sqlalchemy as sa
from alembic import op

revision = "0014"
down_revision = "0013"
branch_labels = None
depends_on = None


def upgrade() -> None:
    op.create_index(
        "ix_weight_sets_snapshot_latest",
        "weight_sets",
        ["netuid", "id"],
        postgresql_where=sa.text("api_snapshot IS NOT NULL"),
    )
    op.create_index(
        "ix_weight_sets_snapshot_expiry",
        "weight_sets",
        ["netuid", "created_at", "id"],
        postgresql_where=sa.text("api_snapshot IS NOT NULL"),
    )


def downgrade() -> None:
    op.drop_index("ix_weight_sets_snapshot_expiry", table_name="weight_sets")
    op.drop_index("ix_weight_sets_snapshot_latest", table_name="weight_sets")
