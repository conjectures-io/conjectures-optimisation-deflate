"""Identify unchanged scoring publications without rereading their JSON payloads.

Revision ID: 0015
Revises: 0014
"""

import sqlalchemy as sa
from alembic import op

revision = "0015"
down_revision = "0014"
branch_labels = None
depends_on = None


def upgrade() -> None:
    op.add_column("weight_sets", sa.Column("scoring_content_sha256", sa.Text(), nullable=True))
    op.create_index("ix_weight_sets_netuid_id", "weight_sets", ["netuid", "id"])


def downgrade() -> None:
    op.drop_index("ix_weight_sets_netuid_id", table_name="weight_sets")
    op.drop_column("weight_sets", "scoring_content_sha256")
