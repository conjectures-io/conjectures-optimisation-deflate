"""Persist account attribution and immutable API scoring evidence.

Revision ID: 0011
Revises: 0010
"""

import sqlalchemy as sa
from alembic import op
from sqlalchemy.dialects.postgresql import JSONB

revision = "0011"
down_revision = "0010"
branch_labels = None
depends_on = None


def upgrade() -> None:
    op.add_column("submissions", sa.Column("account_id", sa.Text(), nullable=True))
    op.add_column("weight_sets", sa.Column("api_snapshot", JSONB(), nullable=True))


def downgrade() -> None:
    op.drop_column("weight_sets", "api_snapshot")
    op.drop_column("submissions", "account_id")
