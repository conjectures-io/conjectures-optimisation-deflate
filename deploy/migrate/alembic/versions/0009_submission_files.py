"""Submission files in the database, so the platform API can queue without a shared disk."""

import sqlalchemy as sa
from alembic import op

revision = "0009"
down_revision = "0008"
branch_labels = None
depends_on = None


def upgrade():
    op.create_table(
        "submission_files",
        sa.Column(
            "submission_id",
            sa.BigInteger(),
            sa.ForeignKey("submissions.id", ondelete="CASCADE"),
            primary_key=True,
        ),
        sa.Column("name", sa.Text(), primary_key=True),
        sa.Column("content", sa.LargeBinary(), nullable=False),
        sa.Column(
            "created_at", sa.DateTime(timezone=True), nullable=False, server_default=sa.func.now()
        ),
        sa.CheckConstraint(
            "name IN ('parse.rs', 'Parse.lean')", name="ck_submission_files_name"
        ),
    )


def downgrade():
    op.drop_table("submission_files")
