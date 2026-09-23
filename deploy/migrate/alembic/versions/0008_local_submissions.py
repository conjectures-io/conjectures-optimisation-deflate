"""Allow ownerless diagnostic submissions without adding a submission flag."""

from alembic import op

revision = "0008"
down_revision = "0007"
branch_labels = None
depends_on = None


def upgrade():
    op.drop_constraint("ck_submission_owner", "submissions", type_="check")
    op.create_check_constraint(
        "ck_submission_owner", "submissions", "hotkey IS NULL OR baseline_key IS NULL"
    )


def downgrade():
    # Refuse if test rows remain; never silently delete their evidence.
    op.drop_constraint("ck_submission_owner", "submissions", type_="check")
    op.create_check_constraint(
        "ck_submission_owner",
        "submissions",
        "(baseline_key IS NULL) = (hotkey IS NOT NULL)",
    )
