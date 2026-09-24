"""Record scoring-bound exclusions independently of successful benchmarks."""

from alembic import op

revision = "0010"
down_revision = "0009"
branch_labels = None
depends_on = None


def upgrade() -> None:
    op.drop_constraint("ck_admission_outcome", "submission_admission_checks", type_="check")
    op.create_check_constraint(
        "ck_admission_outcome",
        "submission_admission_checks",
        "outcome IN ('passed', 'inconclusive', 'not_required', 'dominated', 'excluded')",
    )


def downgrade() -> None:
    # Refuse when exclusions exist rather than deleting historical decisions.
    op.drop_constraint("ck_admission_outcome", "submission_admission_checks", type_="check")
    op.create_check_constraint(
        "ck_admission_outcome",
        "submission_admission_checks",
        "outcome IN ('passed', 'inconclusive', 'not_required', 'dominated')",
    )
