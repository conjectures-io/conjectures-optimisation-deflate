"""Immutable statistical admission history and explicit publication pointers."""

import sqlalchemy as sa
from alembic import op
from sqlalchemy.dialects import postgresql

revision = "0007"
down_revision = "0006"
branch_labels = None
depends_on = None


def upgrade():
    op.create_table(
        "submission_admission_checks",
        sa.Column("id", sa.BigInteger(), primary_key=True),
        sa.Column(
            "submission_id",
            sa.BigInteger(),
            sa.ForeignKey("submissions.id", ondelete="RESTRICT"),
            nullable=False,
        ),
        sa.Column(
            "candidate_aggregation_id",
            sa.BigInteger(),
            sa.ForeignKey("benchmark_aggregations.id", ondelete="RESTRICT"),
            nullable=False,
        ),
        sa.Column(
            "reference_aggregation_id",
            sa.BigInteger(),
            sa.ForeignKey("benchmark_aggregations.id", ondelete="RESTRICT"),
        ),
        sa.Column("decision_key", sa.Text(), nullable=False, unique=True),
        sa.Column("policy_version", sa.Text(), nullable=False),
        sa.Column("outcome", sa.Text(), nullable=False),
        sa.Column("reason_code", sa.Text(), nullable=False),
        sa.Column("details", postgresql.JSONB(), nullable=False),
        sa.Column(
            "created_at", sa.DateTime(timezone=True), nullable=False, server_default=sa.func.now()
        ),
        sa.CheckConstraint(
            "outcome IN ('passed', 'inconclusive', 'not_required', 'dominated')",
            name="ck_admission_outcome",
        ),
        sa.CheckConstraint(
            "(outcome IN ('passed', 'inconclusive')) = (reference_aggregation_id IS NOT NULL)",
            name="ck_admission_reference",
        ),
    )
    op.create_index("ix_admission_submission", "submission_admission_checks", ["submission_id"])
    for table in ("submissions", "score_snapshots"):
        op.add_column(table, sa.Column("admission_check_id", sa.BigInteger(), nullable=True))
        op.create_foreign_key(
            f"fk_{table}_admission",
            table,
            "submission_admission_checks",
            ["admission_check_id"],
            ["id"],
            ondelete="RESTRICT",
        )
    op.execute("""CREATE FUNCTION immutable_admission_check() RETURNS trigger LANGUAGE plpgsql AS $$
        BEGIN RAISE EXCEPTION 'admission checks are immutable; append a new decision'; END $$""")
    op.execute("""CREATE TRIGGER admission_checks_immutable BEFORE UPDATE OR DELETE
        ON submission_admission_checks FOR EACH ROW EXECUTE FUNCTION immutable_admission_check()""")


def downgrade():
    for table in ("score_snapshots", "submissions"):
        op.drop_column(table, "admission_check_id")
    op.drop_table("submission_admission_checks")
    op.execute("DROP FUNCTION immutable_admission_check()")
