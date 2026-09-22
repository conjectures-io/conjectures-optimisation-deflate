"""Reusable static/Lean verification identity on submissions.

Revision ID: 0003
Revises: 0002
"""

import sqlalchemy as sa
from alembic import op

revision = "0003"
down_revision = "0002"
branch_labels = None
depends_on = None

HASHES = ("source_sha256", "proof_sha256", "verifier_fingerprint", "measured_source_sha256")


def upgrade():
    for name in (*HASHES, "verification_attempt"):
        op.add_column("submissions", sa.Column(name, sa.Text(), nullable=True))
    for name in ("static_verified_at", "lean_verified_at"):
        op.add_column("submissions", sa.Column(name, sa.DateTime(timezone=True), nullable=True))
    for name in HASHES:
        op.create_check_constraint(
            f"ck_submission_{name}", "submissions", f"{name} IS NULL OR {name} ~ '^[0-9a-f]{{64}}$'"
        )
    op.create_check_constraint(
        "ck_submission_lean_requires_static",
        "submissions",
        "lean_verified_at IS NULL OR static_verified_at IS NOT NULL",
    )
    op.create_check_constraint(
        "ck_submission_verification_identity",
        "submissions",
        "static_verified_at IS NULL OR (source_sha256 IS NOT NULL AND "
        "proof_sha256 IS NOT NULL AND verifier_fingerprint IS NOT NULL)",
    )
    op.create_index("ix_submissions_source_sha256", "submissions", ["source_sha256"])


def downgrade():
    op.drop_index("ix_submissions_source_sha256", table_name="submissions")
    for name in ("lean_requires_static", "verification_identity", *HASHES):
        op.drop_constraint(f"ck_submission_{name}", "submissions", type_="check")
    for name in ("lean_verified_at", "static_verified_at", "verification_attempt", *HASHES):
        op.drop_column("submissions", name)
