"""The migration and the models must describe the same database.

The models are what the code reads and what autogenerate compares against; the Alembic
revisions are what a validator actually runs. A column added to one and not the other is
a production failure that no other test would catch, so this one applies the migrations
to an empty database and asserts nothing is left to change.
"""

from __future__ import annotations

import os
import sys
import uuid
from pathlib import Path

import pytest
import sqlalchemy as sa
from alembic import command
from alembic.autogenerate import compare_metadata
from alembic.config import Config
from alembic.migration import MigrationContext
from sqlalchemy.exc import IntegrityError

VALIDATOR = Path(__file__).resolve().parent.parent
REPO = VALIDATOR.parent
sys.path.insert(0, str(VALIDATOR))

from db import models  # noqa: E402
from db.status import STATE_VALUES, SubmissionState  # noqa: E402

ALEMBIC = REPO / "deploy/migrate"


def _alembic_config(url: str) -> Config:
    config = Config(str(ALEMBIC / "alembic.ini"))
    config.set_main_option("script_location", str(ALEMBIC / "alembic"))
    config.set_main_option("sqlalchemy.url", url)
    return config


@pytest.fixture
def migrated(database_url):
    """A second scratch database with the migrations applied, rather than create_all.

    The session fixture builds its schema from the models, which is fast and is what the
    other tests want. This one has to come from the revisions, or it would be comparing
    the models against themselves.
    """
    base, _ = database_url.rsplit("/", 1)
    name = f"conjectures_migrated_{uuid.uuid4().hex[:8]}"
    admin = sa.create_engine(f"{base}/postgres", isolation_level="AUTOCOMMIT")
    with admin.connect() as conn:
        conn.execute(sa.text(f'CREATE DATABASE "{name}"'))
    url = f"{base}/{name}"
    previous = os.environ.get("DATABASE_URL")
    os.environ["DATABASE_URL"] = url
    try:
        command.upgrade(_alembic_config(url), "head")
        yield url
    finally:
        if previous is None:
            os.environ.pop("DATABASE_URL", None)
        else:
            os.environ["DATABASE_URL"] = previous
        with admin.connect() as conn:
            conn.execute(sa.text(f'DROP DATABASE IF EXISTS "{name}"'))
        admin.dispose()


def test_the_migrations_build_exactly_what_the_models_describe(migrated):
    engine = sa.create_engine(migrated)
    try:
        with engine.connect() as conn:
            context = MigrationContext.configure(
                conn, opts={"compare_type": True, "compare_server_default": True}
            )
            diff = compare_metadata(context, models.Base.metadata)
    finally:
        engine.dispose()
    assert diff == [], f"models and migrations have drifted: {diff}"


def test_the_migrations_are_reversible(migrated):
    # A revision that cannot be undone is a revision nobody dares apply.
    config = _alembic_config(migrated)
    command.downgrade(config, "base")
    engine = sa.create_engine(migrated)
    try:
        remaining = sa.inspect(engine).get_table_names()
    finally:
        engine.dispose()
    assert set(remaining) <= {"alembic_version"}


# ── The contracts the schema encodes ──────────────────────────────────────


def test_the_state_check_matches_the_python_enum(store):
    # The CHECK constraint and the enum are two spellings of one list; if they drift, a
    # state the code can produce becomes a state the database refuses to store.
    assert STATE_VALUES == ("queued", "verifying", "accepted", "rejected", "error")
    with store.engine.connect() as conn:
        rendered = conn.execute(
            sa.text(
                "SELECT pg_get_constraintdef(oid) FROM pg_constraint "
                "WHERE conname = 'ck_submissions_state'"
            )
        ).scalar_one()
    for state in SubmissionState:
        assert f"'{state.value}'" in rendered


def test_an_unknown_state_is_refused_by_the_database(store):
    sid, _ = store.submissions.add("5" * 47, "a" * 64)
    with pytest.raises(IntegrityError):
        with store.engine.begin() as conn:
            conn.execute(
                sa.text("UPDATE submissions SET state = 'promoted' WHERE id = :i"), {"i": sid}
            )


def test_a_registration_cannot_be_recorded_twice_for_one_block(store):
    from conftest import register

    register(store, "5" * 47, uid=3, block=42)
    with pytest.raises(IntegrityError):
        register(store, "5" * 47, uid=3, block=42)


def test_the_same_files_from_one_hotkey_are_one_submission(store):
    first, fresh = store.submissions.add("5" * 47, "a" * 64)
    second, again = store.submissions.add("5" * 47, "a" * 64)
    assert (fresh, again) == (True, False) and first == second


def test_submission_files_precede_scoring_bounds(migrated):
    """Main's 0009 remains stable; only 0010 adds the exclusion outcome."""
    config = _alembic_config(migrated)
    engine = sa.create_engine(migrated)
    try:
        with engine.connect() as conn:
            assert (
                conn.execute(sa.text("SELECT version_num FROM alembic_version")).scalar_one()
                == "0014"
            )
            constraint = conn.execute(
                sa.text(
                    "SELECT pg_get_constraintdef(oid) FROM pg_constraint "
                    "WHERE conname = 'ck_admission_outcome'"
                )
            ).scalar_one()
            assert "'excluded'" in constraint
        command.downgrade(config, "0009")
        with engine.connect() as conn:
            assert "submission_files" in sa.inspect(conn).get_table_names()
            constraint = conn.execute(
                sa.text(
                    "SELECT pg_get_constraintdef(oid) FROM pg_constraint "
                    "WHERE conname = 'ck_admission_outcome'"
                )
            ).scalar_one()
            assert "'excluded'" not in constraint
        command.upgrade(config, "head")
    finally:
        engine.dispose()
