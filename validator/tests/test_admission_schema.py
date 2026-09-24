"""Migration-enforced append-only audit history."""

import pytest
from sqlalchemy import create_engine, text
from sqlalchemy.exc import DBAPIError
from sqlalchemy.orm import Session
from test_admission import stored_point
from test_db_schema import migrated  # noqa: F401

# pyright: reportUnusedImport=false
from db.admission import evaluate
from db.locks import publication_lock


def test_history_cannot_be_updated_or_deleted(migrated):  # noqa: F811
    engine = create_engine(migrated)
    try:
        with Session(engine) as session, session.begin():
            p = stored_point(session, 500, [1.0] * 3)
            publication_lock(session)
            check_id = evaluate(session, [p], compute=True, persist=True)[0].admission_check_id
        for statement in (
            "UPDATE submission_admission_checks SET outcome='dominated' WHERE id=:id",
            "DELETE FROM submission_admission_checks WHERE id=:id",
        ):
            with pytest.raises(DBAPIError, match="immutable"):
                with engine.begin() as conn:
                    conn.execute(text(statement), {"id": check_id})
    finally:
        engine.dispose()
