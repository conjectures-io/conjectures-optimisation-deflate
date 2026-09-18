"""Alembic environment.

Resolves the database URL the same way validator/db/engine.py does, and points
autogenerate at the SQLAlchemy models, which are the schema's source of truth.
"""

from __future__ import annotations

import os
import sys
from logging.config import fileConfig
from pathlib import Path

from alembic import context
from sqlalchemy import engine_from_config, pool

# The models live in validator/db, which is not an installed package: the repo puts
# validator/ on the path instead (the same way `cd validator && python -m service.api`
# does). In the migration image that directory is /app/validator.
REPO = Path(__file__).resolve().parents[3]
for candidate in (REPO / "validator", Path("/app/validator")):
    if candidate.is_dir() and str(candidate) not in sys.path:
        sys.path.insert(0, str(candidate))

from db.models import Base  # noqa: E402 - must follow the sys.path setup above

config = context.config

if config.config_file_name is not None:
    fileConfig(config.config_file_name)

target_metadata = Base.metadata


def _database_url() -> str:
    url = os.getenv("DATABASE_URL")
    if url:
        return url
    user = os.getenv("POSTGRES_USER", "conjectures")
    password = os.getenv("POSTGRES_PASSWORD", "conjectures")
    host = os.getenv("POSTGRES_HOST", "localhost")
    port = os.getenv("POSTGRES_PORT", "5432")
    name = os.getenv("POSTGRES_DB", "conjectures")
    return f"postgresql+psycopg://{user}:{password}@{host}:{port}/{name}"


def run_migrations_offline() -> None:
    context.configure(
        url=_database_url(),
        target_metadata=target_metadata,
        literal_binds=True,
        dialect_opts={"paramstyle": "named"},
        compare_type=True,
        compare_server_default=True,
    )
    with context.begin_transaction():
        context.run_migrations()


def run_migrations_online() -> None:
    section = config.get_section(config.config_ini_section, {})
    section["sqlalchemy.url"] = _database_url()
    connectable = engine_from_config(section, prefix="sqlalchemy.", poolclass=pool.NullPool)
    with connectable.connect() as connection:
        context.configure(
            connection=connection,
            target_metadata=target_metadata,
            compare_type=True,
            compare_server_default=True,
        )
        with context.begin_transaction():
            context.run_migrations()


if context.is_offline_mode():
    run_migrations_offline()
else:
    run_migrations_online()
