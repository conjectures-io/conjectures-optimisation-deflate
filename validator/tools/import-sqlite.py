#!/usr/bin/env python3
"""Move an existing SQLite queue into Postgres, once.

The service used to keep its submissions in one SQLite file. A validator upgrading
mid-round should not lose the queue, so this reads that file and inserts what it finds.

    python validator/tools/import-sqlite.py validator/.work/service.db [--dry-run]

Idempotent: a submission already present under the same (hotkey, digest) is left alone,
so a re-run after a partial import finishes the job rather than duplicating it.

Two things the old file cannot supply, and this does not invent:

  * raw bytes and absolute parse seconds. The old schema stored only the ratios, so
    imported submissions carry no Pareto point and are skipped by the scorer until the
    miner submits again. Their place on the byte leaderboard is unaffected.
  * entitlement claims. The old service had no registrations, so nothing was ever
    charged. Imported accepted submissions are NOT retro-charged -- pass
    --charge-accepted if you would rather they were, which requires the chain watcher to
    have already recorded the registrations they would spend.
"""

from __future__ import annotations

import argparse
import dataclasses
import sqlite3
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import cast

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

import db as store_pkg  # noqa: E402
from db import models  # noqa: E402
from db.registrations import NoSlot  # noqa: E402

# The states the old service used. They are the same strings, which is why the import is
# a copy rather than a translation.
STATES = {"queued", "verifying", "accepted", "rejected", "error"}


def parse_time(value: str | None) -> datetime | None:
    if not value:
        return None
    return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def rows_of(path: Path) -> list[sqlite3.Row]:
    conn = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    conn.row_factory = sqlite3.Row
    try:
        return conn.execute("SELECT * FROM submissions ORDER BY id").fetchall()
    finally:
        conn.close()


@dataclasses.dataclass
class Args:
    sqlite_db: Path = Path()
    dry_run: bool = False
    charge_accepted: bool = False


def main() -> None:
    ap = argparse.ArgumentParser(description=(__doc__ or "").split("\n")[0])
    ap.add_argument("sqlite_db", type=Path, help="the old service.db")
    ap.add_argument("--dry-run", action="store_true", help="report what would be imported")
    ap.add_argument(
        "--charge-accepted",
        action="store_true",
        help="also spend a registration for each imported accepted submission",
    )
    args = ap.parse_args(namespace=Args())

    if not args.sqlite_db.is_file():
        sys.exit(f"{args.sqlite_db} is not a file")

    rows = rows_of(args.sqlite_db)
    store = store_pkg.connect()
    imported = skipped = charged = 0
    try:
        for row in rows:
            state = row["state"] if row["state"] in STATES else "error"
            # A submission caught mid-gate by the migration belongs back on the queue:
            # the worker that was verifying it no longer exists.
            if state == "verifying":
                state = "queued"
            # sqlite3.Row indexes by column name with no static schema, so every field
            # read from it is cast to the type the old service's schema actually used.
            hotkey = cast("str | None", row["hotkey"])
            digest = cast(str, row["digest"])
            if not hotkey:
                print(f"  skipping {digest!r}: no hotkey (the old schema predates baselines)")
                skipped += 1
                continue
            submitted_at = parse_time(cast("str | None", row["submitted_at"]))
            if submitted_at is None:
                print(f"  skipping {hotkey[:8]}…: missing or unparseable submitted_at")
                skipped += 1
                continue
            with store_pkg.session_scope(store.sessions) as session:
                existing = (
                    session.query(models.Submission)
                    .filter_by(hotkey=hotkey, digest=digest)
                    .one_or_none()
                )
                if existing is not None:
                    skipped += 1
                    continue
                if args.dry_run:
                    imported += 1
                    continue
                new = models.Submission(
                    hotkey=hotkey,
                    digest=digest,
                    submitted_at=submitted_at,
                    state=state,
                    exit_code=row["exit_code"],
                    report=row["report"],
                    incumbent_bytes=row["incumbent_bytes"],
                    bytes=row["bytes"],
                    time_ratio=row["time_ratio"],
                )
                session.add(new)
                session.flush()
                imported += 1
                if args.charge_accepted and state == "accepted":
                    try:
                        store.registrations.claim_slot(session, hotkey, new.id)
                        charged += 1
                    except NoSlot:
                        print(f"  no registration to charge submission {new.id} to; left unpaid")
    finally:
        store.close()

    verb = "would import" if args.dry_run else "imported"
    print(f"{verb} {imported} submission(s), skipped {skipped} (already present or malformed)")
    if args.charge_accepted:
        print(f"charged {charged} registration(s)")
    if imported:
        print("submitted files stay where they are: SERVICE_FILES is unchanged by this import")


if __name__ == "__main__":
    main()
