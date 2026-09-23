"""A scratch Postgres database per test session, and the fixtures built on it.

The store is Postgres, so the tests use Postgres: DISTINCT ON, FOR UPDATE ... SKIP
LOCKED, ON CONFLICT ... RETURNING and the entitlement race are the parts most worth
testing and none of them exist on SQLite. `just db-up` provides the server; each session
creates its own database on it and drops it afterwards, so a run never disturbs a
validator's real one.

Every database test skips itself when no server is reachable, so `pytest validator/tests`
still runs the gate's own tests on a machine with no Docker.
"""

from __future__ import annotations

import os
import sys
import uuid
from collections.abc import Callable, Iterator
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import TypedDict

import pytest
import sqlalchemy as sa

VALIDATOR = Path(__file__).resolve().parent.parent
REPO = VALIDATOR.parent
if str(VALIDATOR) not in sys.path:
    sys.path.insert(0, str(VALIDATOR))

import db as store_pkg  # noqa: E402
from db import models  # noqa: E402

T0 = datetime(2026, 10, 1, 12, 0, tzinfo=timezone.utc)


def _admin_url() -> str:
    # The server's maintenance database, used only to CREATE/DROP the scratch one.
    user = os.getenv("POSTGRES_USER", "conjectures")
    password = os.getenv("POSTGRES_PASSWORD", "conjectures")
    host = os.getenv("POSTGRES_HOST", "localhost")
    port = os.getenv("POSTGRES_PORT", "5432")
    return f"postgresql+psycopg://{user}:{password}@{host}:{port}/postgres"


def _scratch_url(name: str) -> str:
    return _admin_url().rsplit("/", 1)[0] + f"/{name}"


@pytest.fixture(scope="session")
def database_url() -> Iterator[str]:
    """Create a scratch database for this session; drop it at the end.

    Skips the whole database suite when no server answers, rather than failing: the
    gate's own tests must still run on a machine without Docker.
    """
    name = f"conjectures_test_{uuid.uuid4().hex[:10]}"
    try:
        admin = sa.create_engine(_admin_url(), isolation_level="AUTOCOMMIT")
        with admin.connect() as conn:
            conn.execute(sa.text(f'CREATE DATABASE "{name}"'))
    except Exception as exc:  # noqa: BLE001 - no server, wrong password, no permission
        pytest.skip(f"no Postgres for the store tests ({exc.__class__.__name__}); try `just db-up`")
    url = _scratch_url(name)
    try:
        engine = sa.create_engine(url)
        models.Base.metadata.create_all(engine)
        engine.dispose()
        yield url
    finally:
        with admin.connect() as conn:
            # Terminate leftover connections first, or the DROP blocks on them.
            conn.execute(
                sa.text(
                    "SELECT pg_terminate_backend(pid) FROM pg_stat_activity "
                    "WHERE datname = :n AND pid <> pg_backend_pid()"
                ),
                {"n": name},
            )
            conn.execute(sa.text(f'DROP DATABASE IF EXISTS "{name}"'))
        admin.dispose()


class Clock(TypedDict):
    """A settable clock: `t` is what db.clock.now returns, `tick` moves it."""

    t: datetime
    tick: Callable[..., None]


@pytest.fixture
def clock(monkeypatch: pytest.MonkeyPatch) -> Clock:
    # A settable clock, so submissions can be ordered without sleeping.
    state: Clock = {"t": T0, "tick": lambda *_: None}
    monkeypatch.setattr(store_pkg.clock, "now", lambda: state["t"])

    def tick(seconds: float = 1.0) -> None:
        state["t"] = state["t"] + timedelta(seconds=seconds)

    state["tick"] = tick
    return state


@pytest.fixture
def store(database_url, clock):
    """A clean store: every table truncated, so tests cannot leak into each other."""
    s = store_pkg.connect(database_url, rate_limit=10, rate_window_seconds=60)
    with s.engine.begin() as conn:
        names = [t.name for t in reversed(models.Base.metadata.sorted_tables)]
        tables = ", ".join(f'"{n}"' for n in names)
        conn.execute(sa.text(f"TRUNCATE {tables} RESTART IDENTITY CASCADE"))
    try:
        yield s
    finally:
        s.close()


def register(store, hotkey: str, *, uid: int = 0, block: int = 1000) -> int:
    """Put one registration row in, as the chain watcher would. Returns its id.

    One of these is one submission slot -- the tests spend them the same way a miner does.
    """
    with store_pkg.session_scope(store.sessions) as session:
        row = models.Registration(
            uid=uid,
            ss58_hot=hotkey,
            ss58_cold=f"cold-{hotkey[:8]}",
            block=block,
            block_date=T0 - timedelta(days=1),
        )
        session.add(row)
        session.flush()
        return int(row.id)


# ── The service under test ────────────────────────────────────────────────

STUB_VERIFIER = """
import json, sys
from pathlib import Path
rs = (Path(sys.argv[1]) / "parse.rs").read_text()
if "MISCONFIGURED" in rs:
    print("VALIDATOR ERROR\\n  stub"); sys.exit(2)
if "REJECT" in rs:
    print("REJECTED at stage 4 (statement)\\n  stub"); sys.exit(1)
n = int(rs.split("BYTES=")[1].split()[0]) if "BYTES=" in rs else 2000000
t = float(rs.split("SECONDS=")[1].split()[0]) if "SECONDS=" in rs else 0.100
Path(sys.argv[sys.argv.index("--results") + 1]).write_text(json.dumps({
    "schema_version": 4,
    "corpus": {"name": "corpus-initial", "public": True},
    "candidates": ["submission"],
    "raw_bytes": 8060939,
    "speed_floor": 8.0,
    "methods": {
        "incumbent": {"external": False, "output_bytes": 2153387, "parse_s": 0.025,
                      "total_s": 0.025, "errors": []},
        "submission": {"external": False, "output_bytes": n, "parse_s": t, "total_s": t,
                       "ratio": n / 2153387, "slowdown": t / 0.025,
                       "accepted": True, "improved": n < 2153387, "errors": []},
    },
}))
print(f"TOTAL                         8060939     2153387     {n}")
print(f"parse time 0.025s incumbent, {t}s submission ({t / 0.025:.2f}x)")
print("ACCEPTED"); sys.exit(0)
"""


@pytest.fixture
def settings(tmp_path, monkeypatch):
    # Files under the test's own directory; everything else at its default.
    from service.settings import Settings

    return Settings(files=tmp_path / "submissions", worker_id="test-worker")


@pytest.fixture
def stub_verifier(tmp_path, monkeypatch, store):
    # Stand in for the six-stage gate, so the service tests need no toolchain. The stub
    # writes the same `--results` JSON the real gate does, which is what the worker
    # reads; the TOTAL and `parse time` lines are there because the report is still a
    # human document the tests assert on.
    from service import worker as worker_mod

    path = tmp_path / "verify.py"
    path.write_text(STUB_VERIFIER)
    monkeypatch.setattr(worker_mod, "VERIFY", path)
    original = worker_mod.run_gate

    def run_gate(directory, results, claim=None, attempt=None):
        result = original(directory, results, claim, attempt)
        if result.returncode == 0 and worker_mod.VERIFY == path:
            # The stub stands in for all successful verification milestones too.
            from verifier.identity import fingerprint

            sid = int(directory.name)
            token, _ = store.verification.begin(
                sid,
                (directory / "parse.rs").read_bytes(),
                (directory / "Parse.lean").read_bytes(),
                fingerprint(),
                expected_claim=claim,
                expected_attempt=attempt,
            )
            for stage in ("static", "lean", "measured"):
                store.verification.publish(sid, token, stage)
        return result

    original_finish = store.submissions.finish

    def finish(*args, **kwargs):
        state = original_finish(*args, **kwargs)
        if state == "accepted":
            attach_aggregation(store, args[0])
        return state

    monkeypatch.setattr(store.submissions, "finish", finish)
    monkeypatch.setattr(worker_mod, "run_gate", run_gate)
    return path


@pytest.fixture
def client(store, settings, stub_verifier):
    from fastapi.testclient import TestClient

    from service.api import create_app

    with TestClient(app=create_app(settings, store)) as c:
        yield c


@pytest.fixture
def drain(store, settings, stub_verifier):
    # Run the gate worker over the queue once, as the standalone process would.
    from service import worker as worker_mod

    def run() -> int:
        return worker_mod.drain(store, settings)

    return run


def submission_files(tmp: Path, name: str, marker: str = "") -> Path:
    # A copy of the reference template, with a marker line the stub verifier reads.
    import shutil

    d = tmp / name
    shutil.copytree(REPO / "miner/template", d)
    if marker:
        (d / "parse.rs").write_text((d / "parse.rs").read_text() + f"\n// {marker}\n")
    return d


def post_submission(client, kp, d: Path, *, signer=None, timestamp: int | None = None, files=None):
    """Sign a submission's digest and post it. Returns the raw response.

    `signer`, `timestamp` and `files` are the seams the security tests pull on: signing
    with the wrong key, with a stale clock, or over different bytes than are uploaded.
    """
    from service import sig

    rs, lean = (d / "parse.rs").read_bytes(), (d / "Parse.lean").read_bytes()
    stamp = int(datetime.now(timezone.utc).timestamp()) if timestamp is None else timestamp
    digest = sig.digest_of(*(files or (rs, lean)))
    return client.post(
        "/submit",
        data={
            "hotkey": kp.ss58_address,
            "signature": sig.sign(signer or kp, sig.submit_message(digest, kp.ss58_address, stamp)),
            "timestamp": stamp,
        },
        files={"parse.rs": ("parse.rs", rs), "Parse.lean": ("Parse.lean", lean)},
    )


def attach_aggregation(store, sid):
    """Test gate evidence mirrors the production DB publication path."""
    import copy

    from test_bench_storage import evidence

    from bench.storage import sha256
    from db.aggregation import aggregate, publish

    with store.sessions.begin() as session:
        sub = session.get(models.Submission, sid)
        raw = copy.deepcopy(evidence())
        raw[0]["methods"]["candidate"]["source_sha256"] = sub.source_sha256
        raw[0]["measured_rounds"] = 2
        raw[0]["benchmark_provenance"] = {
            "engine_sha256": "1" * 64,
            "template_sha256": "2" * 64,
            "host_sha256": "3" * 64,
        }
        raw[1]["raw_bytes"] = sub.raw_bytes
        for name, size, seconds in (
            ("candidate", sub.bytes, sub.parse_seconds),
            ("incumbent", sub.incumbent_bytes, sub.incumbent_seconds),
        ):
            raw[1]["methods"][name]["output_bytes"] = size
            raw[1]["methods"][name]["reps"] = [
                {
                    "phase": "measured",
                    "order_index": i,
                    "time_s": seconds,
                    "encode_s": 0.0,
                    "total_s": seconds,
                }
                for i in range(2)
            ]
        row = models.BenchmarkRun(
            source_sha256=sub.source_sha256,
            candidate_method="candidate",
            corpus="tiny",
            corpus_sha256=sha256([("a.txt", "c" * 64, sub.raw_bytes)]),
            status="complete",
            raw_data=raw,
        )
        session.add(row)
        session.flush()
        result = aggregate(session, [row])
        publish(session, sid, result.id)
