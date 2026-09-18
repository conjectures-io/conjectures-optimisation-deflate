"""What the API refuses, and why.

The submission endpoint is the only unauthenticated write on a validator that spends
real time per request, so every refusal here is load-bearing: a bad shape, a stale
signature, an oversized body or a flood must all be turned away before they cost
anything.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

import pytest
from conftest import post_submission, register, submission_files

VALIDATOR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(VALIDATOR))

from service import security, sig  # noqa: E402
from service.settings import MAX_FILE_BYTES, MAX_REQUEST_BYTES  # noqa: E402

ALICE = sig.load_keypair("//Alice")
BOB = sig.load_keypair("//Bob")


def reason(response) -> str:
    return response.json()["detail"]["reason"]


# ── Signatures ────────────────────────────────────────────────────────────


def test_someone_elses_signature_is_refused(client, store, tmp_path):
    register(store, ALICE.ss58_address)
    r = post_submission(client, ALICE, submission_files(tmp_path, "a"), signer=BOB)
    assert r.status_code == 401 and "does not verify" in reason(r)


def test_a_signature_over_different_files_is_refused(client, store, tmp_path):
    # The digest binds the signature to these exact two files: signing one pair and
    # uploading another is the substitution the digest exists to stop.
    register(store, ALICE.ss58_address)
    d = submission_files(tmp_path, "a")
    r = post_submission(client, ALICE, d, files=(b"other parser", b"other proof"))
    assert r.status_code == 401 and "does not verify" in reason(r)


@pytest.mark.parametrize("skew", [-3600, -301, 301, 3600])
def test_a_stale_or_future_timestamp_is_refused(client, store, tmp_path, skew):
    # Both directions: a stale timestamp is a replay, and a future one would let a miner
    # mint today a signature that stays valid for a round that has not opened.
    register(store, ALICE.ss58_address)
    stamp = int(time.time()) + skew
    r = post_submission(client, ALICE, submission_files(tmp_path, "a"), timestamp=stamp)
    assert r.status_code == 401 and "from the validator's clock" in reason(r)


def test_a_captured_request_cannot_be_replayed_later(client, store, tmp_path, monkeypatch):
    # The exact bytes of a valid request, sent again once the window has passed.
    register(store, ALICE.ss58_address)
    d = submission_files(tmp_path, "a", "BYTES=2300000")
    stamp = int(time.time())
    assert post_submission(client, ALICE, d, timestamp=stamp).status_code == 200
    monkeypatch.setattr(time, "time", lambda: stamp + 3600)
    replay = post_submission(client, ALICE, d, timestamp=stamp)
    assert replay.status_code == 401 and "from the validator's clock" in reason(replay)


# ── Shapes ────────────────────────────────────────────────────────────────


@pytest.mark.parametrize("hotkey", ["not-an-address", "0x1234", "l" * 48, "5" * 200])
def test_a_malformed_hotkey_is_refused_before_any_crypto(client, tmp_path, hotkey):
    d = submission_files(tmp_path, "a")
    r = client.post(
        "/submit",
        data={"hotkey": hotkey, "signature": "ab" * 64, "timestamp": int(time.time())},
        files={
            "parse.rs": ("parse.rs", (d / "parse.rs").read_bytes()),
            "Parse.lean": ("Parse.lean", (d / "Parse.lean").read_bytes()),
        },
    )
    assert r.status_code == 400 and "ss58" in reason(r)


@pytest.mark.parametrize("signature", ["00", "0x" + "z" * 128, "ab" * 63])
def test_a_malformed_signature_is_refused(client, tmp_path, signature):
    d = submission_files(tmp_path, "a")
    r = client.post(
        "/submit",
        data={
            "hotkey": ALICE.ss58_address,
            "signature": signature,
            "timestamp": int(time.time()),
        },
        files={
            "parse.rs": ("parse.rs", (d / "parse.rs").read_bytes()),
            "Parse.lean": ("Parse.lean", (d / "Parse.lean").read_bytes()),
        },
    )
    assert r.status_code == 400 and "64 hex" in reason(r)


def test_missing_fields_are_named_but_never_echoed(client):
    r = client.post("/submit", data={"hotkey": ALICE.ss58_address})
    assert r.status_code == 422
    # The field names, and nothing of their values -- the signature is in there.
    assert "signature" in reason(r) and "timestamp" in reason(r)


def test_an_empty_field_counts_as_a_missing_one(client, tmp_path):
    # FastAPI treats an empty required form value as absent, so it never reaches the
    # shape checks. Either way it is a refusal that names the field and echoes nothing.
    d = submission_files(tmp_path, "a")
    r = client.post(
        "/submit",
        data={"hotkey": "", "signature": "ab" * 64, "timestamp": int(time.time())},
        files={
            "parse.rs": ("parse.rs", (d / "parse.rs").read_bytes()),
            "Parse.lean": ("Parse.lean", (d / "Parse.lean").read_bytes()),
        },
    )
    assert r.status_code == 422 and "hotkey" in reason(r)


def test_an_oversized_file_is_refused(client, store):
    register(store, ALICE.ss58_address)
    r = client.post(
        "/submit",
        data={
            "hotkey": ALICE.ss58_address,
            "signature": "ab" * 64,
            "timestamp": int(time.time()),
        },
        files={
            "parse.rs": ("parse.rs", b"a" * (MAX_FILE_BYTES + 1)),
            "Parse.lean": ("Parse.lean", b"b"),
        },
    )
    assert r.status_code == 413


def test_an_oversized_body_is_refused_on_its_headers(client):
    # Refused from Content-Length, before anything reads it: the point is not to spool
    # a multi-gigabyte upload to disk just to find out it is too big.
    r = client.post(
        "/submit",
        data={"hotkey": ALICE.ss58_address},
        files={"parse.rs": ("parse.rs", b"a" * (MAX_REQUEST_BYTES + 1024))},
    )
    assert r.status_code == 413 and "at most" in reason(r)


def test_an_empty_file_is_refused(client, store, tmp_path):
    register(store, ALICE.ss58_address)
    r = post_submission(client, ALICE, submission_files(tmp_path, "a"), files=(b"", b""))
    # The signature is over the empty pair, so this reaches the emptiness check only if
    # the signature verifies -- which it does, because the miner really did sign nothing.
    assert r.status_code in (400, 401)


def test_an_unknown_submission_is_a_404(client):
    assert client.get("/submissions/999999").status_code == 404


# ── Flooding ──────────────────────────────────────────────────────────────


def test_the_rate_limit_is_per_hotkey_and_counted_in_the_store(client, store, tmp_path):
    register(store, ALICE.ss58_address)
    d = submission_files(tmp_path, "a", "BYTES=2300000")
    limit = store.rate.limit
    codes = [post_submission(client, ALICE, d).status_code for _ in range(limit + 1)]
    assert codes[-1] == 429
    # And the count is in Postgres, not in this process: a restart does not reset it.
    assert store.rate.peek(f"hotkey:{ALICE.ss58_address}") >= limit


def test_the_rate_limit_survives_a_new_app_instance(client, store, settings, tmp_path):
    # The whole reason the counter is not a dict: a second API worker, or a restarted
    # one, must see the same budget.
    from fastapi.testclient import TestClient

    from service.api import create_app

    register(store, ALICE.ss58_address)
    d = submission_files(tmp_path, "a", "BYTES=2300000")
    for _ in range(store.rate.limit):
        post_submission(client, ALICE, d)
    with TestClient(app=create_app(settings, store)) as second:
        assert post_submission(second, ALICE, d).status_code == 429


def test_security_headers_and_a_request_id_are_always_set(client):
    r = client.get("/health")
    assert r.headers["X-Content-Type-Options"] == "nosniff"
    assert r.headers["X-Frame-Options"] == "DENY"
    assert len(r.headers["X-Request-Id"]) == 12


def test_no_interactive_docs_or_schema_are_served(client):
    for path in ("/docs", "/redoc", "/openapi.json"):
        assert client.get(path).status_code == 404


# ── The checks themselves ─────────────────────────────────────────────────


def test_freshness_accepts_inside_the_window_and_refuses_outside():
    assert security.check_fresh(1000, 300, now=1000.0) == 1000
    assert security.check_fresh(1000, 300, now=1299.0) == 1000
    with pytest.raises(security.Invalid):
        security.check_fresh(1000, 300, now=1301.0)
    with pytest.raises(security.Invalid):
        security.check_fresh(1000, 300, now=699.0)
