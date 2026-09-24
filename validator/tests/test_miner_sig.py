"""The miner's half of the platform's submission contract, pinned to the exact bytes.

conjectures-validator rebuilds the signed message from the request it received and checks
the signature against that. A one-character difference -- a space, a line ending, a field
order -- refuses every submission as a bad signature, and nothing short of a live submit
would say why. So the golden message here is the platform's format written out by hand; if
either side changes it, this fails before a miner does.

The request-shape tests matter for a different reason: the scalars must travel as
`X-Conjectures-*` headers, never as form fields. The platform relies on those headers being
un-allowlisted for CORS to keep the signed endpoint out of a browser's reach, so a client
that put them in the form would not merely be refused -- it would be asking the platform to
give up that property.
"""

from __future__ import annotations

import sys
from argparse import Namespace
from pathlib import Path
from types import SimpleNamespace

import pytest

MINER = Path(__file__).resolve().parent.parent.parent / "miner"
sys.path.insert(0, str(MINER))

import sig  # noqa: E402
import submit  # noqa: E402

RUST = b"pub fn parse() {}\n"
LEAN = b"theorem ok : True := trivial\n"


def test_the_message_is_the_platforms_format_byte_for_byte():
    # Written out by hand from conjectures-validator's submission_api/competition_sig.py.
    expected = (
        "conjectures-competition-submit-v1\n"
        "competition: miniz-oxide\n"
        "digest: abc123\n"
        "hotkey: 5Hot\n"
        "timestamp: 1700000000"
    )
    assert (
        sig.submit_message(
            competition="miniz-oxide", digest="abc123", hotkey="5Hot", timestamp=1700000000
        )
        == expected
    )


def test_the_competition_is_part_of_what_is_signed():
    """A signature for one competition must not verify for another."""
    kp = sig.load_keypair("//Alice")
    digest = sig.digest_of(RUST, LEAN)
    here = sig.submit_message(
        competition="miniz-oxide", digest=digest, hotkey=kp.ss58_address, timestamp=1
    )
    there = sig.submit_message(
        competition="rust-competition", digest=digest, hotkey=kp.ss58_address, timestamp=1
    )
    signature = bytes.fromhex(sig.sign(kp, here))
    assert kp.verify(here.encode(), signature)
    assert not kp.verify(there.encode(), signature)


def test_the_digest_is_sha256_of_the_two_files_in_order():
    import hashlib

    assert sig.digest_of(RUST, LEAN) == hashlib.sha256(RUST + LEAN).hexdigest()
    # Order is part of it: the platform hashes parse.rs first.
    assert sig.digest_of(RUST, LEAN) != sig.digest_of(LEAN, RUST)


class _Response:
    def __init__(self, status: int, body: dict[str, object]) -> None:
        self.status_code = status
        self._body = body
        self.headers = {"content-type": "application/json"}
        self.text = str(body)

    def json(self) -> dict[str, object]:
        return self._body


def _submission(tmp_path: Path) -> Path:
    d = tmp_path / "entry"
    d.mkdir()
    (d / "parse.rs").write_bytes(RUST)
    (d / "Parse.lean").write_bytes(LEAN)
    return d


def test_submit_signs_in_headers_and_targets_the_competition(tmp_path, monkeypatch, capsys):
    urls: list[str] = []
    sent_headers: dict[str, str] = {}
    sent_files: dict[str, tuple[str, bytes]] = {}
    rest: dict[str, object] = {}

    def post(
        url: str,
        *,
        headers: dict[str, str],
        files: dict[str, tuple[str, bytes]],
        **kwargs: object,
    ) -> _Response:
        urls.append(url)
        sent_headers.update(headers)
        sent_files.update(files)
        rest.update(kwargs)
        return _Response(
            201,
            {
                "competition": "miniz-oxide",
                "submission": "7",
                "state": "queued",
                "digest": sig.digest_of(RUST, LEAN),
                "created": True,
                "slots_remaining": 0,
            },
        )

    # By name: submit.py looks both up at call time, and reaching them through `submit.` would
    # lean on its imports being part of its interface.
    monkeypatch.setattr("requests.post", post)
    monkeypatch.setattr(submit, "time", SimpleNamespace(time=lambda: 1_700_000_000))
    submit.cmd_submit(
        Namespace(
            dir=str(_submission(tmp_path)),
            hotkey="//Alice",
            url="https://api.example/",
            competition="miniz-oxide",
        )
    )

    assert urls == ["https://api.example/v1/competitions/miniz-oxide/submissions"]
    # Nothing scalar in the body: the form carries the two files and nothing else.
    assert "data" not in rest
    assert set(sent_files) == {"parse.rs", "Parse.lean"}
    headers = sent_headers
    kp = sig.load_keypair("//Alice")
    assert headers["X-Conjectures-Hotkey"] == kp.ss58_address
    assert headers["X-Conjectures-Timestamp"] == "1700000000"
    # The signature verifies over exactly the message the platform will rebuild.
    rebuilt = sig.submit_message(
        competition="miniz-oxide",
        digest=sig.digest_of(RUST, LEAN),
        hotkey=kp.ss58_address,
        timestamp=1_700_000_000,
    )
    assert kp.verify(rebuilt.encode(), bytes.fromhex(headers["X-Conjectures-Signature"]))
    assert "submission 7 queued" in capsys.readouterr().out


def test_a_refusal_reports_the_platforms_reason_code(tmp_path, monkeypatch):
    def post(url: str, **kwargs: object) -> _Response:
        return _Response(
            402,
            {
                "type": "about:blank",
                "title": "Payment not confirmed",
                "status": 402,
                "detail": "this hotkey is not registered on the subnet",
                "reason_code": "NOT_REGISTERED",
            },
        )

    monkeypatch.setattr("requests.post", post)
    with pytest.raises(SystemExit) as exited:
        submit.cmd_submit(
            Namespace(
                dir=str(_submission(tmp_path)),
                hotkey="//Alice",
                url="https://api.example",
                competition="miniz-oxide",
            )
        )
    assert "402 NOT_REGISTERED" in str(exited.value)
    assert "not registered" in str(exited.value)


def test_the_leaderboard_follows_every_page(monkeypatch, capsys):
    pages: dict[str | None, dict[str, object]] = {
        None: {
            "ranked_by": "bytes",
            "headline": {"incumbent_bytes": 2153387, "speed_floor": 8.0},
            "ranking": [
                {
                    "rank": 1,
                    "submission": "1",
                    "hotkey": "5First",
                    "metrics": {"bytes": 2100000, "vs_incumbent": 0.97519, "time_ratio": 1.5},
                },
            ],
            "next_cursor": "page-two",
        },
        "page-two": {
            "ranked_by": "bytes",
            "headline": {"incumbent_bytes": 2153387, "speed_floor": 8.0},
            "ranking": [
                {
                    "rank": 2,
                    "submission": "2",
                    "hotkey": "5Second",
                    "metrics": {"bytes": 2200000, "vs_incumbent": 1.02165, "time_ratio": None},
                },
            ],
            "next_cursor": None,
        },
    }
    asked: list[str | None] = []

    def get(url: str, params: dict[str, str | None], **kw: object) -> _Response:
        assert url == "https://api.example/v1/competitions/miniz-oxide/leaderboard"
        asked.append(params.get("cursor"))
        return _Response(200, pages[params.get("cursor")])

    monkeypatch.setattr("requests.get", get)
    submit.cmd_leaderboard(Namespace(url="https://api.example", competition="miniz-oxide"))
    out = capsys.readouterr().out
    assert asked == [None, "page-two"]
    assert "5First" in out and "5Second" in out
