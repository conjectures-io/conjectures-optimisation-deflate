"""Miner client: submit a parser and its proof, read the score, read the leaderboard.

python miner/submit.py submit my-submission --hotkey ~/.bittensor/wallets/w/hotkeys/h --url http://host:9200
python miner/submit.py status <submission id> --url …
python miner/submit.py leaderboard --url …
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path
from typing import NotRequired, TypedDict, cast

import requests

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "validator"))
from service import sig  # noqa: E402 - shared with the service so both hash and sign identically

TIMEOUT = 60


class SubmitResult(TypedDict):
    submission: int
    state: str
    digest: str
    # How many unclaimed registrations the hotkey has left. Absent from a service
    # that predates entitlements, so every read of it goes through .get().
    slots_remaining: NotRequired[int]


class StatusResult(TypedDict):
    id: int
    state: str
    submitted_at: str
    report: str | None
    bytes: int | None
    incumbent_bytes: int | None
    time_ratio: float | None


class LeaderboardEntry(TypedDict):
    rank: int
    bytes: int
    vs_incumbent: float | None
    time_ratio: float | None
    hotkey: str


class LeaderboardResult(TypedDict):
    incumbent_bytes: int | None
    speed_floor: float
    ranking: list[LeaderboardEntry]


def files_of(d: Path) -> tuple[bytes, bytes]:
    # The two files a submission is.
    rs, lean = d / "parse.rs", d / "Parse.lean"
    if not rs.is_file() or not lean.is_file():
        sys.exit(f"{d} must contain parse.rs and Parse.lean")
    return rs.read_bytes(), lean.read_bytes()


def cmd_submit(args: argparse.Namespace) -> None:
    # Hash the files, sign (hash, hotkey, now), upload; print the submission id.
    d, hotkey, url = cast(str, args.dir), cast(str, args.hotkey), cast(str, args.url)
    rs, lean = files_of(Path(d))
    kp = sig.load_keypair(hotkey)
    digest = sig.digest_of(rs, lean)
    # The timestamp is part of what is signed: the service refuses a signature more than
    # a few minutes from its own clock, so a captured upload cannot be replayed later. A
    # machine whose clock is badly wrong will be refused -- that is the check working.
    timestamp = int(time.time())
    r = requests.post(
        f"{url}/submit",
        data={
            "hotkey": kp.ss58_address,
            "signature": sig.sign(kp, sig.submit_message(digest, kp.ss58_address, timestamp)),
            "timestamp": timestamp,
        },
        files={"parse.rs": ("parse.rs", rs), "Parse.lean": ("Parse.lean", lean)},
        timeout=TIMEOUT,
    )
    if r.status_code != 200:
        detail: object = r.text
        if r.headers.get("content-type", "").startswith("application/json"):
            detail = cast("dict[str, object]", r.json()).get("detail", r.text)
        reason: object = detail
        if isinstance(detail, dict):
            nested = cast("dict[str, object]", detail)
            reason = nested.get("reason", nested)
        sys.exit(f"submit refused ({r.status_code}): {reason}")
    s = cast(SubmitResult, r.json())
    print(f"submission {s['submission']} {s['state']}  digest {digest}")
    if (left := s.get("slots_remaining")) is not None:
        print(f"{left} registration slot(s) left; one registration buys one accepted submission")
    print(f"check with: submit.py status {s['submission']} --url {url}")


def cmd_status(args: argparse.Namespace) -> None:
    # Print a submission's state, and its report and score once verified.
    sub_id, url = cast(int, args.id), cast(str, args.url)
    r = requests.get(f"{url}/submissions/{sub_id}", timeout=TIMEOUT)
    if r.status_code != 200:
        sys.exit(f"{r.status_code}: {r.text}")
    s = cast(StatusResult, r.json())
    print(f"submission {s['id']}  state {s['state']}  submitted {s['submitted_at']}")
    if s["report"]:
        print(s["report"])
    if s["bytes"] and s["incumbent_bytes"]:
        ratio = s["bytes"] / s["incumbent_bytes"]
        print(f"bytes {s['bytes']}  vs incumbent {ratio:.5f}x  time {s['time_ratio']}x")


def cmd_leaderboard(args: argparse.Namespace) -> None:
    # Print the ranking.
    url = cast(str, args.url)
    r = requests.get(f"{url}/leaderboard", timeout=TIMEOUT)
    if r.status_code != 200:
        sys.exit(f"{r.status_code}: {r.text}")
    b = cast(LeaderboardResult, r.json())
    print(f"incumbent {b['incumbent_bytes']} bytes; speed floor {b['speed_floor']}x")
    if not b["ranking"]:
        print("leaderboard: empty")
        return
    print(f"{'rank':>4} {'bytes':>10} {'vs incumbent':>13} {'time':>6}  hotkey")
    for x in b["ranking"]:
        head = f"{x['rank']:>4} {x['bytes']:>10} {x['vs_incumbent']:>12}x"
        print(f"{head} {x['time_ratio']:>5.2f}x  {x['hotkey']}")


CMDS = {"submit": cmd_submit, "status": cmd_status, "leaderboard": cmd_leaderboard}


def main() -> None:
    # Dispatch a subcommand.
    ap = argparse.ArgumentParser(prog="submit.py", description=(__doc__ or "").split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("submit")
    p.add_argument("dir", help="submission directory with parse.rs and Parse.lean")
    p.add_argument("--hotkey", required=True, help="Bittensor hotkey file (or //Alice for tests)")
    p.add_argument("--url", required=True, help="service URL, e.g. http://host:9200")
    st = sub.add_parser("status")
    st.add_argument("id", type=int)
    st.add_argument("--url", required=True)
    lb = sub.add_parser("leaderboard")
    lb.add_argument("--url", required=True)
    args = ap.parse_args()
    CMDS[cast(str, args.cmd)](args)


if __name__ == "__main__":
    main()
