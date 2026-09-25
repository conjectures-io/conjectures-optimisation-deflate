"""Miner client: submit a parser and its proof, read the score, read the leaderboard.

Talks to conjectures-validator, which serves every competition from one API under
`/v1/competitions/{slug}`. `--url` is that API's origin; `--competition` picks the
competition and defaults to this one.

python miner/submit.py submit my-submission --hotkey ~/.bittensor/wallets/w/hotkeys/h --url https://api.host
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sig  # noqa: E402 - the platform's signing contract, pinned by test_miner_sig.py

TIMEOUT = 60
DEFAULT_COMPETITION = "lz77"
# The API caps a page at 100; asking for the most means the fewest round trips.
PAGE = 100


# The platform's competition surface is generic across competitions: ids are opaque strings,
# and a competition's measurements travel as `metrics`, keyed by the metric keys it declares at
# GET /v1/competitions/{slug}. This competition's are bytes, vs_incumbent, ratio_pct,
# time_ratio and compression_seconds.
Metrics = dict[str, "int | float | None"]


class SubmitResult(TypedDict):
    competition: str
    submission: str
    state: str
    digest: str
    # False when these exact files were already queued: the retry got the same submission.
    created: bool
    # How many more this hotkey could queue right now: unclaimed registrations minus what
    # is already queued. A queued submission has not spent one yet -- only acceptance does.
    slots_remaining: int | None


class StatusResult(TypedDict):
    id: str
    hotkey: str
    state: str
    submitted_at: str
    metrics: Metrics


class ApiAdmission(TypedDict):
    outcome: str | None
    reason_code: str | None


class ApiSubmission(TypedDict):
    id: str
    gate_status: str
    submitted_at: str
    metrics: Metrics | None
    admission: ApiAdmission
    score: dict[str, object] | None


class ApiStatus(TypedDict):
    submission: ApiSubmission


class ApiRank(TypedDict):
    rank: int
    hotkey: str
    payable_weight: float
    combined_weight: float


class ApiBoard(TypedDict):
    context: dict[str, object]
    ranking: list[ApiRank]
    next_cursor: str | None


class ReportResult(TypedDict):
    report: str | None


class LeaderboardEntry(TypedDict):
    rank: int
    submission: str
    hotkey: str
    metrics: Metrics


class LeaderboardPage(TypedDict):
    ranked_by: str
    # This competition's: incumbent_bytes (the bar) and speed_floor.
    headline: Metrics
    ranking: list[LeaderboardEntry]
    next_cursor: NotRequired[str | None]


def base(url: str, competition: str) -> str:
    return f"{url.rstrip('/')}/v1/competitions/{competition}"


def refused(what: str, r: requests.Response) -> str:
    """One line a miner can act on, from the platform's problem body.

    `reason_code` is the stable part (NOT_REGISTERED, NO_ENTITLEMENT, SIGNATURE_EXPIRED,
    RATE_LIMITED, SUBMISSIONS_PAUSED, ...); `detail` is the sentence explaining it.
    """
    content_type = r.headers.get("content-type", "")
    if content_type.startswith(("application/json", "application/problem+json")):
        body = cast("dict[str, object]", r.json())
        code, detail = body.get("reason_code"), body.get("detail")
        if code or detail:
            return f"{what} refused ({r.status_code} {code}): {detail}"
    return f"{what} refused ({r.status_code}): {r.text[:300]}"


def files_of(d: Path) -> tuple[bytes, bytes]:
    # The two files a submission is.
    rs, lean = d / "parse.rs", d / "Parse.lean"
    if not rs.is_file() or not lean.is_file():
        sys.exit(f"{d} must contain parse.rs and Parse.lean")
    return rs.read_bytes(), lean.read_bytes()


def signed_headers(
    kp: sig.Keypair, *, competition: str, digest: str, timestamp: int
) -> dict[str, str]:
    """The three headers that authorise one submission.

    Headers rather than form fields, because the platform requires it: multipart form data is
    a CORS-safelisted content type, so fields there would make the endpoint reachable from a
    browser, and the `X-Conjectures-*` headers are exactly what keeps it unreachable.
    """
    message = sig.submit_message(
        competition=competition, digest=digest, hotkey=kp.ss58_address, timestamp=timestamp
    )
    return {
        "X-Conjectures-Hotkey": kp.ss58_address,
        "X-Conjectures-Timestamp": str(timestamp),
        "X-Conjectures-Signature": sig.sign(kp, message),
    }


def cmd_submit(args: argparse.Namespace) -> None:
    # Hash the files, sign (competition, hash, hotkey, now), upload; print the submission id.
    d, hotkey = cast(str, args.dir), cast(str, args.hotkey)
    url, competition = cast(str, args.url), cast(str, args.competition)
    rs, lean = files_of(Path(d))
    kp = sig.load_keypair(hotkey)
    digest = sig.digest_of(rs, lean)
    # The timestamp is part of what is signed: the platform refuses a signature more than a
    # few minutes from its own clock, so a captured upload cannot be replayed later. A
    # machine whose clock is badly wrong will be refused -- that is the check working.
    timestamp = int(time.time())
    r = requests.post(
        f"{base(url, competition)}/submissions",
        headers=signed_headers(kp, competition=competition, digest=digest, timestamp=timestamp),
        files={"parse.rs": ("parse.rs", rs), "Parse.lean": ("Parse.lean", lean)},
        timeout=TIMEOUT,
    )
    # 201 for a new submission; the same two files again return the same submission, so a
    # retry after a dropped response is safe.
    if r.status_code not in (200, 201):
        sys.exit(refused("submit", r))
    s = cast(SubmitResult, r.json())
    again = "" if s["created"] else " (already queued: same files, same submission)"
    print(f"submission {s['submission']} {s['state']}{again}  digest {digest}")
    if s["slots_remaining"] is not None:
        print(
            f"{s['slots_remaining']} more submission(s) can be queued on this hotkey's "
            "registrations; one registration buys one accepted submission"
        )
    print(f"check with: submit.py status {s['submission']} --url {url}")


def cmd_status(args: argparse.Namespace) -> None:
    # Print a submission's state, its score once verified, and the gate's report.
    sub_id, url, competition = cast(str, args.id), cast(str, args.url), cast(str, args.competition)
    here = f"{base(url, competition)}/submissions/{sub_id}"
    r = requests.get(here, timeout=TIMEOUT)
    if r.status_code != 200:
        sys.exit(refused("status", r))
    body = cast(dict[str, object], r.json())
    if "submission" in body:
        current = cast(ApiStatus, cast(object, body))["submission"]
        print(
            f"submission {current['id']}  gate {current['gate_status']}  "
            f"submitted {current['submitted_at']}"
        )
        admission = current["admission"]
        print(f"admission {admission['outcome'] or 'pending'}: {admission['reason_code']}")
        if current["metrics"]:
            print(
                f"balanced time {current['metrics'].get('balanced_time_ratio')}x; "
                f"mean file compression {current['metrics'].get('mean_file_compression_pct')}%"
            )
        if current["score"]:
            print(f"payable competition weight {current['score'].get('payable_weight')}")
    else:
        s = cast(StatusResult, r.json())
        print(f"submission {s['id']}  state {s['state']}  submitted {s['submitted_at']}")
        m = s["metrics"]
        if m.get("bytes") is not None:
            vs, ratio = m.get("vs_incumbent"), m.get("time_ratio")
            print(f"bytes {m['bytes']}  vs incumbent {vs}x  time {ratio}x")
    # The report is its own endpoint on the platform, since it is unbounded text that no
    # listing should carry. It is how a rejected miner finds out which stage refused them.
    rr = requests.get(f"{here}/report", timeout=TIMEOUT)
    if rr.status_code == 200 and (report := cast(ReportResult, rr.json())["report"]):
        print(report)


def cmd_leaderboard(args: argparse.Namespace) -> None:
    # Print the whole ranking, following the platform's pages to the end.
    url, competition = cast(str, args.url), cast(str, args.competition)
    rows: list[LeaderboardEntry] = []
    cursor: str | None = None
    first: LeaderboardPage | None = None
    while True:
        params: dict[str, str | int] = {"limit": PAGE}
        if cursor:
            params["cursor"] = cursor
        r = requests.get(f"{base(url, competition)}/leaderboard", params=params, timeout=TIMEOUT)
        if r.status_code != 200:
            sys.exit(refused("leaderboard", r))
        body = cast(dict[str, object], r.json())
        if "context" in body:
            current = cast(ApiBoard, cast(object, body))
            if cursor is None:
                print(
                    f"scoring snapshot {current['context'].get('snapshot_id')}; "
                    "ranked by payable competition weight"
                )
                print(f"{'rank':>4} {'payable':>12} {'allocated':>12}  hotkey")
            for row in current["ranking"]:
                print(
                    f"{row['rank']:>4} {row['payable_weight']:>12.6f} "
                    f"{row['combined_weight']:>12.6f}  {row['hotkey']}"
                )
            cursor = current["next_cursor"]
            if cursor:
                continue
            return
        page = cast(LeaderboardPage, cast(object, body))
        first = first or page
        rows.extend(page["ranking"])
        cursor = page.get("next_cursor")
        if not cursor:
            break
    assert first is not None
    headline = first["headline"]
    print(
        f"incumbent {headline.get('incumbent_bytes')} bytes; "
        f"speed floor {headline.get('speed_floor')}x; ranked by {first['ranked_by']}"
    )
    if not rows:
        print("leaderboard: empty")
        return
    print(f"{'rank':>4} {'bytes':>10} {'vs incumbent':>13} {'time':>6}  hotkey")
    for x in rows:
        m = x["metrics"]
        head = f"{x['rank']:>4} {m.get('bytes')!s:>10} {m.get('vs_incumbent')!s:>12}x"
        ratio = m.get("time_ratio")
        time_ratio = f"{ratio:>5.2f}x" if isinstance(ratio, (int, float)) else "    ?"
        print(f"{head} {time_ratio}  {x['hotkey']}")


CMDS = {"submit": cmd_submit, "status": cmd_status, "leaderboard": cmd_leaderboard}


def main() -> None:
    # Dispatch a subcommand.
    ap = argparse.ArgumentParser(prog="submit.py", description=(__doc__ or "").split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(p: argparse.ArgumentParser) -> None:
        p.add_argument(
            "--url", required=True, help="the platform API's origin, e.g. https://api.host"
        )
        p.add_argument(
            "--competition",
            default=DEFAULT_COMPETITION,
            help=f"competition slug (default: {DEFAULT_COMPETITION})",
        )

    p = sub.add_parser("submit")
    p.add_argument("dir", help="submission directory with parse.rs and Parse.lean")
    p.add_argument("--hotkey", required=True, help="Bittensor hotkey file (or //Alice for tests)")
    common(p)
    st = sub.add_parser("status")
    st.add_argument("id")
    common(st)
    lb = sub.add_parser("leaderboard")
    common(lb)
    args = ap.parse_args()
    CMDS[cast(str, args.cmd)](args)


if __name__ == "__main__":
    main()
