"""The gate worker: claim a submission, run verify.py over it, record what came back.

Its own process, not a thread inside the API. The gate is a ~45 minute subprocess holding
a Lean toolchain and a cargo build; as a thread it pinned the API to one uvicorn worker
and took the API down with it whenever it died. Claiming with FOR UPDATE ... SKIP LOCKED
means several of these can drain one queue, on one box or on several.

    cd validator && python -m service.worker
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import cast

from loguru import logger

import db
from db import SubmissionState, models

from .settings import Settings, load

VALIDATOR = Path(__file__).resolve().parent.parent
VERIFY = VALIDATOR / "verifier/verify.py"

# The whole gate, every stage. The Lean stages have their own tighter cap inside verify.py.
TOTAL_TIMEOUT = float(os.environ.get("VERIFY_TOTAL_TIMEOUT", "2700"))

STATE_OF_EXIT = {0: SubmissionState.ACCEPTED, 1: SubmissionState.REJECTED}
IDLE_SECONDS = 2.0
# How often to sweep stale claims and expired rate-limit windows, in idle turns.
SWEEP_EVERY = 30

# What scoring needs from a run, and what the store has a column for. All of it or none
# of it: a row carrying bytes but no timing would put a half-measured point on the
# frontier, and db.scoring filters those out anyway, so recording one only hides the
# problem until someone asks why a submission never scored.
MEASURED = ("raw_bytes", "bytes", "incumbent_bytes", "parse_seconds", "incumbent_seconds")


def scored(results: Path) -> dict[str, int | float]:
    """Pull the score out of the results file the gate wrote.

    `candidates` names the submission's own method, so nothing here depends on what the
    caller happened to name it. Reading the gate's JSON rather than scraping its stdout
    is what lets the report stay a human document: it can be reworded without silently
    changing what a validator stores.
    """
    if not results.is_file():
        return {}
    summary = cast("dict[str, object]", json.loads(results.read_text()))
    names = cast("list[str]", summary.get("candidates", []))
    methods = cast("dict[str, dict[str, object]]", summary.get("methods", {}))
    if not names or names[0] not in methods:
        return {}
    me, incumbent = methods[names[0]], methods.get("incumbent", {})

    def number(source: dict[str, object], key: str) -> int | float | None:
        value = source.get(key)
        return value if isinstance(value, (int, float)) and not isinstance(value, bool) else None

    out: dict[str, int | float | None] = {
        "raw_bytes": number(summary, "raw_bytes"),
        "bytes": number(me, "output_bytes"),
        "incumbent_bytes": number(incumbent, "output_bytes"),
        "parse_seconds": number(me, "parse_s"),
        "incumbent_seconds": number(incumbent, "parse_s"),
    }
    if any(out[key] is None for key in MEASURED):
        logger.warning(f"[worker] {results} is missing {[k for k in MEASURED if out[k] is None]}")
        return {}
    full = cast("dict[str, int | float]", out)
    # The gate computes the ratio the floor is applied to; recomputing it here would be a
    # second opinion on the one number the verdict already turned on.
    if (slowdown := number(me, "slowdown")) is not None:
        full["time_ratio"] = float(slowdown)
    return full


def run_gate(submission_dir: Path, results: Path) -> subprocess.CompletedProcess[str]:
    # Run verify.py over one submission directory, capped. A timeout is the validator
    # refusing to spend more; it is reported to the miner as a rejection with the reason.
    cmd = [sys.executable, str(VERIFY), str(submission_dir), "--results", str(results)]
    try:
        return subprocess.run(
            cmd, capture_output=True, text=True, env=dict(os.environ), timeout=TOTAL_TIMEOUT
        )
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        return subprocess.CompletedProcess(
            cmd, 1, out + f"\nREJECTED: the gate did not finish within {TOTAL_TIMEOUT:.0f}s\n", ""
        )


def score_one(store: db.Store, settings: Settings, sub: models.Submission) -> str:
    """Verify one claimed submission and record the outcome. Returns its final state.

    An exit code the gate does not define is the validator's problem, not the miner's:
    the submission goes back on the queue uncharged and the loop stops so an operator
    sees it, rather than grinding the same misconfiguration through every submission.
    """
    logger.info(f"[worker] verifying submission {sub.id} ({sub.hotkey[:8]}…)")
    with tempfile.TemporaryDirectory(prefix=f"score-{sub.id}-") as tmp:
        results = Path(tmp) / "results.json"
        result = run_gate(settings.submission_dir(sub.id), results)
        measured = scored(results) if result.returncode == 0 else {}
    report = result.stdout
    state = STATE_OF_EXIT.get(result.returncode)

    if state is None:
        logger.warning(
            f"[worker] validator error on submission {sub.id}:\n"
            f"{report[-1500:]}\n{result.stderr[-1500:]}"
        )
        store.submissions.requeue(sub.id)
        return SubmissionState.ERROR.value

    fields: dict[str, object] = {"exit_code": result.returncode, "report": report}
    if state is SubmissionState.ACCEPTED:
        fields |= measured
    final = store.submissions.finish(sub.id, state, **fields)
    logger.info(
        f"[worker] submission {sub.id} {final}"
        + (f" {fields['bytes']} bytes" if "bytes" in fields else "")
    )
    return final


def drain(store: db.Store, settings: Settings) -> int:
    # Verify every claimable submission in arrival order; stop on a validator error.
    done = 0
    while (sub := store.submissions.claim_next(settings.worker_id)) is not None:
        if score_one(store, settings, sub) == SubmissionState.ERROR.value:
            break
        done += 1
    return done


def sweep(store: db.Store, settings: Settings) -> None:
    # Housekeeping between drains: reclaim what a dead worker abandoned, and drop
    # rate-limit counters for windows that can no longer be current.
    if requeued := store.submissions.requeue_stale(settings.stale_claim_seconds):
        logger.info(f"[worker] requeued {requeued} submission(s) abandoned mid-gate")
    store.rate.prune()


def run_forever(store: db.Store, settings: Settings) -> None:
    # Sweep, drain, sleep when idle, and never die on one bad turn.
    logger.info(f"[worker] {settings.worker_id} draining the queue")
    sweep(store, settings)
    turn = 0
    while True:
        try:
            drain(store, settings)
            turn += 1
            if turn % SWEEP_EVERY == 0:
                sweep(store, settings)
        except Exception:  # noqa: BLE001 - a database or subprocess blip must not end the loop
            logger.exception("[worker] loop error")
        time.sleep(IDLE_SECONDS)


def main() -> None:
    settings = load()
    store = db.connect()
    try:
        run_forever(store, settings)
    except KeyboardInterrupt:
        logger.info("[worker] interrupted")
    finally:
        store.close()


if __name__ == "__main__":
    main()
