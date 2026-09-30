"""The gate worker: claim a submission, run verify.py over it, record what came back.

Its own process, not a thread inside the API. The gate is a ~45 minute subprocess holding
a Lean toolchain and a cargo build; as a thread it pinned the API to one uvicorn worker
and took the API down with it whenever it died. Claiming with FOR UPDATE ... SKIP LOCKED
means several of these can drain one queue, on one box or on several.

    cd validator && python -m service.worker
"""

from __future__ import annotations

import datetime as dt
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import cast

from loguru import logger

import db
from db import SubmissionState, models
from observability.axiom import config_error, get_events, init
from observability.gate import verdict_fields, vs_incumbent

from .settings import Settings, load
from .storage import NAMES, write_submission

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
MEASURED = (
    "raw_bytes",
    "bytes",
    "incumbent_bytes",
    "parse_seconds",
    "compression_seconds",
    "incumbent_seconds",
)


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
        "incumbent_seconds": number(incumbent, "total_s"),
        "compression_seconds": number(me, "total_s"),
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


def run_gate(
    submission_dir: Path,
    results: Path,
    claim: dt.datetime | None = None,
    attempt: str | None = None,
) -> subprocess.CompletedProcess[str]:
    # Run verify.py over one submission directory, capped. A timeout is the validator
    # refusing to spend more; it is reported to the miner as a rejection with the reason.
    cmd = [sys.executable, str(VERIFY), str(submission_dir), "--results", str(results)]
    # Stored submission directories are named by their database ID. Local gate
    # invocations remain available separately through just check/verify-lean.
    cmd += ["--submission-id", str(int(submission_dir.name))]
    if claim is not None:
        cmd += ["--claim", claim.isoformat()]
    if attempt is not None:
        cmd += ["--claim-token", attempt]
    with subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=dict(os.environ),
        start_new_session=True,
    ) as process:
        try:
            stdout, stderr = process.communicate(timeout=TOTAL_TIMEOUT)
            return subprocess.CompletedProcess(cmd, process.returncode, stdout, stderr)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                stdout, stderr = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                stdout, stderr = process.communicate()
            return subprocess.CompletedProcess(
                cmd,
                1,
                stdout + f"\nREJECTED: the gate did not finish within {TOTAL_TIMEOUT:.0f}s\n",
                stderr,
            )


def materialize(store: db.Store, sub_id: int, directory: Path) -> bool:
    """Write a submission's database-held files into its submission directory.

    verify.py reads the directory `service.settings` names for the id, whichever path queued
    the submission. A submission queued through the platform API arrives with its files in
    `submission_files` and no directory, since that API shares no disk with this host; one
    queued through this repository's own service already has its directory and nothing in the
    table. Returns whether anything was written.

    The database copy wins when both exist: it is the one the submitter's signature covers,
    through the digest, and a directory left over from an earlier run must not stand in for it.
    """
    files = store.submissions.files(sub_id)
    if not files:
        return False
    if set(files) != set(NAMES):
        raise ValueError(f"submission {sub_id} stores {sorted(files)}, not {list(NAMES)}")
    write_submission(directory, files["parse.rs"], files["Parse.lean"])
    return True


def score_one(store: db.Store, settings: Settings, sub: models.Submission) -> str:
    """Verify one claimed submission and record the outcome. Returns its final state.

    An exit code the gate does not define is the validator's problem, not the miner's:
    the submission goes back on the queue uncharged and the loop stops so an operator
    sees it, rather than grinding the same misconfiguration through every submission.
    """
    label = sub.hotkey or sub.baseline_key or "unknown"
    logger.info(f"[worker] verifying submission {sub.id} ({label[:8]}…)")
    events = get_events()
    who = {"submission_id": sub.id, "hotkey": sub.hotkey, "baseline_key": sub.baseline_key}
    directory = settings.submission_dir(sub.id)
    try:
        materialize(store, sub.id, directory)
    except ValueError as exc:
        # A row the platform wrote wrongly is the validator's problem, not the miner's: back
        # on the queue uncharged, and the loop stops so an operator sees it.
        logger.error(f"[worker] submission {sub.id}: {exc}")
        store.submissions.requeue(
            sub.id, expected_claim=sub.claimed_at, expected_attempt=sub.verification_attempt
        )
        events.error("gate_verdict", **who, state="error", stage="materialize", reason=str(exc))
        events.warning("submission_requeued", submission_id=sub.id, reason=f"files: {exc}")
        return SubmissionState.ERROR.value
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix=f"score-{sub.id}-") as tmp:
        results = Path(tmp) / "results.json"
        result = run_gate(directory, results, sub.claimed_at, sub.verification_attempt)
        measured = scored(results) if result.returncode == 0 else {}
    duration = round(time.monotonic() - started, 3)
    report = result.stdout
    state = STATE_OF_EXIT.get(result.returncode)

    if state is None:
        logger.warning(
            f"[worker] validator error on submission {sub.id}:\n"
            f"{report[-1500:]}\n{result.stderr[-1500:]}"
        )
        store.submissions.requeue(
            sub.id, expected_claim=sub.claimed_at, expected_attempt=sub.verification_attempt
        )
        verdict = verdict_fields(report, state="error")
        events.error("gate_verdict", **who, state="error", **verdict, duration_seconds=duration)
        events.error(
            "gate_validator_error",
            submission_id=sub.id,
            exit_code=result.returncode,
            error=verdict["reason"] or result.stderr[-1500:] or report[-1500:],
        )
        events.warning(
            "submission_requeued",
            submission_id=sub.id,
            reason=f"validator error (exit {result.returncode})",
        )
        return SubmissionState.ERROR.value

    fields: dict[str, object] = {"exit_code": result.returncode, "report": report}
    if state is SubmissionState.ACCEPTED:
        fields |= measured
    final = store.submissions.finish(
        sub.id,
        state,
        expected_claim=sub.claimed_at,
        expected_attempt=sub.verification_attempt,
        **fields,
    )
    events.emit(
        "info" if final == SubmissionState.ACCEPTED.value else "warning",
        "gate_verdict",
        **who,
        state=final,
        **verdict_fields(report, state=final, gate_state=state.value),
        bytes=measured.get("bytes") if state is SubmissionState.ACCEPTED else None,
        vs_incumbent=vs_incumbent(measured) if state is SubmissionState.ACCEPTED else None,
        time_ratio=measured.get("time_ratio") if state is SubmissionState.ACCEPTED else None,
        exit_code=result.returncode,
        duration_seconds=duration,
    )
    if final == SubmissionState.ACCEPTED.value and (sub.hotkey or sub.baseline_key):
        from db.admission import run as admit

        try:
            decisions = admit(store.scoring, persist=True)
            for point in decisions:
                if point.submission_id == sub.id and point.admission:
                    logger.info(
                        f"[worker] admission {sub.id}: {point.admission['outcome']} "
                        f"({point.admission['reason_code']})"
                    )
        except ValueError as exc:
            logger.error(f"[worker] admission pending: {exc}")
    logger.info(
        f"[worker] submission {sub.id} {final}"
        + (f" {fields['bytes']} bytes" if "bytes" in fields else "")
    )
    return final


def drain(store: db.Store, settings: Settings) -> int:
    # Verify every claimable submission in arrival order; stop on a validator error.
    done = 0
    while (sub := store.submissions.claim_next(settings.worker_id)) is not None:
        get_events().info(
            "submission_claimed",
            submission_id=sub.id,
            hotkey=sub.hotkey,
            baseline_key=sub.baseline_key,
            worker_id=settings.worker_id,
        )
        if score_one(store, settings, sub) == SubmissionState.ERROR.value:
            break
        done += 1
    return done


def sweep(store: db.Store, settings: Settings) -> None:
    # Housekeeping between drains: reclaim what a dead worker abandoned, and drop
    # rate-limit counters for windows that can no longer be current.
    if requeued := store.submissions.requeue_stale(settings.stale_claim_seconds):
        logger.info(f"[worker] requeued {requeued} submission(s) abandoned mid-gate")
        get_events().warning(
            "submission_requeued", count=requeued, reason="stale claim: abandoned mid-gate"
        )
    store.rate.prune()


def run_forever(store: db.Store, settings: Settings) -> None:
    # Restore admission for submissions accepted before a restart, then drain the
    # queue. A transient startup error is retried before accepting more work.
    logger.info(f"[worker] {settings.worker_id} draining the queue")
    initialized = False
    turn = 0
    while True:
        try:
            if not initialized:
                requeued = store.submissions.requeue_interrupted(settings.worker_id)
                if requeued:
                    logger.info(
                        f"[worker] requeued {requeued} submission(s) interrupted before restart"
                    )
                sweep(store, settings)
                from db.admission import run as admit

                try:
                    decisions = admit(store.scoring, persist=True)
                except ValueError as exc:
                    # Invalid scoring evidence needs operator action. Keep verifying
                    # queued submissions; a restart can retry admission after repair.
                    logger.error(f"[worker] startup admission unavailable: {exc}")
                else:
                    pending = sum(
                        p.admission is not None and p.admission.get("outcome") == "pending"
                        for p in decisions
                    )
                    logger.info(
                        f"[worker] startup admission checked {len(decisions)} submission(s); "
                        f"{pending} pending"
                    )
                initialized = True
            drain(store, settings)
            turn += 1
            if turn % SWEEP_EVERY == 0:
                sweep(store, settings)
        except Exception:  # noqa: BLE001 - a database or subprocess blip must not end the loop
            logger.exception("[worker] loop error")
        time.sleep(IDLE_SECONDS)


def main() -> None:
    events = init("competition-gate-worker")
    try:
        settings = load()
    except Exception as exc:
        events.error("service_misconfigured", error=config_error(exc))
        raise
    store = db.connect()
    events.info(
        "service_started",
        worker_id=settings.worker_id,
        total_timeout_seconds=TOTAL_TIMEOUT,
        stale_claim_seconds=settings.stale_claim_seconds,
        corpus=os.environ.get("VERIFY_CORPUS") or None,
    )
    reason = "crashed"
    try:
        run_forever(store, settings)
    except KeyboardInterrupt:
        reason = "interrupted"
        logger.info("[worker] interrupted")
    finally:
        events.info("service_stopped", reason=reason)
        store.close()


if __name__ == "__main__":
    main()
