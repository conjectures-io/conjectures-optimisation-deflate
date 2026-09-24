"""The four endpoints: submit two signed files, read a submission, read the board."""

from __future__ import annotations

from typing import cast

from fastapi import APIRouter, File, Form, HTTPException, Request, UploadFile
from loguru import logger

import db
from db import iso, models
from scoring.config import ScoringConfig

from . import schemas, security, sig, storage
from .settings import MAX_FILE_BYTES, Settings

router = APIRouter()


def refuse(code: int, reason: str) -> HTTPException:
    # Every rejected write is a 4xx with a one-line reason, and nothing else.
    return HTTPException(status_code=code, detail={"reason": reason})


def _store(request: Request) -> db.Store:
    # Starlette's app.state is a namespace with no static type, so what the lifespan put
    # there has to be named here. Doing it once is what keeps every handler below typed
    # instead of Any.
    return cast("db.Store", request.app.state.store)  # pyright: ignore[reportAny]


def _settings(request: Request) -> Settings:
    return cast("Settings", request.app.state.settings)  # pyright: ignore[reportAny]


def _limit(request: Request, subject: str, what: str) -> None:
    allowed, hits = _store(request).rate.hit(subject)
    if not allowed:
        limit = _store(request).rate.limit
        logger.warning(f"[api] rate limit: {what} at {hits} writes in the window")
        raise refuse(429, f"more than {limit} writes a minute from this {what}")


def _client(request: Request) -> str:
    # The direct peer. Behind a proxy this is the proxy, which is why the hotkey bucket
    # is the one that actually bounds a miner -- this one only bounds an unsigned flood.
    return request.client.host if request.client else "unknown"


def submission_view(row: models.Submission) -> schemas.SubmissionView:
    return schemas.SubmissionView(
        id=row.id,
        hotkey=row.hotkey,
        baseline_key=row.baseline_key,
        digest=row.digest,
        submitted_at=iso(row.submitted_at),
        state=row.state,
        exit_code=row.exit_code,
        report=row.report,
        bytes=row.bytes,
        incumbent_bytes=row.incumbent_bytes,
        time_ratio=row.time_ratio,
    )


@router.get("/health", response_model=schemas.Health)
def health(request: Request) -> schemas.Health:
    # Liveness plus the queue length. Deliberately does not touch the database beyond
    # one count: a health check that fails when the store is slow takes the API down
    # with it. /ready is the one that reports the store.
    return schemas.Health(
        ok=True,
        queued=_store(request).submissions.queue_depth(),
        speed_floor=ScoringConfig.from_env().speed_floor,
        max_ratio_pct=ScoringConfig.from_env().max_ratio_pct,
    )


@router.get("/ready", response_model=schemas.Ready)
def ready(request: Request) -> schemas.Ready:
    # Readiness: can this process actually serve? Answers false, with a 503, when the
    # database is unreachable, so a load balancer stops sending it traffic.
    store = _store(request)
    try:
        database = store.ping()
        queued = store.submissions.queue_depth()
    except Exception as exc:  # noqa: BLE001 - any store failure is "not ready"
        logger.warning(f"[api] not ready: {exc}")
        raise HTTPException(503, {"reason": "the store is not reachable"}) from exc
    return schemas.Ready(
        ok=True,
        queued=queued,
        speed_floor=ScoringConfig.from_env().speed_floor,
        max_ratio_pct=ScoringConfig.from_env().max_ratio_pct,
        database=database,
    )


@router.post("/submit", response_model=schemas.SubmitAccepted)
async def submit(
    request: Request,
    hotkey: str = Form(...),
    signature: str = Form(...),
    timestamp: int = Form(...),
    parse_rs: UploadFile = File(..., alias="parse.rs"),
    parse_lean: UploadFile = File(..., alias="Parse.lean"),
) -> schemas.SubmitAccepted:
    """Accept two signed files and queue them for the gate.

    The checks run cheapest-first: shape, then the rate limit, then freshness, then the
    signature, then the entitlement. A malformed request is refused before it costs a
    curve operation, and an unregistered hotkey before it costs a disk write.

    Submitting the same two files again returns the same id and does not re-queue them.
    """
    store, settings = _store(request), _settings(request)
    _limit(request, f"ip:{_client(request)}", "address")
    try:
        security.check_hotkey(hotkey)
        security.check_signature(signature)
    except security.Invalid as exc:
        raise refuse(400, str(exc)) from exc

    _limit(request, f"hotkey:{hotkey}", "hotkey")

    try:
        security.check_fresh(timestamp, settings.signature_window_seconds)
    except security.Invalid as exc:
        raise refuse(401, str(exc)) from exc

    rs = await parse_rs.read(MAX_FILE_BYTES + 1)
    lean = await parse_lean.read(MAX_FILE_BYTES + 1)
    if len(rs) > MAX_FILE_BYTES or len(lean) > MAX_FILE_BYTES:
        raise refuse(413, f"each file must be at most {MAX_FILE_BYTES} bytes")
    if not rs or not lean:
        raise refuse(400, "both parse.rs and Parse.lean must be non-empty")

    digest = sig.digest_of(rs, lean)
    if not sig.verify(hotkey, sig.submit_message(digest, hotkey, timestamp), signature):
        raise refuse(401, "signature does not verify against the hotkey for these files")

    # One registration buys one accepted submission. Having a slot is checked here and
    # spent only when the gate accepts, so a rejection costs the miner nothing.
    if not store.registrations.is_registered(hotkey):
        raise refuse(402, "this hotkey is not registered on the subnet")
    allowed, slots, pending = store.submissions.may_queue(hotkey)
    if not allowed:
        raise refuse(
            402,
            f"{slots} unclaimed registration(s) and {pending} already in the queue: "
            "one registration buys one accepted submission, so register again to submit again",
        )

    sub_id, fresh = store.submissions.add(hotkey, digest)
    if fresh:
        storage.write_submission(settings.submission_dir(sub_id), rs, lean)
    row = store.submissions.get(sub_id)
    assert row is not None, "add() either inserted this row or found the existing one"
    logger.info(
        f"[api] submit hotkey={hotkey[:8]}… {digest[:16]} -> {sub_id} {row.state} "
        f"({'new' if fresh else 'repeat'}, {slots} slot(s))"
    )
    return schemas.SubmitAccepted(
        submission=sub_id, state=row.state, digest=digest, slots_remaining=slots
    )


@router.get("/submissions/{sub_id}", response_model=schemas.SubmissionView)
def submission(request: Request, sub_id: int) -> schemas.SubmissionView:
    # State, report and score of one submission. Public: a miner reads their own by id,
    # and the report is how they find out which stage refused them.
    row = _store(request).submissions.get(sub_id)
    if row is None:
        raise HTTPException(404, {"reason": "no such submission"})
    return submission_view(row)


@router.get("/leaderboard", response_model=schemas.Leaderboard)
def leaderboard(request: Request) -> schemas.Leaderboard:
    # Every hotkey's best accepted submission, fewest bytes first.
    store = _store(request)
    rows = store.submissions.leaderboard()
    incumbent = store.submissions.latest_incumbent_bytes()
    return schemas.Leaderboard(
        incumbent_bytes=incumbent,
        speed_floor=ScoringConfig.from_env().speed_floor,
        max_ratio_pct=ScoringConfig.from_env().max_ratio_pct,
        ranking=[
            schemas.Ranking(
                rank=i + 1,
                submission=row.id,
                hotkey=row.hotkey,
                baseline_key=row.baseline_key,
                # leaderboard() selects only accepted rows, and the worker records bytes
                # on every acceptance, so this is never NULL in practice.
                bytes=row.bytes or 0,
                vs_incumbent=(
                    round((row.bytes or 0) / row.incumbent_bytes, 5)
                    if row.incumbent_bytes
                    else None
                ),
                time_ratio=row.time_ratio,
                submitted_at=iso(row.submitted_at),
            )
            for i, row in enumerate(rows)
        ],
    )
