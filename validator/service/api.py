"""The submission service: an app factory, a lifespan-owned store, and four endpoints.

    cd validator && python -m service.api          the API
    cd validator && python -m service.worker       the gate beside it

They are separate processes on purpose. The gate takes the better part of an hour per
submission; running it as a thread inside the API is what limits the API to a single
worker, and it means a gate crash takes the API with it.
"""

from __future__ import annotations

import os
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from typing import cast

from fastapi import FastAPI, HTTPException
from fastapi.exceptions import RequestValidationError
from fastapi.middleware.gzip import GZipMiddleware
from fastapi.middleware.trustedhost import TrustedHostMiddleware
from loguru import logger
from starlette.requests import Request
from starlette.responses import JSONResponse

import db
from observability.axiom import config_error, get_events, init

from . import routes
from .middleware import BodyLimit, RequestContext
from .settings import MAX_REQUEST_BYTES, Settings, load


def create_app(settings: Settings | None = None, store: db.Store | None = None) -> FastAPI:
    """Build the app. `store` is injected by the tests; in production the lifespan owns it.

    One store per process, created at startup and disposed at shutdown, so the connection
    pool is shared instead of a fresh connection being opened per request.
    """
    settings = settings or load()

    # Deprecated in typeshed for the ASGI lifespan protocol's sake; FastAPI's own
    # `lifespan=` argument still expects exactly this.
    @asynccontextmanager  # pyright: ignore[reportDeprecated]
    async def lifespan(app: FastAPI) -> AsyncIterator[None]:
        owned = store is None
        app.state.store = store or db.connect(
            rate_limit=settings.rate_per_minute,
            rate_window_seconds=settings.rate_window_seconds,
        )
        app.state.settings = settings
        logger.info(f"[api] listening on {settings.host}:{settings.port}")
        events = get_events()
        events.info(
            "service_started",
            host=settings.host,
            port=settings.port,
            rate_per_minute=settings.rate_per_minute,
            signature_window_seconds=settings.signature_window_seconds,
        )
        try:
            yield
        finally:
            events.info("service_stopped", reason="shutdown")
            if owned:
                app.state.store.close()

    app = FastAPI(
        title="conjectures-deflate-competition",
        # No interactive docs and no schema: the four endpoints are documented in the
        # README, and an unauthenticated schema endpoint is surface for nothing.
        docs_url=None,
        redoc_url=None,
        openapi_url=None,
        lifespan=lifespan,
    )
    app.state.settings = settings
    if store is not None:
        app.state.store = store

    # Outermost first: the body cap must refuse before anything reads, and the request
    # context must wrap everything it is meant to log.
    app.add_middleware(RequestContext)
    app.add_middleware(BodyLimit, max_bytes=MAX_REQUEST_BYTES)
    app.add_middleware(GZipMiddleware, minimum_size=1024)
    app.add_middleware(TrustedHostMiddleware, allowed_hosts=settings.host_allowlist)
    # No CORS: there is no browser client, so no origin needs to be allowed.

    app.include_router(routes.router)

    @app.exception_handler(HTTPException)
    async def _refusal(_request: Request, exc: HTTPException) -> JSONResponse:
        # Keep the {"detail": {"reason": ...}} shape the miner client already reads,
        # whether the detail was raised as a dict or as a bare string.
        detail = exc.detail if isinstance(exc.detail, dict) else {"reason": str(exc.detail)}
        return JSONResponse({"detail": detail}, status_code=exc.status_code)

    @app.exception_handler(RequestValidationError)
    async def _malformed(_request: Request, exc: RequestValidationError) -> JSONResponse:
        # A missing or unparseable form field. Name the fields, never echo their values:
        # the signature and the files are in there.
        # pydantic types an error's "loc" as Any; it is the field path tuple.
        errors = cast("list[dict[str, object]]", exc.errors())
        locs = [cast("tuple[object, ...]", e["loc"]) for e in errors]
        fields = sorted({str(loc[-1]) for loc in locs if loc})
        return JSONResponse(
            {"detail": {"reason": f"malformed or missing: {', '.join(fields)}"}}, status_code=422
        )

    return app


# No module-level `app`: building one at import time would read the environment before
# anything has a chance to fail cleanly. Run it with the factory instead --
# `uvicorn --factory service.api:create_app` -- or through main() below.


def main() -> None:
    import uvicorn

    events = init("competition-submission-api")
    try:
        settings = load()
    except Exception as exc:
        events.error("service_misconfigured", error=config_error(exc))
        raise
    uvicorn.run(
        create_app(settings),
        host=settings.host,
        port=settings.port,
        # Behind a reverse proxy this lets uvicorn honour X-Forwarded-*; direct, it makes
        # no difference because nothing sets those headers.
        proxy_headers=True,
        forwarded_allow_ips=os.environ.get("SERVICE_FORWARDED_ALLOW_IPS", "127.0.0.1"),
    )


if __name__ == "__main__":
    main()
