"""Everything that wraps a request: a body cap, a request id, and response headers."""

from __future__ import annotations

import uuid

from loguru import logger
from starlette.middleware.base import BaseHTTPMiddleware, RequestResponseEndpoint
from starlette.requests import Request
from starlette.responses import JSONResponse, Response
from starlette.types import ASGIApp

# Headers worth setting even on a JSON-only API: the responses carry a miner's gate
# report, and a browser that is somehow pointed at one should not sniff or frame it.
SECURITY_HEADERS = {
    "X-Content-Type-Options": "nosniff",
    "X-Frame-Options": "DENY",
    "Referrer-Policy": "no-referrer",
    "Cache-Control": "no-store",
}


class BodyLimit(BaseHTTPMiddleware):
    """Refuse an oversized body from its Content-Length, before anything reads it.

    Checking the declared length first means a multi-gigabyte upload is refused on its
    headers rather than after it has been streamed into a spooled temporary file. A
    request that lies about its length is still bounded by the per-file caps in the
    route, which read at most one byte past the limit.
    """

    _max: int

    def __init__(self, app: ASGIApp, *, max_bytes: int) -> None:
        super().__init__(app)
        self._max = max_bytes

    async def dispatch(self, request: Request, call_next: RequestResponseEndpoint) -> Response:
        declared = request.headers.get("content-length")
        if declared is not None and declared.isdigit() and int(declared) > self._max:
            return JSONResponse(
                {"detail": {"reason": f"the request may be at most {self._max} bytes"}},
                status_code=413,
            )
        return await call_next(request)


class RequestContext(BaseHTTPMiddleware):
    """Stamp each request with an id, log its outcome, and let nothing leak out of it.

    The id goes in the response header and in every log line for the request, so a miner
    reporting "my submission 500'd" can be matched to the traceback that caused it --
    which is what lets the response itself stay a one-line reason with no internals in it.
    """

    async def dispatch(self, request: Request, call_next: RequestResponseEndpoint) -> Response:
        request_id = uuid.uuid4().hex[:12]
        request.state.request_id = request_id
        with logger.contextualize(request_id=request_id):
            try:
                response: Response = await call_next(request)
            except Exception:
                logger.exception(f"[api] {request.method} {request.url.path} failed")
                response = JSONResponse(
                    {"detail": {"reason": "the validator hit an internal error"}},
                    status_code=500,
                )
            response.headers["X-Request-Id"] = request_id
            for header, value in SECURITY_HEADERS.items():
                response.headers.setdefault(header, value)
            if response.status_code >= 400:
                logger.info(f"[api] {request.method} {request.url.path} -> {response.status_code}")
            return response
