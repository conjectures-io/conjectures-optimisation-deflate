"""Every knob the service reads, in one typed object.

pydantic-settings so a bad value fails at startup with the variable's name in the error,
rather than at the first request that happens to need it.
"""

from __future__ import annotations

import os
import socket
from pathlib import Path
from typing import ClassVar

from pydantic import Field, field_validator
from pydantic_settings import BaseSettings, SettingsConfigDict

VALIDATOR = Path(__file__).resolve().parent.parent

# Each of the two submitted files. Generous: the largest reference submission is under
# 20 KB, so anything near this is already not a parser and a proof.
MAX_FILE_BYTES = 512 * 1024
# The whole multipart body, including both files, the form fields and their headers.
MAX_REQUEST_BYTES = 3 * MAX_FILE_BYTES
# A submission that beats the incumbent's bytes but is slower than this multiple of the
# incumbent's time is rejected by the gate, not here; the API only reports it.
SPEED_FLOOR = 8.0


class Settings(BaseSettings):
    model_config: ClassVar[SettingsConfigDict] = SettingsConfigDict(
        env_prefix="SERVICE_", extra="ignore"
    )

    host: str = "0.0.0.0"
    port: int = 9200
    # Where the two files of each submission are written. Everything else is in Postgres.
    files: Path = VALIDATOR / ".work/submissions"

    # Signed writes allowed per hotkey per minute, counted in Postgres.
    rate_per_minute: int = Field(default=10, ge=1)
    rate_window_seconds: int = Field(default=60, ge=1)

    # How far a submission's signed timestamp may sit from the validator's clock. A
    # captured request is useless once it falls outside this, which is what stops a
    # recorded upload being replayed against a later round.
    signature_window_seconds: int = Field(default=300, ge=1)

    # Host header allowlist; "*" accepts anything, which is right behind a proxy that
    # already filters. Comma-separated.
    allowed_hosts: str = "*"

    # Identifies this gate worker in the submissions table. Two workers on one box must
    # not share it, which is why the default carries the pid.
    worker_id: str = Field(default_factory=lambda: f"{socket.gethostname()}:{os.getpid()}")

    # Seconds a claimed submission may sit in `verifying` before another worker may take
    # it. Must exceed the gate's own timeout, or a slow verification gets stolen.
    stale_claim_seconds: float = Field(default=7200.0, gt=0)

    @field_validator("files")
    @classmethod
    def _absolute(cls, value: Path) -> Path:
        # Relative paths in .env are relative to the repo, not to whatever directory the
        # process happened to start in.
        return value if value.is_absolute() else (VALIDATOR.parent / value).resolve()

    @property
    def host_allowlist(self) -> list[str]:
        return [h.strip() for h in self.allowed_hosts.split(",") if h.strip()]

    def submission_dir(self, sub_id: int) -> Path:
        return self.files / str(sub_id)


def load() -> Settings:
    return Settings()
