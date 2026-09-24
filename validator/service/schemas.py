"""The wire contract. Same fields the SQLite service returned, now declared."""

from __future__ import annotations

from typing import ClassVar

from pydantic import BaseModel, ConfigDict


class Health(BaseModel):
    ok: bool
    queued: int
    # Legacy field name: now a balanced scoring limit, not a benchmark limit.
    speed_floor: float
    max_ratio_pct: float


class Ready(Health):
    # False when the process is up but the database is not reachable: a load balancer
    # needs to tell "alive" from "able to serve".
    database: bool


class SubmitAccepted(BaseModel):
    submission: int
    state: str
    digest: str
    # What is left after this one. A miner who sees 0 knows the next submission needs
    # another registration, without having to read the refusal first.
    slots_remaining: int


class SubmissionView(BaseModel):
    model_config: ClassVar[ConfigDict] = ConfigDict(from_attributes=True)

    id: int
    hotkey: str | None
    baseline_key: str | None = None
    digest: str
    submitted_at: str
    state: str
    exit_code: int | None = None
    report: str | None = None
    bytes: int | None = None
    incumbent_bytes: int | None = None
    time_ratio: float | None = None


class Ranking(BaseModel):
    rank: int
    submission: int
    hotkey: str | None
    baseline_key: str | None = None
    bytes: int
    vs_incumbent: float | None = None
    time_ratio: float | None = None
    submitted_at: str


class Leaderboard(BaseModel):
    incumbent_bytes: int | None = None
    # Legacy field name: now a balanced scoring limit, not a benchmark limit.
    speed_floor: float
    max_ratio_pct: float
    ranking: list[Ranking]


class Refusal(BaseModel):
    reason: str
