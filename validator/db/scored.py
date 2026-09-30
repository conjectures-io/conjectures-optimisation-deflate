"""The scored-submission data contract, shared by scoring and admission.

Pulled out of scoring.py on purpose: ScoringDb calls into admission.evaluate() (which
returns and rewrites these), and admission.py needs this type for its own signatures.
Living in scoring.py would put ScoredSubmission on the wrong side of a real cycle; a
plain, dependency-free module is what both sides import instead.
"""

from __future__ import annotations

import dataclasses as dc
import datetime as dt


@dc.dataclass(frozen=True, slots=True)
class ScoredSubmission:
    """One accepted submission, reduced to what scoring actually uses.

    `pareto_time` and `ratio_pct` are the Pareto axes, both "lower is better".
    `time_s` retains absolute seconds; current evidence supplies normalized_time_ratio.
    `ratio_pct` is
    the equal-corpus mean of per-file compression percentages for current aggregations.
    Raw byte totals remain telemetry. Legacy standalone inputs use byte-weighted ratios.
    """

    submission_id: int
    hotkey: str | None
    bytes: int
    raw_bytes: int
    time_s: float
    # The incumbent as this submission's own run measured it. Both are needed: the bytes
    # are the record the improvement component measures progress against (and they move
    # when an operator promotes a new incumbent), and the seconds set the speed floor
    # that is the frontier's time boundary.
    incumbent_bytes: int
    incumbent_seconds: float
    submitted_at: dt.datetime
    aggregation_id: int | None = None
    baseline_key: str | None = None
    context: dict[str, object] | None = None
    # Full recorded context stays intact for admission identity and audit. Scoring
    # compares the same context with only the engine binary hash omitted.
    comparison_context: dict[str, object] | None = None

    admission_check_id: int | None = None
    admission: dict[str, object] | None = None
    normalized_time_ratio: float | None = None
    verification_current: bool | None = None
    normalized_ratio_pct: float | None = None
    normalized_incumbent_ratio_pct: float | None = None

    @property
    def pareto_time(self) -> float:
        return self.normalized_time_ratio if self.normalized_time_ratio is not None else self.time_s

    @property
    def point_id(self) -> str:
        return str(self.submission_id)

    @property
    def ratio_pct(self) -> float:
        if self.normalized_ratio_pct is not None:
            return self.normalized_ratio_pct
        return self.byte_weighted_ratio_pct

    @property
    def byte_weighted_ratio_pct(self) -> float:
        return 100.0 * self.bytes / self.raw_bytes
