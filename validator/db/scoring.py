"""What the scorer reads, and what it writes back.

The reads are deliberately narrow: the scorer needs each competing hotkey's position on
the (time, ratio) plane and the history of accepted submissions that improved on the
record. The writes are the audit trail -- the vector that was set and the per-hotkey
reasoning behind it.
"""

from __future__ import annotations

import dataclasses as dc
import datetime as dt

from sqlalchemy import select
from sqlalchemy.orm import Session, sessionmaker

from . import models
from .engine import session_scope
from .status import SubmissionState


@dc.dataclass(frozen=True, slots=True)
class ScoredSubmission:
    """One accepted submission, reduced to what scoring actually uses.

    `time_s` and `ratio_pct` are the Pareto axes, both "lower is better". `ratio_pct` is
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

    verification_current: bool | None = None
    normalized_ratio_pct: float | None = None
    normalized_incumbent_ratio_pct: float | None = None

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


def _scorable(stmt, *, preview=False):
    # Only accepted submissions carrying every number the frontier needs. A row missing
    # one of them predates the columns or came from a harness that did not print it;
    # scoring it would put a fabricated point on the frontier.
    from verifier.identity import required_fingerprint

    return stmt.where(
        models.Submission.static_verified_at.is_not(None),
        models.Submission.lean_verified_at.is_not(None),
        models.Submission.verifier_fingerprint.is_not(None)
        if preview
        else models.Submission.verifier_fingerprint == required_fingerprint(),
        models.Submission.measured_source_sha256 == models.Submission.source_sha256,
        models.Submission.state == SubmissionState.ACCEPTED.value,
        models.Submission.bytes.is_not(None),
        models.Submission.raw_bytes.is_not(None),
        models.Submission.raw_bytes > 0,
        models.Submission.compression_seconds.is_not(None),
        models.Submission.compression_seconds > 0,
        models.Submission.incumbent_seconds.is_not(None),
        models.Submission.incumbent_bytes.is_not(None),
    )


def _to_scored(row: models.Submission) -> ScoredSubmission:
    # Every column below is nullable on the model and non-null here: `_scorable` is the
    # only way a row reaches this function, and it filters out each one. The asserts are
    # that filter restated where the types are checked -- if the filter is ever loosened,
    # this fails loudly instead of putting a half-measured point on the frontier.
    assert row.bytes is not None, "_scorable filters bytes IS NULL"
    assert row.raw_bytes is not None, "_scorable filters raw_bytes IS NULL"
    assert row.compression_seconds is not None, "_scorable filters compression_seconds IS NULL"
    assert row.incumbent_seconds is not None, "_scorable filters incumbent_seconds IS NULL"
    return ScoredSubmission(
        submission_id=row.id,
        hotkey=row.hotkey,
        bytes=row.bytes,
        raw_bytes=row.raw_bytes,
        time_s=row.compression_seconds,
        incumbent_bytes=row.incumbent_bytes,
        incumbent_seconds=row.incumbent_seconds,
        submitted_at=row.submitted_at,
        aggregation_id=row.aggregation_id,
        baseline_key=row.baseline_key,
    )


class ScoringDb:
    def __init__(self, sessions: sessionmaker[Session]) -> None:
        self._sessions = sessions

    def scoring_inputs(self, corpora=None, aggregation_ids=None) -> list[ScoredSubmission]:
        """Current verified, published evidence for live scoring."""
        return self._inputs(corpora, aggregation_ids, preview=False)

    def preview_inputs(self, corpora=None, aggregation_ids=None) -> list[ScoredSubmission]:
        """Recalculate historical verified evidence without publishing or re-verifying.

        Use the runs linked to each submission's published aggregation (or explicit
        aggregation IDs), never silently select different benchmark measurements.
        Historical verification is sufficient for this operator-only preview.
        """
        return self._inputs(corpora, aggregation_ids, preview=True)

    def _inputs(self, corpora, aggregation_ids, *, preview) -> list[ScoredSubmission]:
        """SCORING_CORPORA selects exact corpus hashes; mixed contexts fail closed."""
        import json
        import os

        from verifier.identity import required_fingerprint

        from .aggregation import CALCULATOR_VERSION, evaluation_context, reduce_runs

        current_fingerprint = required_fingerprint()

        requested = corpora
        if requested is None and os.getenv("SCORING_CORPORA"):
            requested = json.loads(os.environ["SCORING_CORPORA"])
        with session_scope(self._sessions) as session:
            rows = list(
                session.scalars(
                    _scorable(select(models.Submission), preview=preview)
                    .where(
                        models.Submission.aggregation_id.is_not(None),
                        (
                            True
                            if aggregation_ids is not None
                            else (
                                models.Submission.baseline_key.is_(None)
                                | models.Submission.baseline_active
                            )
                        ),
                    )
                    .order_by(models.Submission.submitted_at, models.Submission.id)
                )
            )
            overrides = {}
            if aggregation_ids is not None:
                for aid in aggregation_ids:
                    item = session.get(models.BenchmarkAggregation, aid)
                    if item is None or item.source_sha256 in overrides:
                        raise ValueError(
                            "unknown aggregation or multiple aggregations for one source"
                        )
                    overrides[item.source_sha256] = item
            result = []
            for row in rows:
                aggregation = (
                    overrides.get(row.source_sha256)
                    if aggregation_ids is not None
                    else session.get(models.BenchmarkAggregation, row.aggregation_id)
                )
                if aggregation is None or (
                    not preview and aggregation.calculator_version != CALCULATOR_VERSION
                ):
                    continue
                runs = list(
                    session.scalars(
                        select(models.BenchmarkRun)
                        .join(
                            models.BenchmarkAggregationInput,
                            models.BenchmarkAggregationInput.run_id == models.BenchmarkRun.id,
                        )
                        .where(models.BenchmarkAggregationInput.aggregation_id == aggregation.id)
                    )
                )
                try:
                    values = reduce_runs(runs)
                    context = evaluation_context(runs)
                except ValueError:
                    continue  # Invalidated evidence removes the point, not only its payout.
                # A formula change may alter only aggregation metadata. Corpus,
                # timing definition and measurement protocol must still agree.
                ignored = {"calculator", "compression"} if preview else set()
                stored_context = {
                    key: value for key, value in aggregation.context.items() if key not in ignored
                }
                computed_context = {
                    key: value for key, value in context.items() if key not in ignored
                }
                if (
                    stored_context != computed_context
                    or values.source_sha256 != row.source_sha256
                    or aggregation.source_sha256 != row.source_sha256
                ):
                    continue
                if requested is not None and dict(context["corpora"]) != requested:
                    continue
                if any(
                    getattr(values, key) != getattr(aggregation, key)
                    for key in (
                        "raw_bytes",
                        "bytes",
                        "incumbent_bytes",
                        "parse_seconds",
                        "compression_seconds",
                        "incumbent_seconds",
                    )
                ):
                    continue
                if aggregation.compression_seconds is None:
                    continue
                result.append(
                    dc.replace(
                        _to_scored(row),
                        bytes=aggregation.bytes,
                        raw_bytes=aggregation.raw_bytes,
                        time_s=aggregation.compression_seconds,
                        incumbent_bytes=aggregation.incumbent_bytes,
                        incumbent_seconds=aggregation.incumbent_seconds,
                        verification_current=row.verifier_fingerprint == current_fingerprint,
                        normalized_ratio_pct=values.ratio_pct,
                        normalized_incumbent_ratio_pct=values.incumbent_ratio_pct,
                        context=context,
                        aggregation_id=aggregation.id,
                    )
                )
            if aggregation_ids is not None and {r.aggregation_id for r in result} != set(
                aggregation_ids
            ):
                raise ValueError(
                    "requested aggregation is invalid or lacks the required verified "
                    "submission identity"
                )
            if len({json.dumps(r.context, sort_keys=True) for r in result}) > 1:
                raise ValueError(
                    "incompatible published scoring contexts; select SCORING_CORPORA "
                    "and rebenchmark consistently"
                )
            return result

    def best_per_hotkey(self) -> list[ScoredSubmission]:
        """Each hotkey's best accepted submission -- one competitor, one point.

        "Best" is fewest bytes, earliest submission breaking a tie: the same rule the
        leaderboard ranks by, so what a miner sees ranked is what gets scored.
        """
        with session_scope(self._sessions) as session:
            rows = (
                session.execute(
                    _scorable(
                        select(models.Submission)
                        .distinct(models.Submission.hotkey)
                        .order_by(
                            models.Submission.hotkey,
                            models.Submission.bytes,
                            models.Submission.submitted_at,
                            models.Submission.id,
                        )
                    )
                )
                .scalars()
                .all()
            )
            return [_to_scored(r) for r in rows]

    def accepted_history(self) -> list[ScoredSubmission]:
        # Every scorable accepted submission, oldest first: the improvement component
        # walks this in order to find which ones actually moved the record.
        with session_scope(self._sessions) as session:
            rows = (
                session.execute(
                    _scorable(select(models.Submission)).order_by(
                        models.Submission.submitted_at, models.Submission.id
                    )
                )
                .scalars()
                .all()
            )
            return [_to_scored(r) for r in rows]

    def record_weight_set(
        self,
        *,
        netuid: int,
        block: int,
        uids: list[int],
        weights: list[float],
        summary: str | None,
        accepted: bool,
        dry_run: bool = False,
        error: str | None = None,
        snapshots: list[dict[str, object]] | None = None,
    ) -> int:
        """Persist one weight vector and the per-hotkey reasoning behind it.

        Both in one transaction: a vector whose explanation went missing is not an audit
        trail. Returns the weight_sets id.
        """
        with session_scope(self._sessions) as session:
            row = models.WeightSet(
                netuid=netuid,
                block=block,
                uids=list(uids),
                weights=[float(w) for w in weights],
                summary=summary,
                accepted=accepted,
                dry_run=dry_run,
                error=error,
            )
            session.add(row)
            session.flush()
            for snap in snapshots or []:
                session.add(models.ScoreSnapshot(weight_set_id=row.id, **snap))
            return int(row.id)
