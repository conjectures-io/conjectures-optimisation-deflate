"""The submission bounty ledger: which epochs were read, who was credited, who is capped.

`scoring.bounty` decides; this reads and writes. Each epoch is recorded once, in one
transaction with its credits, so a restarted worker that reads the same epoch again
changes nothing.
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Iterable, Sequence
from typing import final

from sqlalchemy import func, select
from sqlalchemy.dialects.postgresql import insert
from sqlalchemy.orm import Session, sessionmaker

import db.models as models
from chain.types import EpochEmission
from scoring.bounty import Credit, Ledger, NewCap, Outlook, PaidSet, attribute

from .bounty_models import BountyAccrual, BountyCap, BountyEpoch
from .engine import session_scope


@final
class BountyDb:
    def __init__(self, sessions: sessionmaker[Session]) -> None:
        self._sessions = sessions

    def latest_epoch(self, netuid: int) -> int | None:
        with session_scope(self._sessions) as session:
            return session.scalar(
                select(func.max(BountyEpoch.epoch_block)).where(BountyEpoch.netuid == netuid)
            )

    def outlook(self, netuid: int) -> Outlook:
        with session_scope(self._sessions) as session:
            row = session.scalar(
                select(BountyEpoch)
                .where(BountyEpoch.netuid == netuid)
                .order_by(BountyEpoch.epoch_block.desc())
                .limit(1)
            )
            if row is None:
                return Outlook()
            return Outlook(miner_pool_rao=row.miner_pool_rao, horizon_epochs=row.reveal_epochs + 1)

    def record_epoch(self, netuid: int, epoch: EpochEmission) -> list[Credit] | None:
        """Credit one epoch's emission; None when it was already recorded."""
        with self._sessions.begin() as session:
            inserted = session.execute(
                insert(BountyEpoch)
                .values(
                    netuid=netuid,
                    epoch_block=epoch.epoch_block,
                    observed_block=epoch.block,
                    tempo=epoch.tempo,
                    reveal_epochs=epoch.reveal_epochs,
                    miner_pool_rao=epoch.miner_pool_rao,
                )
                .on_conflict_do_nothing()
                .returning(BountyEpoch.epoch_block)
            ).scalar_one_or_none()
            if inserted is None:
                return None
            credits = attribute(epoch, self._paid_sets(session, netuid, epoch))
            session.add_all(
                BountyAccrual(
                    netuid=netuid,
                    epoch_block=epoch.epoch_block,
                    submission_id=c.submission_id,
                    hotkey=c.hotkey,
                    coldkey=c.coldkey,
                    uid=c.uid,
                    alpha_rao=c.alpha_rao,
                    weight_set_id=c.weight_set_id,
                )
                for c in credits
            )
            return credits

    @staticmethod
    def _paid_sets(session: Session, netuid: int, epoch: EpochEmission) -> list[PaidSet]:
        # The accepted vectors that could have paid this epoch: the one consensus read,
        # set `reveal_epochs` before it, and those since. Dry runs paid nobody.
        rows = session.scalars(
            select(models.WeightSet)
            .where(
                models.WeightSet.netuid == netuid,
                models.WeightSet.accepted,
                models.WeightSet.dry_run.is_(False),
                models.WeightSet.block <= epoch.epoch_block,
            )
            .order_by(models.WeightSet.id.desc())
            .limit(epoch.reveal_epochs + 3)
        ).all()
        sets: list[PaidSet] = []
        for row in rows:
            paid: dict[str, list[tuple[int, float]]] = defaultdict(list)
            for snap in session.scalars(
                select(models.ScoreSnapshot).where(
                    models.ScoreSnapshot.weight_set_id == row.id,
                    models.ScoreSnapshot.payable_weight > 0,
                    models.ScoreSnapshot.hotkey.is_not(None),
                    models.ScoreSnapshot.submission_id.is_not(None),
                )
            ):
                assert snap.hotkey is not None and snap.submission_id is not None
                paid[snap.hotkey].append((snap.submission_id, snap.payable_weight))
            sets.append(PaidSet(row.id, row.block, dict(paid)))
        return sets

    def ledgers(self, submission_ids: Iterable[int]) -> dict[int, Ledger]:
        credited = BountyAccrual
        ids = sorted(set(submission_ids))
        if not ids:
            return {}
        with session_scope(self._sessions) as session:
            earned: dict[int, int] = dict(
                session.execute(
                    select(credited.submission_id, func.sum(credited.alpha_rao))
                    .where(BountyAccrual.submission_id.in_(ids))
                    .group_by(BountyAccrual.submission_id)
                )
                .tuples()
                .all()
            )
            latest = (
                select(
                    BountyAccrual.submission_id,
                    func.max(BountyAccrual.epoch_block).label("epoch_block"),
                )
                .where(BountyAccrual.submission_id.in_(ids))
                .group_by(BountyAccrual.submission_id)
                .subquery()
            )
            last: dict[int, int] = dict(
                session.execute(
                    select(credited.submission_id, func.sum(credited.alpha_rao))
                    .join(
                        latest,
                        (latest.c.submission_id == BountyAccrual.submission_id)
                        & (latest.c.epoch_block == BountyAccrual.epoch_block),
                    )
                    .group_by(BountyAccrual.submission_id)
                )
                .tuples()
                .all()
            )
            capped = set(
                session.scalars(
                    select(BountyCap.submission_id).where(BountyCap.submission_id.in_(ids))
                )
            )
            return {
                sid: Ledger(int(earned.get(sid) or 0), int(last.get(sid) or 0), sid in capped)
                for sid in ids
            }

    def totals(self, submission_ids: Iterable[int]) -> dict[int, int]:
        """Alpha rao each submission has received; what the read endpoints show."""
        return {sid: ledger.earned_rao for sid, ledger in self.ledgers(submission_ids).items()}

    def cap(self, caps: Sequence[NewCap], *, bounty_rao: int) -> None:
        if not caps:
            return
        with self._sessions.begin() as session:
            session.execute(
                insert(BountyCap)
                .values(
                    [
                        {
                            "submission_id": c.submission_id,
                            "hotkey": c.hotkey,
                            "earned_rao": c.earned_rao,
                            "projected_rao": c.projected_rao,
                            "bounty_rao": bounty_rao,
                        }
                        for c in caps
                    ]
                )
                .on_conflict_do_nothing()
            )
