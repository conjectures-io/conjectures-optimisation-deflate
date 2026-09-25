"""The submission bounty ledger's tables (`db.bounty`, `scoring.bounty`).

Kept out of db/models.py on purpose: that file is pinned (verifier/PINS.json), so a
change there changes the verifier fingerprint and sends every submission back through
the gate. Nothing here takes part in a verdict. The tables share the one metadata, so
the schema drift test and the migrations see them like any other.
"""

from __future__ import annotations

import datetime as dt

from sqlalchemy import (
    BigInteger,
    CheckConstraint,
    DateTime,
    ForeignKey,
    ForeignKeyConstraint,
    Index,
    Integer,
    Text,
    UniqueConstraint,
    func,
)
from sqlalchemy.orm import Mapped, mapped_column
from sqlalchemy.sql.schema import SchemaItem

from .models import Base


class BountyEpoch(Base):
    """One subnet epoch whose emission the bounty ledger has read -- each exactly once.

    The epoch's pool and commit-reveal delay are kept because the next cap decision
    projects from them.
    """

    __tablename__: str = "bounty_epochs"

    netuid: Mapped[int] = mapped_column(Integer, primary_key=True)
    # The chain's LastMechansimStepBlock: the epoch's identity.
    epoch_block: Mapped[int] = mapped_column(BigInteger, primary_key=True)
    # The block the emission was read at.
    observed_block: Mapped[int] = mapped_column(BigInteger, nullable=False)
    tempo: Mapped[int] = mapped_column(Integer, nullable=False)
    reveal_epochs: Mapped[int] = mapped_column(Integer, nullable=False)
    miner_pool_rao: Mapped[int] = mapped_column(BigInteger, nullable=False)
    created_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )


class BountyAccrual(Base):
    """Alpha one (hotkey, coldkey, submission) pair received in one epoch.

    Read from the chain's per-uid Emission and credited to the submissions the named
    weight set paid that hotkey for; the sum over a submission is what it has earned.
    """

    __tablename__: str = "bounty_accruals"

    id: Mapped[int] = mapped_column(BigInteger, primary_key=True, autoincrement=True)
    netuid: Mapped[int] = mapped_column(Integer, nullable=False)
    epoch_block: Mapped[int] = mapped_column(BigInteger, nullable=False)
    submission_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("submissions.id", ondelete="RESTRICT"), nullable=False
    )
    hotkey: Mapped[str] = mapped_column(Text, nullable=False)
    coldkey: Mapped[str] = mapped_column(Text, nullable=False)
    uid: Mapped[int] = mapped_column(Integer, nullable=False)
    alpha_rao: Mapped[int] = mapped_column(BigInteger, nullable=False)
    weight_set_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("weight_sets.id", ondelete="RESTRICT"), nullable=False
    )
    created_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )

    __table_args__: tuple[SchemaItem, ...] = (
        ForeignKeyConstraint(
            ["netuid", "epoch_block"],
            ["bounty_epochs.netuid", "bounty_epochs.epoch_block"],
            ondelete="RESTRICT",
        ),
        UniqueConstraint("netuid", "epoch_block", "submission_id", "uid"),
        CheckConstraint("alpha_rao >= 0", name="ck_bounty_accrual_nonnegative"),
        Index("ix_bounty_accruals_submission", "submission_id"),
    )


class BountyCap(Base):
    """A submission that reached its bounty: paid nothing from then on, permanently."""

    __tablename__: str = "bounty_caps"

    submission_id: Mapped[int] = mapped_column(
        BigInteger, ForeignKey("submissions.id", ondelete="RESTRICT"), primary_key=True
    )
    hotkey: Mapped[str] = mapped_column(Text, nullable=False)
    # What it had received, and what the projection added, when it was capped.
    earned_rao: Mapped[int] = mapped_column(BigInteger, nullable=False)
    projected_rao: Mapped[int] = mapped_column(BigInteger, nullable=False)
    bounty_rao: Mapped[int] = mapped_column(BigInteger, nullable=False)
    created_at: Mapped[dt.datetime] = mapped_column(
        DateTime(timezone=True), nullable=False, server_default=func.now()
    )
