"""Data contracts for chain state -- pure, no IO, no SDK types.

These are the immutable snapshots a `source.ChainSource` produces and the watcher
publishes, and the views the weight setter works from. They are deliberately framed in
plain Python so nothing downstream depends on how the data was fetched: that is what
makes one source interchangeable with another, and what lets every test here run without
a node.
"""

from __future__ import annotations

import dataclasses as dc
import datetime as dt

# Subnet 66 on the Bittensor mainnet, polled from Finney by default.
NETUID = 66
FINNEY = "finney"
# A neuron's registration block is usually older than a lite node's ~300-block state
# window, so its on-chain time is read from an archive node (full history) instead.
ARCHIVE = "archive"

# Blocks are ~12s apart; polling at half that comfortably catches every head.
BLOCK_SECONDS = 12
POLL_INTERVAL_SECONDS = BLOCK_SECONDS / 2


@dc.dataclass(frozen=True, slots=True)
class ChainHead:
    """The current chain tip: its block number and wall-clock time (UTC)."""

    block: int
    timestamp: dt.datetime


@dc.dataclass(frozen=True, slots=True)
class NeuronInfo:
    """One neuron registered on the subnet.

    `block_at_registration` is when this uid was registered -- the on-chain
    BlockAtRegistration height for the uid -- not the block of the snapshot it was read
    from. Stamping a registration with its own block keeps it correct across watcher
    downtime and the initial backfill, when the snapshot block can be far ahead of when
    the neuron actually registered. That matters more here than it did in the validator
    this was ported from: the block is what makes each registration a distinct row, and
    each row is one submission slot.
    """

    uid: int
    hotkey: str
    coldkey: str
    stake: float
    block_at_registration: int


@dc.dataclass(frozen=True, slots=True)
class MetagraphSnapshot:
    """The subnet's uid -> hot/cold key assignments captured at a single block."""

    netuid: int
    block: int
    timestamp: dt.datetime
    neurons: tuple[NeuronInfo, ...]


@dc.dataclass(frozen=True, slots=True)
class MetagraphView:
    """What the weight setter needs from the metagraph: the uids, and who holds them."""

    uids: tuple[int, ...]
    uid_by_hotkey: dict[str, int]


@dc.dataclass(frozen=True, slots=True)
class SubnetParams:
    """Startup state: our own uid, and the subnet's weight timing."""

    uid: int
    tempo: int
    weights_rate_limit: int


@dc.dataclass(frozen=True, slots=True)
class PollState:
    """Per-tick chain state: the tip, and blocks since our uid last set weights."""

    current_block: int
    blocks_since_last_update: int


@dc.dataclass(frozen=True, slots=True)
class WeightPlan:
    """A uid-aligned vector, and whether it is fit to submit."""

    uids: tuple[int, ...]
    weights: tuple[float, ...]
    submittable: bool
    skip_reason: str | None
    summary: str
