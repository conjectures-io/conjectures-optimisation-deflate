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
    """Per-tick chain state: the tip, blocks since our uid last set weights, and the block of
    the subnet's most recent epoch (LastMechansimStepBlock), all read at the tip."""

    current_block: int
    blocks_since_last_update: int
    last_epoch_block: int


@dc.dataclass(frozen=True, slots=True)
class WeightPlan:
    """A uid-aligned vector, and whether it is fit to submit."""

    uids: tuple[int, ...]
    weights: tuple[float, ...]
    submittable: bool
    skip_reason: str | None
    summary: str


@dc.dataclass(frozen=True, slots=True)
class NeuronEmission:
    """What one uid was emitted in an epoch, in alpha rao, and who held it then."""

    uid: int
    hotkey: str
    coldkey: str
    emission_rao: int
    incentive: float


@dc.dataclass(frozen=True, slots=True)
class EpochEmission:
    """The subnet's most recent epoch, read at one block: what each uid received from it.

    `epoch_block` is the chain's LastMechansimStepBlock, the epoch's identity. The bounty
    ledger records each epoch once, so reading the same one on every tick is harmless.
    `reveal_epochs` is 0 without commit-reveal: how many epochs a vector set now waits
    before consensus reads it.
    """

    epoch_block: int
    block: int
    tempo: int
    reveal_epochs: int
    neurons: tuple[NeuronEmission, ...]

    @property
    def miner_pool_rao(self) -> int:
        # What the epoch paid for incentive: the uids that earned any. A validator uid's
        # dividends are in Emission too, but it has no incentive, so it is left out.
        return sum(n.emission_rao for n in self.neurons if n.incentive > 0)
