"""The chain: what the validator reads from the subnet, and what it writes back.

Seam-first, like the rest of the validator. Everything here is written against the two
protocols -- `ChainSource` for reading state, `WeightChain` for setting weights -- so the
watcher, the scorer and the weight setter never touch the bittensor SDK. `finney.py` is
the only file that does, and it is imported lazily so a miner who never installed the SDK
can still import this package.
"""

from __future__ import annotations

from .schedule import SetDecision, blocks_until_next_epoch, should_set
from .sink import LoggingSink, SnapshotSink
from .source import ChainSource
from .types import (
    ARCHIVE,
    BLOCK_SECONDS,
    FINNEY,
    NETUID,
    POLL_INTERVAL_SECONDS,
    ChainHead,
    MetagraphSnapshot,
    MetagraphView,
    NeuronInfo,
    PollState,
    SubnetParams,
    WeightPlan,
)
from .watcher import run, step
from .weights import WeightChain

__all__ = [
    "ARCHIVE",
    "BLOCK_SECONDS",
    "FINNEY",
    "NETUID",
    "POLL_INTERVAL_SECONDS",
    "BittensorChainSource",
    "BittensorWeightChain",
    "ChainHead",
    "ChainSource",
    "LoggingSink",
    "MetagraphSnapshot",
    "MetagraphView",
    "NeuronInfo",
    "PollState",
    "SetDecision",
    "SnapshotSink",
    "SubnetParams",
    "WeightChain",
    "WeightPlan",
    "blocks_until_next_epoch",
    "run",
    "should_set",
    "step",
]


def __getattr__(name: str) -> object:
    # The SDK is a heavy optional dependency (requirements-chain.txt), so the two live
    # implementations are imported only when actually asked for.
    if name in ("BittensorChainSource", "BittensorWeightChain"):
        from . import finney

        return getattr(finney, name)
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
