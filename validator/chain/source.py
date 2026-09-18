"""The interface for receiving chain state -- the watcher's only view of a data source.

`ChainSource` is the seam that makes the source interchangeable: the watcher is written
entirely against this protocol, never against the bittensor SDK. The live implementation
is `finney.BittensorChainSource`, but any object with these two methods works -- a replay
out of the database, a recorded fixture, or an in-memory fake in tests.
"""

from __future__ import annotations

from typing import Protocol, runtime_checkable

from .types import ChainHead, MetagraphSnapshot


@runtime_checkable
class ChainSource(Protocol):
    """A read-only source of subnet chain state."""

    def head(self) -> ChainHead:
        """The current chain tip: latest block number and its timestamp."""
        ...

    def metagraph(self, netuid: int, block: int | None = None) -> MetagraphSnapshot:
        """The metagraph snapshot for `netuid`, at `block` if given else the tip."""
        ...
