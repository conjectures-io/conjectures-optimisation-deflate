"""Where the watcher publishes what it reads -- the outbound seam.

The watcher does not write rows itself: it hands each (head, metagraph) pair to a
`SnapshotSink`. The production sink is `db.adapters.DatabaseSnapshotSink`, which
satisfies this Protocol structurally. `LoggingSink` is a trivial one so the watcher can
be exercised end to end without a database.
"""

from __future__ import annotations

from typing import Protocol, runtime_checkable

from loguru import logger

from .types import ChainHead, MetagraphSnapshot


@runtime_checkable
class SnapshotSink(Protocol):
    """A destination for chain snapshots. Must be idempotent per block."""

    def publish(self, head: ChainHead, metagraph: MetagraphSnapshot) -> None: ...


class LoggingSink:
    """A no-storage sink that just logs each snapshot -- for local runs and tests."""

    def publish(self, head: ChainHead, metagraph: MetagraphSnapshot) -> None:
        logger.info(
            f"[watcher] block={head.block} time={head.timestamp.isoformat()} "
            f"netuid={metagraph.netuid} neurons={len(metagraph.neurons)}"
        )
