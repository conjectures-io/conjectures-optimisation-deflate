"""The chain watcher: poll a `ChainSource`, publish each new block's state.

Pure orchestration with the IO injected -- it holds a source and a sink and depends on
neither the SDK nor the database. `step()` is the testable unit: advance-or-skip for one
tick. `run()` is the loop around it. The wired-up entry point is workers/chain_watcher.py.
"""

from __future__ import annotations

import time
from collections.abc import Callable

from loguru import logger

from .sink import SnapshotSink
from .source import ChainSource
from .types import NETUID, POLL_INTERVAL_SECONDS


def step(
    source: ChainSource, sink: SnapshotSink, netuid: int, last_block: int | None
) -> int | None:
    """One poll: if the tip advanced past `last_block`, snapshot and publish.

    Returns the block now considered last-seen. Pure with respect to source and sink --
    no sleeping, no looping -- so it can be driven directly in tests with fakes.
    """
    head = source.head()
    if last_block is not None and head.block <= last_block:
        return last_block
    metagraph = source.metagraph(netuid, head.block)
    sink.publish(head, metagraph)
    return head.block


def run(
    source: ChainSource,
    sink: SnapshotSink,
    *,
    netuid: int = NETUID,
    poll_interval: float = POLL_INTERVAL_SECONDS,
    sleep: Callable[[float], None] = time.sleep,
) -> None:
    """Poll forever, publishing each newly seen block.

    A transient query error is logged and retried on the next tick rather than killing
    the watcher: one bad block must never stop it, because a missed registration is a
    miner who cannot submit. `sleep` is injected so tests can run the loop
    deterministically or break out of it.
    """
    last_block: int | None = None
    try:
        while True:
            try:
                last_block = step(source, sink, netuid, last_block)
            except Exception as exc:  # noqa: BLE001 - one bad tick must not kill the watcher
                logger.exception(f"[watcher] poll failed: {exc}")
            sleep(poll_interval)
    except KeyboardInterrupt:
        logger.info("[watcher] interrupted")
