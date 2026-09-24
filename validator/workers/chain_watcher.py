"""Stream subnet registrations into the store.

This is the production wiring the `chain` package leaves injectable: a live Finney
source, and a sink that turns each snapshot into `registrations` rows. The polling loop,
the advance-or-skip logic and the per-tick error handling all live in `chain.watcher`;
this module only builds the pair and hands them over.

    cd validator && python -m workers.chain_watcher

It needs the bittensor SDK, so run `./setup.sh --chain` first. Without this worker no
hotkey has a registration, and so nobody can submit -- it is not optional on a live
validator.
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass
from pathlib import Path

from loguru import logger

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import db  # noqa: E402
from chain.types import ARCHIVE, FINNEY, NETUID, POLL_INTERVAL_SECONDS  # noqa: E402
from chain.watcher import run  # noqa: E402
from db.adapters import DatabaseSnapshotSink  # noqa: E402
from observability.axiom import config_error, init  # noqa: E402


@dataclass(frozen=True, slots=True)
class ChainWatcherConfig:
    network: str = FINNEY
    # Archive node for historical block times: a registration block is usually older than
    # the lite node's pruned-state window.
    archive_network: str = ARCHIVE
    netuid: int = NETUID
    poll_interval: float = POLL_INTERVAL_SECONDS

    @classmethod
    def from_env(cls) -> ChainWatcherConfig:
        d = cls()
        return cls(
            network=os.getenv("BITTENSOR_NETWORK", d.network),
            archive_network=os.getenv("BITTENSOR_ARCHIVE_NETWORK", d.archive_network),
            netuid=int(os.getenv("NETUID", str(d.netuid))),
            poll_interval=float(os.getenv("CHAIN_POLL_SECONDS", str(d.poll_interval))),
        )


def main() -> None:
    from chain.finney import BittensorChainSource

    events = init("competition-chain-watcher")
    try:
        config = ChainWatcherConfig.from_env()
    except Exception as exc:
        events.error("service_misconfigured", error=config_error(exc))
        raise
    events.bind(netuid=config.netuid, network=config.network)
    store = db.connect()
    reason = "crashed"
    try:
        source = BittensorChainSource(
            network=config.network, archive_network=config.archive_network
        )
        # The store stamps each registration's block_date by resolving its height's
        # on-chain time through the source's archive-backed, cached resolver -- invoked
        # only for changed uids, so the archive is hit only on a real registration.
        sink = DatabaseSnapshotSink(store.registrations, source.registration_block_time)
        logger.info(
            f"[watcher] starting network={config.network} archive={config.archive_network} "
            f"netuid={config.netuid} poll={config.poll_interval:.1f}s"
        )
        events.info(
            "service_started",
            archive_network=config.archive_network,
            poll_interval_seconds=config.poll_interval,
        )
        run(source, sink, netuid=config.netuid, poll_interval=config.poll_interval)
        reason = "interrupted"  # run() returns only on KeyboardInterrupt
    finally:
        events.info("service_stopped", reason=reason)
        store.close()


if __name__ == "__main__":
    main()
