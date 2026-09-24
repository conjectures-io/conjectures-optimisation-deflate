"""The live chain, backed by the bittensor SDK -- the only file here that touches it.

Both implementations live together because they share the one thing worth isolating:
SDK objects (tensors, the substrate handle, the wallet) never escape this module.
Callers get the plain contracts from types.py, which is what lets everything else treat
a live node as just one of several interchangeable sources.

The SDK is in requirements-chain.txt, installed by `./setup.sh --chain`. Importing this
module without it is an ImportError by design: a validator that meant to talk to the
chain should find out at startup, not at the first poll.
"""

from __future__ import annotations

import datetime as dt
from collections.abc import Sequence
from typing import Protocol, SupportsFloat, SupportsInt, cast

from loguru import logger

try:
    import bittensor as bt
except ModuleNotFoundError as exc:  # pragma: no cover - depends on how the venv was built
    # The SDK is an optional, heavy dependency that only the two chain workers need, so a
    # miner's venv does not have it. Say what to run rather than leaving a bare import error.
    raise ModuleNotFoundError(
        "the bittensor SDK is not installed. It is needed only by the chain watcher and "
        "the weight setter; install it with `./setup.sh --chain` (or "
        "`pip install -r requirements-chain.txt`)."
    ) from exc

from .types import (
    ARCHIVE,
    FINNEY,
    ChainHead,
    MetagraphSnapshot,
    MetagraphView,
    NeuronInfo,
    PollState,
    SubnetParams,
)


class _SdkScalar(Protocol):
    """A 0-d numpy/torch scalar, whichever backend built it: `Metagraph.n` and `.block`."""

    def item(self) -> int: ...


class _SdkIntVector(Protocol):
    """A 1-d vector of integers: `Metagraph.uids`."""

    def __getitem__(self, index: int, /) -> SupportsInt: ...
    def __len__(self) -> int: ...


class _SdkFloatVector(Protocol):
    """A 1-d vector of floats: `Metagraph.stake`."""

    def __getitem__(self, index: int, /) -> SupportsFloat: ...
    def __len__(self) -> int: ...


class _SdkKeyVector(Protocol):
    """A 1-d vector whose elements stringify to ss58 addresses: `.hotkeys`/`.coldkeys`."""

    def __getitem__(self, index: int, /) -> object: ...
    def __len__(self) -> int: ...


class _SdkMetagraph(Protocol):
    """The slice of `bittensor.Metagraph` this module reads.

    The SDK assigns `n`/`block`/`uids`/`hotkeys`/`coldkeys`/`stake` to a numpy array, a
    torch tensor or a plain list depending on how the metagraph was built, and never
    declares a common type for them -- to a type checker every attribute is Unknown. This
    protocol is the boundary that pins each one down to what `to_snapshot` and
    `BittensorWeightChain.metagraph` actually do with it.
    """

    n: _SdkScalar
    block: _SdkScalar
    uids: _SdkIntVector
    hotkeys: _SdkKeyVector
    coldkeys: _SdkKeyVector
    stake: _SdkFloatVector


def _as_metagraph(meta: object) -> _SdkMetagraph:
    """Pin an SDK metagraph to the protocol above.

    A plain `meta: _SdkMetagraph = ...` annotation is not enough here: since the SDK's own
    attributes are themselves Unknown (not just untyped, but inferred from a mix of numpy,
    torch and dict-literal assignments internally), pyright widens the declared type back
    to `Unknown | _SdkMetagraph` instead of narrowing to it. `cast` is the one construct
    that actually pins it -- an explicit, single-line assertion of the real shape, at the
    one place any of this ever touches the SDK.
    """
    return cast(_SdkMetagraph, meta)


def to_snapshot(netuid: int, meta: _SdkMetagraph, timestamp: dt.datetime) -> MetagraphSnapshot:
    """Map an SDK metagraph to the plain snapshot, stamped with `timestamp`.

    Each neuron carries its registration block height read straight from the payload --
    no chain lookup. Its wall-clock time is resolved later and only for uids that
    actually changed. A uid whose registration block is missing from a degraded payload
    falls back to the snapshot block rather than crashing the watcher.

    Pure: it takes the already-fetched SDK object, so the mapping is testable without a
    live node.
    """
    count = meta.n.item()
    snapshot_block = meta.block.item()
    reg_blocks: Sequence[SupportsInt] = getattr(meta, "block_at_registration", None) or []
    neurons = tuple(
        NeuronInfo(
            uid=int(meta.uids[i]),
            hotkey=str(meta.hotkeys[i]),
            coldkey=str(meta.coldkeys[i]),
            stake=float(meta.stake[i]),
            block_at_registration=int(reg_blocks[i]) if i < len(reg_blocks) else snapshot_block,
        )
        for i in range(count)
    )
    return MetagraphSnapshot(
        netuid=netuid, block=snapshot_block, timestamp=timestamp, neurons=neurons
    )


class _HasScaleValue(Protocol):
    """A decoded SCALE query result: `substrate.query(...)`."""

    value: object


class _SubstrateClient(Protocol):
    """The one `substrate-interface` call this module makes.

    The real method also takes `params`, `raw_storage_key` and `subscription_handler`,
    none of which we use; the SDK declares one of them (`params`) as `list[Unknown]`,
    which would otherwise mark every call to the real method as partially unknown.
    """

    def query(
        self, module: str, storage_function: str, *, block_hash: str | None = None
    ) -> _HasScaleValue: ...


class BittensorChainSource:
    """Reads subnet chain state from a live node.

    `network` is anything `bt.Subtensor` accepts -- a named network ("finney", "test",
    "local") or a node URL. A neuron's registration block is usually older than a lite
    node's pruned-state window, so its on-chain time cannot be read from `network`; those
    lookups go to a separate archive node, connected lazily on first use and memoised. A
    block's time never changes, so each distinct registration block costs one archive RPC
    for the worker's lifetime. Pass `subtensor` / `archive` to inject connected or fake
    clients in tests.
    """

    def __init__(
        self,
        network: str = FINNEY,
        *,
        archive_network: str = ARCHIVE,
        subtensor: bt.Subtensor | None = None,
        archive: bt.Subtensor | None = None,
    ) -> None:
        self._network: str = network
        self._archive_network: str = archive_network
        self._subtensor: bt.Subtensor = subtensor or bt.Subtensor(network=network)
        logger.info(f"[chain] connected to {network}")
        self._archive: bt.Subtensor | None = archive
        self._block_time_cache: dict[int, dt.datetime] = {}

    def _archive_subtensor(self) -> bt.Subtensor:
        # Deferred until a historical block time is needed, so a watcher that never sees
        # a registration never pays for the connection.
        if self._archive is None:
            self._archive = bt.Subtensor(network=self._archive_network)
            logger.info(f"[chain] connected to archive {self._archive_network}")
        return self._archive

    @staticmethod
    def _query_block_time(subtensor: bt.Subtensor, block: int) -> dt.datetime:
        # On-chain time is milliseconds since the epoch (the Timestamp.Now storage value).
        block_hash = subtensor.get_block_hash(block)
        substrate = cast(_SubstrateClient, subtensor.substrate)
        # `.value` is `Any`: the substrate client's query result is generic over the
        # storage item's on-chain SCALE type, which isn't known until the call is made.
        raw_ms = cast(int, substrate.query("Timestamp", "Now", block_hash=block_hash).value)
        return dt.datetime.fromtimestamp(raw_ms / 1000, tz=dt.timezone.utc)

    def registration_block_time(self, block: int) -> dt.datetime:
        """On-chain time of a registration block, via the archive node, memoised.

        The store calls this only for uids whose keys changed -- a handful in steady
        state, the whole subnet once on an empty-database backfill -- so the archive is
        touched only when there is a real registration to timestamp.
        """
        cached = self._block_time_cache.get(block)
        if cached is None:
            cached = self._query_block_time(self._archive_subtensor(), block)
            self._block_time_cache[block] = cached
        return cached

    def head(self) -> ChainHead:
        block = self._subtensor.get_current_block()
        # The head is recent, so its time is on the lite node -- no archive needed.
        return ChainHead(block=block, timestamp=self._query_block_time(self._subtensor, block))

    def metagraph(self, netuid: int, block: int | None = None) -> MetagraphSnapshot:
        meta = _as_metagraph(self._subtensor.metagraph(netuid=netuid, block=block))
        return to_snapshot(netuid, meta, self._query_block_time(self._subtensor, meta.block.item()))


class BittensorWeightChain:
    """Sets weights with the validator's wallet, and reads the timing that governs when."""

    def __init__(
        self,
        *,
        network: str = FINNEY,
        wallet_name: str = "default",
        wallet_hotkey: str = "default",
        wallet_path: str = "~/.bittensor/wallets",
        subtensor: bt.Subtensor | None = None,
        wallet: bt.Wallet | None = None,
    ) -> None:
        self._subtensor: bt.Subtensor = (
            subtensor if subtensor is not None else bt.Subtensor(network=network)
        )
        self._wallet: bt.Wallet = (
            wallet
            if wallet is not None
            else bt.Wallet(name=wallet_name, hotkey=wallet_hotkey, path=wallet_path)
        )
        logger.info(f"[chain] connected to {network} as wallet {wallet_name}/{wallet_hotkey}")

    def current_block(self) -> int:
        return int(self._subtensor.get_current_block())

    def params(self, netuid: int) -> SubnetParams:
        uid = self._subtensor.get_uid_for_hotkey_on_subnet(self._wallet.hotkey.ss58_address, netuid)
        if uid is None:
            raise RuntimeError(f"the wallet hotkey is not registered on netuid {netuid}")
        tempo = self._subtensor.tempo(netuid)
        rate_limit = self._subtensor.weights_rate_limit(netuid)
        return SubnetParams(
            uid=int(uid),
            tempo=int(tempo) if tempo is not None else 0,
            weights_rate_limit=int(rate_limit) if rate_limit is not None else 0,
        )

    def poll(self, netuid: int, uid: int) -> PollState:
        block = int(self._subtensor.get_current_block())
        since = self._subtensor.blocks_since_last_update(netuid, uid, block=block)
        return PollState(
            current_block=block, blocks_since_last_update=int(since) if since is not None else 0
        )

    def metagraph(self, netuid: int) -> MetagraphView:
        meta = _as_metagraph(self._subtensor.metagraph(netuid=netuid))
        count = meta.n.item()
        return MetagraphView(
            uids=tuple(int(meta.uids[i]) for i in range(count)),
            uid_by_hotkey={str(meta.hotkeys[i]): int(meta.uids[i]) for i in range(count)},
        )

    def set_weights(self, netuid: int, uids: Sequence[int], weights: Sequence[float]) -> bool:
        response = self._subtensor.set_weights(
            wallet=self._wallet,
            netuid=netuid,
            uids=list(uids),
            weights=list(weights),
            wait_for_inclusion=True,
            wait_for_finalization=False,
        )
        if not response.success:
            logger.warning(
                f"[chain] set_weights rejected (error={response.error} message={response.message})"
            )
        return bool(response.success)
