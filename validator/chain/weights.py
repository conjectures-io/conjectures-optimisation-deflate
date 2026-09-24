"""The weight-setting seam: the worker's only view of the live network.

The live implementation is `finney.BittensorWeightChain`; tests pass a fake, which is
what lets the whole cadence and vector logic be exercised without a wallet or a node.
"""

from __future__ import annotations

from collections.abc import Sequence
from typing import Protocol, runtime_checkable

from .types import MetagraphView, PollState, SubnetParams


@runtime_checkable
class WeightChain(Protocol):
    def current_block(self) -> int:
        """Read the chain tip without requiring validator registration."""
        ...

    def params(self, netuid: int) -> SubnetParams:
        """Our uid plus the subnet's tempo and rate limit. Raises if not registered."""
        ...

    def poll(self, netuid: int, uid: int) -> PollState:
        """The tip, and blocks since our uid last set weights."""
        ...

    def metagraph(self, netuid: int) -> MetagraphView: ...

    def set_weights(self, netuid: int, uids: Sequence[int], weights: Sequence[float]) -> bool: ...
