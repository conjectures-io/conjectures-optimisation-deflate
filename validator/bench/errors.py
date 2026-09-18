"""What can go wrong, split by whose fault it is.

`Misconfigured` and `Malformed` are always the validator's own problem.
A verdict on a submission is never an exception -- it is in the data.
"""

from __future__ import annotations


class BenchError(RuntimeError):
    """Anything this package raises."""


class Misconfigured(BenchError):
    """The host, the config or the build is unusable; never a submission's fault."""


class Malformed(BenchError):
    """The engine produced something that cannot be read."""
