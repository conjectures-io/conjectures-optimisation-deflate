"""The benchmark protocol: what is measured, how, and what comes back.

`driver` runs it, `corpora` says what it runs against, `results` is the shape of
the answer. Confining the untrusted part is `sandbox/bwrap.py`'s job, not this
package's.
"""

from .corpora import Corpora, Corpus
from .driver import (
    Blamed,
    BuildFailed,
    Config,
    Crashed,
    Failed,
    Keep,
    MeasureFailed,
    Measurement,
    build_sandbox,
    check,
    measure_sandbox,
    run,
    sweep,
)
from .errors import BenchError, Malformed, Misconfigured
from .results import INCUMBENT, FileResult, MethodResult, Run, Totals

__all__ = [
    "INCUMBENT",
    "BenchError",
    "Blamed",
    "BuildFailed",
    "Crashed",
    "Config",
    "Corpora",
    "Corpus",
    "Failed",
    "FileResult",
    "Keep",
    "MeasureFailed",
    "Measurement",
    "Malformed",
    "MethodResult",
    "Misconfigured",
    "Run",
    "Totals",
    "build_sandbox",
    "check",
    "measure_sandbox",
    "run",
    "sweep",
]
