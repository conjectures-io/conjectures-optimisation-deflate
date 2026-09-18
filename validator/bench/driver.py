"""Benchmark protocol: parsers in, measurements out.

Makes a run workspace, generates one cdylib crate per parser (the incumbent
included, through the same pipeline), builds them in a sandbox that may write
only that workspace, then measures in a second sandbox that may write nothing.
One engine process per candidate, each measuring `{incumbent, candidate}`.

Returns data. It never prints, writes a result file or touches a database --
that is an entry point's job. What a Sandbox is and how it is enforced stays
`sandbox/bwrap.py`'s job; this module only decides what one should expose.

    VERIFY_SANDBOX=off                run without bubblewrap (never a validator)
    VERIFY_BENCH_TIMEOUT=300          seconds one build or one measurement may take
    VERIFY_BENCH_MEMORY_MB=2048       cgroup cap while measuring; 0 disables
    VERIFY_BENCH_BUILD_MEMORY_MB=4096 cgroup cap while building; 0 disables
    VERIFY_BENCH_CPUS=                e.g. "2-3"; cgroup AllowedCPUs, unset disables
    VERIFY_BENCH_REPS=11              timed reps per file per method
    VERIFY_BENCH_WARMUP=1             discarded reps before them
    VERIFY_BENCH_KEEP=auto            auto | always | never -- what to do with the workspace
    VERIFY_BENCH_WORKSPACE=<dir>      where run workspaces are made
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import tempfile
import time
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from enum import Enum
from pathlib import Path

from loguru import logger

from sandbox import bwrap

from .corpora import Corpus
from .errors import Malformed, Misconfigured
from .results import INCUMBENT, Run, incumbent_agreement
from .results import parse as parse_results

#: Relative to the repository root. Gitignored by `data/.gitignore`.
DEFAULT_WORKSPACE = "data/bench-workspace"

#: A method name becomes a directory name and a JSON key.
NAME = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")

#: The engine's exit code for "I could not measure at all"; `bwrap.run`'s for a timeout.
REFUSED = 2
TIMED_OUT = 124


class Keep(Enum):
    AUTO = "auto"
    ALWAYS = "always"
    NEVER = "never"


class Failed(RuntimeError):
    """A run that did not produce measurements, with its workspace left on disk."""

    def __init__(self, message: str, *, detail: str, workspace: Path) -> None:
        super().__init__(message)
        self.detail: str = detail
        self.workspace: Path = workspace


class Blamed(Failed):
    """A failure one parser is answerable for; carries which one."""

    def __init__(self, message: str, *, method: str, detail: str, workspace: Path) -> None:
        super().__init__(message, detail=detail, workspace=workspace)
        self.method: str = method


class BuildFailed(Blamed):
    """One parser did not compile."""

    def __init__(self, method: str, detail: str, workspace: Path) -> None:
        super().__init__(
            f"{method} does not build", method=method, detail=detail, workspace=workspace
        )


class Crashed(Blamed):
    """The engine died while measuring one parser: a signal, or the timeout.

    `catch_unwind` in the shim stops a panic here, but nothing stops a stack
    overflow or the memory cap. One process per candidate is what makes this
    survivable, and what says whose fault it was.
    """


class MeasureFailed(Failed):
    """The engine refused to measure at all. Not a verdict on any candidate."""


@dataclass(frozen=True)
class Config:
    """Everything a benchmark run needs that is not a parser or a corpus."""

    validator: Path
    workspace: Path
    enabled: bool = True
    timeout: float = 300.0
    memory_mb: int = 2048
    build_memory_mb: int = 4096
    cpus: str = ""
    reps: int = 11
    warmup: int = 1
    keep: Keep = Keep.AUTO
    #: Measure `miniz_oxide` and `libdeflate` alongside. Context for a report,
    #: never part of a verdict, and they cost more than the parsers do.
    bars: bool = True

    @classmethod
    def from_env(cls, validator: Path) -> Config:
        env = os.environ.get
        workspace = env("VERIFY_BENCH_WORKSPACE") or str(validator.parent / DEFAULT_WORKSPACE)
        return cls(
            validator=validator,
            workspace=Path(workspace),
            enabled=env("VERIFY_SANDBOX", "bwrap") != "off",
            timeout=float(env("VERIFY_BENCH_TIMEOUT", "300")),
            memory_mb=int(env("VERIFY_BENCH_MEMORY_MB", "2048")),
            build_memory_mb=int(env("VERIFY_BENCH_BUILD_MEMORY_MB", "4096")),
            cpus=env("VERIFY_BENCH_CPUS", ""),
            reps=max(int(env("VERIFY_BENCH_REPS", "11")), 1),
            warmup=max(int(env("VERIFY_BENCH_WARMUP", "1")), 0),
            keep=Keep(env("VERIFY_BENCH_KEEP", "auto")),
            bars=env("VERIFY_BENCH_BARS", "1") != "0",
        )

    @property
    def engine(self) -> Path:
        return self.validator / "measure/target/release/measure"

    @property
    def template(self) -> Path:
        return self.validator / "measure/candidate"

    @property
    def incumbent_source(self) -> Path:
        return self.validator / "incumbent/parse.rs"

    @property
    def toolchain(self) -> Path:
        return self.validator / "rust-toolchain.toml"


@dataclass(frozen=True)
class Measurement:
    """What one call to `run()` produced, and where it happened."""

    corpus: Corpus
    runs: tuple[Run, ...]
    workspace: Path
    kept: bool

    def only(self) -> Run:
        # The default shape: the incumbent and exactly one candidate.
        if len(self.runs) != 1:
            raise ValueError(f"{len(self.runs)} candidates were measured, not one")
        return self.runs[0]

    def candidates(self) -> tuple[str, ...]:
        return tuple(name for run in self.runs for name in run.candidates())

    def of(self, candidate: str) -> Run:
        for run in self.runs:
            if candidate in run.candidates():
                return run
        raise KeyError(candidate)

    def warnings(self) -> tuple[str, ...]:
        # What measuring the incumbent once per process says about the host.
        return incumbent_agreement(self.runs)


def check(config: Config) -> str:
    # Refuse to claim a sandbox that cannot confine anything; return the limits in force.
    try:
        bwrap.check(config.enabled)
    except bwrap.Unavailable as e:
        raise Misconfigured(str(e)) from e
    if not config.engine.exists():
        raise Misconfigured(f"the engine is not built: {config.engine} is missing")
    if not config.enabled:
        return "UNSANDBOXED, VERIFY_SANDBOX=off"
    capped = config.memory_mb > 0 and shutil.which("systemd-run")
    mem = f"{config.memory_mb} MB" if capped else "no cap"
    return f"bwrap, {config.timeout:.0f}s, {mem}, cpus={config.cpus or 'any'}"


def run(
    config: Config,
    candidates: Mapping[str, Path],
    corpus: Corpus,
    *,
    speed_floor: float | None = None,
) -> Measurement:
    """Measure each `parse.rs` in `candidates` against the incumbent on `corpus`."""
    _ = check(config)
    corpus.require()
    for name in candidates:
        _check_name(name)
    if not candidates:
        raise Misconfigured("nothing to measure")

    workspace = _make_workspace(config, candidates)
    try:
        crates = _generate(config, workspace, candidates)
        rustc = _rustc_version(config, workspace, crates[INCUMBENT])
        _build(config, workspace, crates)
        runs = tuple(
            _measure(config, workspace, corpus, name, crates, rustc, speed_floor)
            for name in sorted(candidates)
        )
    except BaseException:
        _cleanup(config, workspace, keep=True)
        raise
    kept = _cleanup(config, workspace, keep=_worth_keeping(runs))
    return Measurement(corpus=corpus, runs=runs, workspace=workspace, kept=kept)


def sweep(config: Config) -> None:
    """Remove every retained run workspace. `just bench-clean`."""
    if config.workspace.is_dir():
        shutil.rmtree(config.workspace)


def _check_name(name: str) -> None:
    if name == INCUMBENT:
        raise Misconfigured(f"{INCUMBENT!r} is the reference; a candidate needs another name")
    if not NAME.match(name):
        raise Misconfigured(f"{name!r} is not a usable method name")


def _make_workspace(config: Config, candidates: Mapping[str, Path]) -> Path:
    # A readable prefix for humans; the uniqueness comes from the OS, not the name.
    config.workspace.mkdir(parents=True, exist_ok=True)
    h = hashlib.sha256()
    for name in sorted(candidates):
        h.update(name.encode())
        h.update(candidates[name].read_bytes())
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    return Path(tempfile.mkdtemp(prefix=f"{stamp}-{h.hexdigest()[:8]}-", dir=config.workspace))


def _generate(config: Config, workspace: Path, candidates: Mapping[str, Path]) -> dict[str, Path]:
    # The incumbent goes through the same pipeline, so whatever the cdylib
    # boundary costs, it costs both sides and cancels in the ratio.
    sources = {INCUMBENT: config.incumbent_source, **candidates}
    crates: dict[str, Path] = {}
    for name, source in sources.items():
        crate = workspace / name
        (crate / "src").mkdir(parents=True)
        shutil.copyfile(config.template / "Cargo.toml", crate / "Cargo.toml")
        shutil.copyfile(config.template / "lib.rs", crate / "src/lib.rs")
        shutil.copyfile(config.toolchain, crate / "rust-toolchain.toml")
        shutil.copyfile(source, crate / "src/parse.rs")
        crates[name] = crate
    return crates


def _rustc_version(config: Config, workspace: Path, crate: Path) -> str:
    # Asked inside a generated crate, so `rust-toolchain.toml` decides -- the
    # workspace is outside validator/ and inherits nothing.
    r = bwrap.run(
        build_sandbox(config, workspace),
        ["rustc", "--version"],
        cwd=crate,
        timeout=config.timeout,
    )
    return r.stdout.strip() or "unknown"


def _build(config: Config, workspace: Path, crates: Mapping[str, Path]) -> None:
    sandbox = build_sandbox(config, workspace)
    for name, crate in crates.items():
        r = bwrap.run(
            sandbox,
            ["cargo", "build", "--release", "--offline", "-q"],
            cwd=crate,
            timeout=config.timeout,
        )
        logger.debug(f"[bench] built {name} in {r.seconds:.1f}s exit={r.returncode}")
        if r.returncode != 0:
            raise BuildFailed(name, (r.stderr or r.stdout).strip(), workspace)


def _measure(
    config: Config,
    workspace: Path,
    corpus: Corpus,
    candidate: str,
    crates: Mapping[str, Path],
    rustc: str,
    speed_floor: float | None,
) -> Run:
    cmd = [
        str(config.engine),
        str(corpus.path),
        f"{INCUMBENT}={crates[INCUMBENT]}",
        f"{candidate}={crates[candidate]}",
        "--corpus-name",
        corpus.name,
        "--reps",
        str(config.reps),
        "--warmup",
        str(config.warmup),
        "--rustc-version",
        rustc,
    ]
    if speed_floor is not None:
        cmd += ["--speed-floor", repr(speed_floor)]
    if not config.bars:
        cmd += ["--no-bars"]
    r = bwrap.run(
        measure_sandbox(config, workspace, corpus),
        cmd,
        cwd=None,
        timeout=config.timeout,
    )
    logger.debug(f"[bench] measured {candidate} in {r.seconds:.1f}s exit={r.returncode}")
    if r.returncode == REFUSED:
        raise MeasureFailed(
            f"the engine refused to measure {candidate}",
            detail=(r.stderr or r.stdout).strip(),
            workspace=workspace,
        )
    if r.returncode != 0:
        raise Crashed(
            f"the engine died ({_died(r.returncode)}) measuring {candidate}",
            method=candidate,
            detail=(r.stderr or r.stdout).strip(),
            workspace=workspace,
        )
    try:
        return parse_results(r.stdout, corpus)
    except Malformed as e:
        raise MeasureFailed(
            f"unreadable output measuring {candidate}: {e}",
            detail=r.stderr.strip(),
            workspace=workspace,
        ) from e


def build_sandbox(config: Config, workspace: Path) -> bwrap.Sandbox:
    # The one step that writes anything, and it may write only this run's workspace.
    cargo_home = Path(os.environ.get("CARGO_HOME", Path.home() / ".cargo"))
    rustup_home = Path(os.environ.get("RUSTUP_HOME", Path.home() / ".rustup"))
    return bwrap.Sandbox(
        enabled=config.enabled,
        ro_binds=(config.validator, rustup_home, cargo_home / "registry"),
        rw_binds=(workspace,),
        memory_mb=config.build_memory_mb,
        cpus=config.cpus,
    )


def measure_sandbox(config: Config, workspace: Path, corpus: Corpus) -> bwrap.Sandbox:
    # Nothing writable, a tighter cap, and whatever CPUs the operator reserved.
    return bwrap.Sandbox(
        enabled=config.enabled,
        ro_binds=(config.validator, workspace, corpus.path),
        rw_binds=(),
        memory_mb=config.memory_mb,
        cpus=config.cpus,
    )


def _died(returncode: int) -> str:
    if returncode == TIMED_OUT:
        return "timed out"
    if returncode < 0:
        return f"signal {-returncode}"
    return f"exit {returncode}"


def _worth_keeping(runs: Sequence[Run]) -> bool:
    # Leftovers are what you want after a bad run: keep the crates that misbehaved.
    return any(run.failures(name) for run in runs for name in run.candidates())


def _cleanup(config: Config, workspace: Path, *, keep: bool) -> bool:
    if config.keep is Keep.ALWAYS or (keep and config.keep is not Keep.NEVER):
        logger.debug(f"[bench] kept {workspace}")
        return True
    shutil.rmtree(workspace, ignore_errors=True)
    return False
