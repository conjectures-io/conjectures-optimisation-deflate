"""Generic bwrap sandbox: a declarative spec in, a plain result out.

Knows nothing about cargo, crates, corpora or benchmarks -- see bench.py for
that. This module only runs a command under a `Sandbox`; deciding what that
Sandbox should expose ("environment writing") is entirely the caller's job.
"""

from __future__ import annotations

import shutil
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

from loguru import logger


class Unavailable(RuntimeError):
    """The host cannot sandbox at all; never the sandboxed command's fault."""


@dataclass(frozen=True)
class Sandbox:
    """What a sandboxed command may see and use -- data, not action."""

    enabled: bool = True
    ro_binds: tuple[Path, ...] = ()
    rw_binds: tuple[Path, ...] = ()
    memory_mb: int = 0
    cpus: str = ""


@dataclass(frozen=True)
class Result:
    """A sandboxed command's outcome, independent of subprocess's own type."""

    returncode: int
    stdout: str
    stderr: str
    seconds: float


def check(enabled: bool) -> None:
    # Refuse to claim a sandbox is in force when bwrap cannot actually confine anything.
    if not enabled:
        return
    if not shutil.which("bwrap"):
        raise Unavailable("bubblewrap is not installed: `sudo apt install bubblewrap`.")
    probe = subprocess.run(_probe_argv(), capture_output=True, text=True)
    if probe.returncode != 0:
        raise Unavailable(
            "bubblewrap is installed but cannot create a sandbox here:\n  "
            + probe.stderr.strip().replace("\n", "\n  ")
            + "\n  On Ubuntu 24.04: "
            + "`sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`."
        )


def check_resources(sandbox: Sandbox) -> None:
    """Check requested systemd limits before attributing failures to a parser."""
    if not sandbox.enabled:
        return
    argv = _resource_wrap(sandbox, ["true"])
    if argv == ["true"]:
        return
    try:
        probe = subprocess.run(argv, capture_output=True, text=True, timeout=10)
    except subprocess.TimeoutExpired as e:
        raise Unavailable("systemd resource limits probe timed out") from e
    if probe.returncode != 0:
        raise Unavailable("systemd resource limits are unavailable: " + probe.stderr.strip())


def run(sandbox: Sandbox, cmd: list[str], *, cwd: Path | None, timeout: float) -> Result:
    # Confine `cmd` per `sandbox` and run it; the sandbox is the whole story.
    argv = _argv(sandbox) + cmd
    t0 = time.monotonic()
    try:
        r = subprocess.run(argv, capture_output=True, text=True, timeout=timeout, cwd=cwd)
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        return Result(124, out, f"timed out after {timeout:.0f}s", time.monotonic() - t0)
    logger.debug(f"[bwrap] {Path(cmd[0]).name} exit={r.returncode} in {time.monotonic() - t0:.1f}s")
    return Result(r.returncode, r.stdout, r.stderr, time.monotonic() - t0)


def _probe_argv() -> list[str]:
    return [
        "bwrap",
        "--ro-bind",
        "/",
        "/",
        "--dev",
        "/dev",
        "--proc",
        "/proc",
        "--unshare-all",
        "--die-with-parent",
        "true",
    ]


def _argv(sandbox: Sandbox) -> list[str]:
    if not sandbox.enabled:
        return []
    args = [
        "bwrap",
        "--ro-bind",
        "/",
        "/",
        "--dev",
        "/dev",
        "--proc",
        "/proc",
        "--tmpfs",
        "/tmp",
        "--unshare-all",
        "--die-with-parent",
    ]
    # bwrap refuses to bind onto a destination reached through a symlink (e.g. a
    # target/ shared across test runs); resolve so source and destination match.
    for p in sandbox.ro_binds:
        p = p.resolve()
        if p.exists():
            args += ["--ro-bind", str(p), str(p)]
    for p in sandbox.rw_binds:
        p = p.resolve()
        p.mkdir(parents=True, exist_ok=True)
        args += ["--bind", str(p), str(p)]
    args += ["--"]
    return _resource_wrap(sandbox, args)


def _resource_wrap(sandbox: Sandbox, args: list[str]) -> list[str]:
    props: list[str] = []
    if sandbox.memory_mb > 0:
        props += ["-p", f"MemoryMax={sandbox.memory_mb}M"]
    if sandbox.cpus:
        props += ["-p", f"AllowedCPUs={sandbox.cpus}"]
    if not props or not shutil.which("systemd-run"):
        return args
    return ["systemd-run", "--user", "--scope", "--quiet", *props] + args
