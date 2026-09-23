"""Which corpora exist, where they live, and what may be said about them.

One `validator/corpora.toml` is the single answer for *policy* -- name, path,
held-out or not, which is the default -- replacing the `VERIFY_CORPUS` env var
and the `validator/corpus` symlink. Format labels are not policy, they describe
the data, so they live with the data: a `<name>.formats.json` sibling of each
corpus directory (see e.g. `scripts/make-benchmark-corpus.py`), not in this file.

    VERIFY_CORPUS   a corpus name from the config, or a directory; overrides the
                    entry marked `default = true`
"""

from __future__ import annotations

import json
import os
import tomllib
from collections.abc import Iterator, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import cast

from .errors import Misconfigured

CONFIG = "corpora.toml"


@dataclass(frozen=True)
class Corpus:
    name: str
    path: Path
    #: Per-file numbers may be reported back to whoever submitted. False means
    #: only aggregates leave the validator -- see `notes-sandboxed-benchmark.md`.
    public: bool
    #: Corpus file name to a human-chosen format label, for grouped analysis.
    formats: Mapping[str, str]

    def format_of(self, file: str) -> str:
        return self.formats.get(file, "unknown")

    def require(self) -> Corpus:
        # The config may name corpora this machine has not downloaded; fail where used.
        if not self.path.is_dir():
            raise Misconfigured(f"corpus {self.name}: {self.path} is not a directory")
        return self


@dataclass(frozen=True)
class Corpora:
    entries: tuple[Corpus, ...]
    default_name: str

    def __iter__(self) -> Iterator[Corpus]:
        return iter(self.entries)

    def names(self) -> str:
        return ", ".join(c.name for c in self.entries)

    def missing(self) -> tuple[str, ...]:
        return tuple(c.name for c in self.entries if not c.path.is_dir())

    def by_name(self, name: str) -> Corpus:
        for c in self.entries:
            if c.name == name:
                return c.require()
        raise Misconfigured(f"no corpus named {name}; the config has: {self.names()}")

    def default(self) -> Corpus:
        # VERIFY_CORPUS wins: a configured name, or an ad-hoc directory.
        override = os.environ.get("VERIFY_CORPUS", "").strip()
        if override:
            if any(c.name == override for c in self.entries):
                return self.by_name(override)
            return adhoc(Path(override)).require()
        if self.default_name:
            return self.by_name(self.default_name)
        return self.entries[0].require()


def load(validator: Path) -> Corpora:
    config = validator / CONFIG
    try:
        raw = _as_dict(cast("object", tomllib.loads(config.read_text())))
    except FileNotFoundError:
        raise Misconfigured(f"{config} is missing") from None
    except tomllib.TOMLDecodeError as e:
        raise Misconfigured(f"{config}: {e}") from None
    listed = raw.get("corpus", [])
    if not isinstance(listed, list) or not listed:
        raise Misconfigured(f"{config} must hold at least one [[corpus]] entry")
    entries = [_as_dict(e) for e in cast("list[object]", listed)]
    parsed = tuple(_corpus(config, validator.parent, e) for e in entries)
    marked = [c.name for c, e in zip(parsed, entries) if e.get("default") is True]
    if len(marked) > 1:
        raise Misconfigured(f"{config}: more than one corpus marked default: {', '.join(marked)}")
    return Corpora(entries=parsed, default_name=marked[0] if marked else "")


def default(validator: Path) -> Corpus:
    return load(validator).default()


def gate_corpora(validator: Path) -> tuple[Corpus, ...]:
    """The full gate evaluates both competition corpora unless explicitly overridden."""
    registry = load(validator)
    if os.environ.get("VERIFY_CORPUS", "").strip():
        selected = (registry.default(),)
    else:
        selected = tuple(registry.by_name(name) for name in ("corpus-stage1", "corpus-stage2"))
    for corpus in selected:
        if not any(corpus.path.iterdir()):
            raise Misconfigured(f"corpus {corpus.name} is empty; run just corpus-pull")
    return selected


def adhoc(path: Path) -> Corpus:
    # A directory nobody configured carries no held-out policy, so it is public.
    # If you hold a corpus back, give it an entry.
    resolved = path.resolve()
    return Corpus(name=path.name, path=resolved, public=True, formats=_load_formats(resolved))


def _as_dict(v: object) -> dict[str, object]:
    if not isinstance(v, dict):
        raise Misconfigured(f"expected a table, got {type(v).__name__}")
    return cast("dict[str, object]", v)


def _load_formats(path: Path) -> dict[str, str]:
    sidecar = path.with_name(f"{path.name}.formats.json")
    if not sidecar.is_file():
        return {}
    try:
        raw = cast("object", json.loads(sidecar.read_text()))
    except json.JSONDecodeError as e:
        raise Misconfigured(f"{sidecar}: {e}") from None
    if not isinstance(raw, dict):
        raise Misconfigured(f"{sidecar}: expected a JSON object")
    items = cast("dict[object, object]", raw).items()
    return {str(k): str(v) for k, v in items if k != "_comment" and isinstance(v, str)}


def _corpus(config: Path, root: Path, entry: Mapping[str, object]) -> Corpus:
    name = entry.get("name")
    path = entry.get("path")
    if not isinstance(name, str) or not name:
        raise Misconfigured(f"{config}: every [[corpus]] needs a name")
    if not isinstance(path, str) or not path:
        raise Misconfigured(f"{config}: corpus {name} needs a path")
    public = entry.get("public", True)
    if not isinstance(public, bool):
        raise Misconfigured(f"{config}: corpus {name}: public must be true or false")
    resolved = (root / path).resolve()
    return Corpus(name=name, path=resolved, public=public, formats=_load_formats(resolved))
