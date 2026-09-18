#!/usr/bin/env python3
"""Build the scoring corpus - five files of different kinds, so the score measures every parse.

    verifier/make-corpus.py [source-root ...] [--force] [--allow-partial]

The committed corpus is the reference every byte count was measured against; rerunning this
replaces it (`git checkout data/benchmark/corpus-initial` restores). A live service scores
against whatever validator/corpora.toml or VERIFY_CORPUS names instead.
"""

import hashlib
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT.parent / "data/benchmark/corpus-initial"

# With no roots given, this repository alone; a held-out corpus passes its own.
DEFAULT_ROOTS = [ROOT.parent]

# (name, extensions, cap in bytes)
PARTS = [
    ("source.rs.txt", {".rs", ".toml", ".py"}, 2_000_000),
    ("prose.md.txt", {".md"}, 2_000_000),
    ("lean.txt", {".lean"}, 2_000_000),
    ("json.txt", {".json", ".lock"}, 1_000_000),
    ("binary.bin", {".rlib", ".so", ""}, 2_000_000),
]

SKIP_PARTS = {".lake", ".git", "packages", "corpus", "node_modules", "target"}
# `target/` is skipped for text but is the only source of binaries, so the binary
# part is collected from release build directories explicitly.
BIN_DIRS = ["validator/measure/target/release", "validator/slot/target/release"]


def walk(roots: list[pathlib.Path], exts: set[str], cap: int, allow_target: bool = False) -> bytes:
    buf = bytearray()
    for base in roots:
        base = pathlib.Path(base)
        if not base.exists():
            continue
        for p in sorted(base.rglob("*")):
            if len(buf) >= cap:
                break
            parts = set(p.parts)
            if parts & SKIP_PARTS and not allow_target:
                continue
            if not p.is_file() or p.suffix not in exts:
                continue
            try:
                b = p.read_bytes()
            except OSError:
                continue
            if len(b) > 4_000_000 or len(b) == 0:
                continue
            buf += b
    return bytes(buf[:cap])


def main() -> None:
    roots = [pathlib.Path(a) for a in sys.argv[1:] if not a.startswith("-")] or DEFAULT_ROOTS
    OUT.mkdir(exist_ok=True)
    if any(OUT.iterdir()) and "--force" not in sys.argv:
        sys.exit(
            "data/benchmark/corpus-initial/ is not empty. This would replace the\n"
            "reference corpus every byte count in the docs was measured against.\n"
            "Pass --force if that is what you mean;\n"
            "`git checkout data/benchmark/corpus-initial` puts it back."
        )
    for old in OUT.iterdir():
        if old.is_file():
            old.unlink()
    total = 0
    empty: list[str] = []
    print(f"{'file':<18} {'bytes':>10}  sha256")
    for name, exts, cap in PARTS:
        if name == "binary.bin":
            data = walk([ROOT.parent / d for d in BIN_DIRS], exts, cap, allow_target=True)
        else:
            data = walk(roots, exts, cap)
        if len(data) < 4096:
            empty.append(name)
            print(f"{name:<18} {'SKIPPED':>10}  (nothing found)")
            continue
        (OUT / name).write_bytes(data)
        total += len(data)
        print(f"{name:<18} {len(data):>10}  {hashlib.sha256(data).hexdigest()[:16]}")
    print(f"{'TOTAL':<18} {total:>10}")
    if total == 0:
        sys.exit("corpus is empty - pass source roots on the command line")
    if empty:
        hint = " Build the crates first (`just build`)." if "binary.bin" in empty else ""
        msg = f"{', '.join(empty)} came out empty: one kind measures one kind of parse.{hint}"
        if "--allow-partial" not in sys.argv:
            for f in OUT.iterdir():
                f.unlink()
            sys.exit(
                f"REFUSED: {msg} Pass more source roots, or --allow-partial to keep it anyway."
            )
        print(f"\nWARNING: {msg}")


if __name__ == "__main__":
    main()
