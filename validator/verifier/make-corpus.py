#!/usr/bin/env python3
"""Build the scoring corpus.

    verifier/make-corpus.py [source-root ...]

Five files, deliberately different in kind, because a corpus of one kind measures
one kind of parse. This is not fussiness: the first headroom measurement in this
project's research phase used repetitive synthetic data, compressed ~300:1, was
dominated by match emission, and reported a conclusion that was backwards.
`docs/SCORING.md` records the trap.

In a real round the corpus is **held out and commit-revealed**, and only its
*shape* statistics are published -- byte-frequency histograms, mean line length,
the proportion of each kind -- so that miners tune for the class of data rather
than for the bytes. Here it is built from local sources and printed with hashes so
that a number in the docs can be rechecked.
"""
import hashlib
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "corpus"

DEFAULT_ROOTS = [
    ROOT.parent,                                    # this repository
    ROOT.parent.parent / "conjectures-research",
    ROOT.parent.parent / "conjectures-rust",
    ROOT.parent.parent / "conjectures-validator",
]

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
BIN_DIRS = ["validator/harness/target/release", "validator/slot/target/release"]


def walk(roots, exts, cap, allow_target=False):
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


def main():
    roots = [pathlib.Path(a) for a in sys.argv[1:]] or DEFAULT_ROOTS
    OUT.mkdir(exist_ok=True)
    for old in OUT.iterdir():
        if old.is_file():
            old.unlink()
    total, empty = 0, []
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
        sys.exit("corpus is empty -- pass source roots on the command line")
    if empty:
        print(f"\nWARNING: {', '.join(empty)} came out empty. A corpus of one kind")
        print("measures one kind of parse; see docs/SCORING.md.")
        if "binary.bin" in empty:
            print("For binary.bin, build the crates first (`just build`).")


if __name__ == "__main__":
    main()
