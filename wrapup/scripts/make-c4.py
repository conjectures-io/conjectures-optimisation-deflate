#!/usr/bin/env python3
"""C4, the fresh holdout (PLAN.md §3.2): a stratified sample of the scenario data.

Never published. Built from sources no miner was scored on, at natural sizes:
whole small files where the scenario has them (web assets, archive members),
slices at seeded offsets of the large ones (logs, genomics, large files), and the
filtered scanlines of PNGs (what IDAT compression really sees). Writes OUT/files/
and OUT/map.json for rank.py ({"c4/<file>": [category, source]}), plus
OUT/MANIFEST.tsv.

    make-c4.py DATA_DIR OUT_DIR [--seed N] [--budget-mb 40]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import zlib
from pathlib import Path

MiB = 1024 * 1024


def files_under(d: Path) -> list[Path]:
    return sorted(p for p in d.rglob("*") if p.is_file() and not p.name.startswith("."))


def png_scanlines(data: bytes) -> bytes | None:
    if data[:8] != b"\x89PNG\r\n\x1a\n":
        return None
    pos, idat = 8, bytearray()
    while pos + 12 <= len(data):
        n = int.from_bytes(data[pos:pos + 4], "big")
        if data[pos + 4:pos + 8] == b"IDAT":
            idat += data[pos + 8:pos + 8 + n]
        pos += 12 + n
    try:
        return zlib.decompress(bytes(idat))
    except zlib.error:
        return None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("data", type=Path)
    ap.add_argument("out", type=Path)
    ap.add_argument("--seed", type=int, default=4_2026_10_12)
    ap.add_argument("--budget-mb", type=float, default=40.0)
    a = ap.parse_args()
    rng = random.Random(a.seed)
    out_files = a.out / "files"
    out_files.mkdir(parents=True, exist_ok=True)
    per_cat = a.budget_mb * MiB / 7
    chosen: dict[str, tuple[str, str, bytes]] = {}

    def add(cat: str, source: str, name: str, data: bytes) -> None:
        key = f"{cat}--{name}".replace("/", "_")
        chosen[key] = (cat, source, data)

    def sample_whole(cat: str, root: Path, min_size: int = 1) -> None:
        pool = [p for p in files_under(root) if p.stat().st_size >= min_size]
        rng.shuffle(pool)
        used = 0
        for p in pool:
            if used >= per_cat:
                break
            if p.stat().st_size > per_cat / 4:
                continue
            data = p.read_bytes()
            rel = p.relative_to(root)
            add(cat, rel.parts[0], str(rel), data)
            used += len(data)

    def sample_slices(cat: str, root: Path, slice_size: int) -> None:
        pool = [p for p in files_under(root) if p.stat().st_size >= slice_size]
        per_file = max(1, int(per_cat // slice_size // max(1, len(pool))))
        for p in pool:
            size = p.stat().st_size
            with p.open("rb") as f:
                for k in range(per_file):
                    off = rng.randrange(0, size - slice_size + 1)
                    f.seek(off)
                    rel = p.relative_to(root)
                    add(cat, str(rel).split("/")[0] if "/" in str(rel) else p.name, f"{rel}@{off}", f.read(slice_size))

    d = a.data
    sample_whole("web", d / "s1-web", min_size=256)
    sample_slices("large", d / "s2-large", MiB)
    sample_slices("genomics", d / "s3-bgzf", MiB)
    # PNG scanlines, whole.
    used = 0
    pngs = files_under(d / "s4-png")
    rng.shuffle(pngs)
    for p in pngs:
        s = png_scanlines(p.read_bytes())
        if s and used < per_cat:
            add("image", p.parent.name, str(p.relative_to(d / "s4-png")) + ".scanlines", s)
            used += len(s)
    sample_whole("archive", d / "s5-archive", min_size=1)
    sample_slices("logs", d / "s6-logs", MiB)
    sample_slices("messages", d / "s7-messages", 256 * 1024)

    mapping, manifest = {}, []
    for key, (cat, source, data) in sorted(chosen.items()):
        (out_files / key).write_bytes(data)
        mapping[f"c4/{key}"] = [cat, f"{cat}:{source}"]
        manifest.append(f"{key}\t{len(data)}\t{hashlib.sha256(data).hexdigest()}")
    (a.out / "map.json").write_text(json.dumps(mapping, indent=0))
    (a.out / "MANIFEST.tsv").write_text("\n".join(manifest) + "\n")
    cats: dict[str, list[int]] = {}
    for cat, _s, data in chosen.values():
        cats.setdefault(cat, []).append(len(data))
    for cat, sizes in sorted(cats.items()):
        print(f"{cat:9} {len(sizes):5} files {sum(sizes) / MiB:7.1f} MiB")
    print(f"total {len(chosen)} files {sum(len(v[2]) for v in chosen.values()) / MiB:.1f} MiB -> {a.out}")


if __name__ == "__main__":
    main()
