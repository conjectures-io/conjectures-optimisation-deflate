#!/usr/bin/env python3
"""Unpack the PROD sources export into OUT/<id>/{parse.rs,Parse.lean}.

The export is the CSV from the PROD runbook in PLAN.md §2 (columns id, hotkey,
state, submitted_at, source_sha256, name, content_b64). Each parse.rs is checked
against its recorded source_sha256; also writes OUT/index.tsv (id, hotkey,
submitted_at, sha256).

    unpack-prod-sources.py EXPORT.csv.gz OUT_DIR
"""

from __future__ import annotations

import base64
import csv
import gzip
import hashlib
import sys
from collections import Counter
from pathlib import Path


def main() -> None:
    src, out = Path(sys.argv[1]), Path(sys.argv[2])
    csv.field_size_limit(sys.maxsize)
    names: Counter[str] = Counter()
    index, bad = [], []
    with gzip.open(src, "rt", newline="") as f:
        for r in csv.DictReader(f):
            d = out / r["id"]
            d.mkdir(parents=True, exist_ok=True)
            data = base64.b64decode(r["content_b64"])
            (d / r["name"]).write_bytes(data)
            names[r["name"]] += 1
            if r["name"] == "parse.rs":
                sha = hashlib.sha256(data).hexdigest()
                if r["source_sha256"] and sha != r["source_sha256"]:
                    bad.append(r["id"])
                index.append((int(r["id"]), r["hotkey"], r["submitted_at"], sha))
    index.sort()
    (out / "index.tsv").write_text("".join(f"{i}\t{h}\t{t}\t{s}\n" for i, h, t, s in index))
    print(f"{len(index)} submissions, files {dict(names)}, ids {index[0][0]}..{index[-1][0]}")
    if bad:
        print(f"source_sha256 mismatch: {bad}")
        sys.exit(1)


if __name__ == "__main__":
    main()
