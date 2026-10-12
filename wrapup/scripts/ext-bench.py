#!/usr/bin/env python3
"""External command-line compressors, in `arena bench`'s JSONL schema.

Each tool runs once per file per round (interleaved, as `arena bench` does), and
its time includes process start-up (about a millisecond; it matters only for tiny
files, which the report must say). Every output is checked: gzip output must
decompress to the input; PNG output must hold a valid zlib IDAT stream (the
optimisers change filters, so pixels are not compared byte for byte here).

    ext-bench.py --corpus DIR --label NAME --tool NAME... [--reps 3] [--warmup 1] [--out FILE]

Tools: gzip-1..9, pigz-6, pigz-9, pigz-11 (zopfli inside pigz), igzip-0..3,
7z-gzip-9, zopfli-15, oxipng-4, zopflipng-m. TOOLS_DIR (default
/root/deflate-wrapup/tools/bin) is put first on PATH.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import platform
import statistics
import subprocess
import tempfile
import time
import zlib
from pathlib import Path


def tool_cmd(name: str, src: Path, dst: Path) -> list[str] | str:
    kind, _, arg = name.rpartition("-")
    if kind == "gzip":
        return f"gzip -{arg} -c -n '{src}' > '{dst}'"
    if kind == "pigz":
        return f"pigz -p 1 -{arg} -c -n '{src}' > '{dst}'"
    if kind == "igzip":
        return f"igzip -{arg} -c '{src}' > '{dst}'"
    if name == "7z-gzip-9":
        return ["7zz", "a", "-bd", "-bso0", "-tgzip", "-mx9", str(dst), str(src)]
    if name == "zopfli-15":
        return f"zopfli --i15 -c '{src}' > '{dst}'"
    if name == "oxipng-4":
        return ["oxipng", "-q", "-o", "4", "--out", str(dst), str(src)]
    if name == "zopflipng-m":
        return ["zopflipng", "-m", "-y", "--lossy_transparent=false", str(src), str(dst)]
    raise SystemExit(f"unknown tool {name}")


def output_format(name: str) -> str:
    return "png" if name in ("oxipng-4", "zopflipng-m") else "gzip"


def check(fmt: str, out: bytes, original: bytes) -> str | None:
    if fmt == "gzip":
        try:
            return None if gzip.decompress(out) == original else "decompressed bytes differ"
        except Exception as e:  # noqa: BLE001 - any failure is a verdict
            return f"not gzip: {e}"
    pos, idat = 8, bytearray()
    if out[:8] != b"\x89PNG\r\n\x1a\n":
        return "not a PNG"
    while pos + 12 <= len(out):
        n = int.from_bytes(out[pos:pos + 4], "big")
        if out[pos + 4:pos + 8] == b"IDAT":
            idat += out[pos + 8:pos + 8 + n]
        pos += 12 + n
    try:
        zlib.decompress(bytes(idat))
    except zlib.error as e:
        return f"IDAT: {e}"
    return None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", type=Path, required=True)
    ap.add_argument("--label", default="corpus")
    ap.add_argument("--tool", action="append", required=True)
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--warmup", type=int, default=1)
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    tools_dir = os.environ.get("TOOLS_DIR", "/root/deflate-wrapup/tools/bin")
    env = dict(os.environ, PATH=f"{tools_dir}:{os.environ.get('PATH', '')}")
    out = a.out.open("w") if a.out else None

    def emit(obj: dict) -> None:
        line = json.dumps(obj)
        if out:
            out.write(line + "\n")
            out.flush()
        else:
            print(line, flush=True)

    emit({"kind": "meta", "schema": 1, "label": a.label, "corpus_dir": str(a.corpus), "mode": "Whole",
          "external": True, "reps": a.reps, "warmup": a.warmup, "started_at_unix": time.time(),
          "host": platform.node(), "loadavg": Path("/proc/loadavg").read_text().strip(),
          "methods": {t: None for t in a.tool}})
    files = sorted(p for p in a.corpus.rglob("*") if p.is_file() and not p.name.startswith("."))
    with tempfile.TemporaryDirectory() as tmp:
        for f in files:
            data = f.read_bytes()
            acc = {t: {"bytes": None, "verified": False, "error": None, "times": []} for t in a.tool}
            for rnd in range(a.warmup + a.reps):
                for t in a.tool:
                    st = acc[t]
                    if st["error"]:
                        continue
                    dst = Path(tmp) / f"out-{t}"
                    dst.unlink(missing_ok=True)
                    cmd = tool_cmd(t, f, dst)
                    t0 = time.perf_counter()
                    r = subprocess.run(cmd, shell=isinstance(cmd, str), env=env, capture_output=True)
                    dt = time.perf_counter() - t0
                    if r.returncode != 0 and not dst.exists():
                        st["error"] = f"exit {r.returncode}: {r.stderr.decode(errors='replace')[:200]}"
                        continue
                    res = dst.read_bytes()
                    if st["bytes"] is None:
                        st["bytes"] = len(res)
                        err = check(output_format(t), res, data)
                        st["verified"], st["error"] = err is None, err
                    if rnd >= a.warmup:
                        st["times"].append(dt)
            rel = str(f.relative_to(a.corpus))
            for t, st in acc.items():
                emit({"kind": "file", "file": rel, "raw": len(data), "method": t, "bytes": st["bytes"],
                      "verified": st["verified"], "error": st["error"], "total_s": st["times"],
                      "parse_s": [], "encode_s": [],
                      "median_total_s": statistics.median(st["times"]) if st["times"] else None,
                      "parsed_bytes": None})


if __name__ == "__main__":
    main()
