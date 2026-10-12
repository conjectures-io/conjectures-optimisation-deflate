#!/usr/bin/env python3
"""Robustness set A (PLAN.md §3.3): inputs that break parsers tuned to one corpus.

Deterministic: the same bytes on every run, so results compare across hosts.

    gen-setA.py OUT_DIR [--scale-source FILE]

`--scale-source` (e.g. enwik8) gives the 1-64 MiB scaling series; without it the
series is built from generated text.
"""

from __future__ import annotations

import argparse
import random
import struct
from pathlib import Path

MiB = 1024 * 1024


def de_bruijn(k: int, n: int) -> bytes:
    """Every n-gram over k symbols exactly once (cyclic)."""
    a = [0] * k * n
    seq: list[int] = []

    def db(t: int, p: int) -> None:
        if t > n:
            if n % p == 0:
                seq.extend(a[1 : p + 1])
        else:
            a[t] = a[t - p]
            db(t + 1, p)
            for j in range(a[t - p] + 1, k):
                a[t] = j
                db(t + 1, t)

    db(1, 1)
    return bytes(seq)


def fibonacci_word(size: int) -> bytes:
    a, b = b"a", b"ab"
    while len(b) < size:
        a, b = b, b + a
    return b[:size]


def thue_morse(size: int) -> bytes:
    return bytes(ord("a") + bin(i).count("1") % 2 for i in range(size))


def text(rng: random.Random, size: int) -> bytes:
    words = (
        "the of and to in is was for on that with as by at from his her an were which this be "
        "parser window match literal distance length block huffman stream token decode encode "
        "compress zlib deflate gzip lean proof verify submission corpus benchmark frontier"
    ).split()
    out = bytearray()
    while len(out) < size:
        line = " ".join(rng.choice(words) for _ in range(rng.randint(4, 14)))
        out += line.capitalize().encode() + b".\n"
    return bytes(out[:size])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("out", type=Path)
    ap.add_argument("--scale-source", type=Path)
    a = ap.parse_args()
    out = a.out
    out.mkdir(parents=True, exist_ok=True)
    rng = random.Random(20261012)
    files: dict[str, bytes] = {}

    sample = text(rng, 64 * 1024)
    json_like = b'{"id":12345,"name":"example","tags":["a","b"],"ok":true,"score":0.75}\n' * 64
    for n in (1, 10, 100, 1024, 4096):
        files[f"tiny-text-{n}"] = sample[:n]
        files[f"tiny-json-{n}"] = json_like[:n]
        files[f"tiny-random-{n}"] = rng.randbytes(n)

    files["zeros-1m"] = bytes(MiB)
    files["random-1m"] = rng.randbytes(MiB)
    for p in (1, 2, 3, 4, 7):
        files[f"period-{p}-1m"] = (bytes(range(97, 97 + p)) * (MiB // p + 1))[:MiB]
    for p in (32_769, 65_536, 100_000):
        block = rng.randbytes(p)
        files[f"window-trap-{p}"] = (block * (MiB // p + 2))[:MiB]
    near = bytearray(text(rng, 40_000))
    trap = bytearray(near)
    for _ in range(25):
        i = rng.randrange(len(trap))
        trap[i] ^= 0x20
    files["window-trap-text-40k"] = bytes(near + trap)

    # Every 3-gram many times, every 4-gram once: long hash chains, nothing to gain.
    files["debruijn-k32-n4"] = de_bruijn(32, 4)
    db16 = de_bruijn(16, 4)
    files["debruijn-k16-n4-x16"] = db16 * 16  # repeats only at 64 KiB: beyond the window
    files["fibonacci-1m"] = fibonacci_word(MiB)
    files["thue-morse-1m"] = thue_morse(MiB)

    # Integer tables: what app.dex's ID sections look like.
    ids = bytearray()
    v = 1000
    for _ in range(MiB // 8):
        v += rng.choice((1, 1, 1, 2, 3, 8))
        ids += struct.pack("<II", v, rng.randrange(1 << 16))
    files["int-table-1m"] = bytes(ids)
    floats = b"".join(struct.pack("<f", rng.gauss(0.0, 1.0)) for _ in range(MiB // 4))
    files["float32-noise-1m"] = floats
    files["utf16le-text-1m"] = text(rng, MiB // 2).decode().encode("utf-16-le")
    # Long runs with rare mutations: maximal match lengths, distance 1 and 2.
    runs = bytearray()
    while len(runs) < MiB:
        runs += bytes([rng.randrange(256)]) * rng.randint(200, 5000)
        runs += rng.randbytes(rng.randint(1, 3))
    files["runs-1m"] = bytes(runs[:MiB])

    src = a.scale_source.read_bytes()[: 64 * MiB] if a.scale_source else None
    if src is None or len(src) < 64 * MiB:
        base = text(rng, 4 * MiB)
        src = (base * 16)[: 64 * MiB] if src is None else (src * (64 * MiB // len(src) + 1))[: 64 * MiB]
    for n in (1, 4, 16, 64):
        files[f"scale-{n:02d}m"] = src[: n * MiB]

    for name, data in files.items():
        (out / name).write_bytes(data)
    print(f"{len(files)} files, {sum(map(len, files.values())) / MiB:.1f} MiB in {out}")


if __name__ == "__main__":
    main()
