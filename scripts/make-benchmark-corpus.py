#!/usr/bin/env python3
"""Cut a staged scoring corpus out of a real-world source pool.

    scripts/fetch-corpus-sources.sh              once, ~800 MB into data/benchmark/sources/
    scripts/make-benchmark-corpus.py --stage 1   the public set
    scripts/make-benchmark-corpus.py --stage 2 --seed <secret>

Two stages, one manifest, 27 files and ~15.3 MB each. Twenty-six of the twenty-seven
are real data, sliced out of category pools built from what
`fetch-corpus-sources.sh` downloads: source in four languages, prose, non-Latin text,
logs, markup, tabular data, SQL, minified bundles, source maps, genomes, real
binaries, real images, real compressed archives, and real model checkpoints in five
dtypes across safetensors and GGUF. The one exception is `sparse.bin`, 40 KB of long
zero runs, because nothing natural exercises distance-1 matches at the 258 cap that
cleanly. It is 0.25% of the corpus and 0.00% of the headroom.

An earlier version generated most parts from seeded PRNGs, and was tuned hard: its
match distances were swept against Silesia and its weight compressibility calibrated
to within 0.2% of a real checkpoint on every dtype. It was still the wrong idea.
Synthetic data can only contain the structure someone thought to model, which is
exactly the structure a parser can be tuned against, and it flattered submissions --
its most redundant file had a gap of 0.655 against 0.686 for the most redundant real
one. The calibration did hold up, for what it is worth: real bf16 profiles at gap
0.984 and 79.8% zlib against the generator's 0.984 and 79.2%.

HOW THE TWO STAGES ARE KEPT APART

Each category pool is cut into POOL_BLOCK blocks and split by index parity: stage 1
gets the even blocks, stage 2 the odd ones. The halves are disjoint, so stage 2 is
real data that never appears in the public set, and they interleave through the same
files, so the two stages are the same problem statistically (see the README).

The pool is public by construction -- it is GitHub, Gutenberg and Hugging Face, and
the fetch script is in the open. What is hidden is which slice, in which order. That is
a quantitative defence, and a much better one than the synthetic corpus had: stage 0
of the gate caps a submission at 1 MB, against ~300 MB in stage 2's half of the pool,
so no table can cover it. It does not depend on anyone failing to find the data.

Determinism: each part draws from its own PRNG, seeded sha256(seed:partname), so
adding or reordering parts never perturbs another part's bytes. Given the same pool,
stage 1 rebuilds byte-identically. Pools are cached under sources/.pools/ -- delete
that directory, or pass --repool, after changing the manifest or the sources.
"""

import argparse
import hashlib
import json
import os
import pathlib
import random
import struct
import sys
import tarfile

REPO = pathlib.Path(__file__).resolve().parent.parent
BENCH = REPO / "data" / "benchmark"
SOURCES = BENCH / "sources"
SOURCES_TSV = REPO / "scripts" / "SOURCES.tsv"
SOURCES_DOC = REPO / "docs" / "CORPUS-SOURCES.md"

# Published on purpose: the public set has to be reproducible by anyone who wants to
# check that the committed bytes are what this script makes.
STAGE1_SEED = "conjectures-stage1-20260916"

# Block size for the stage-1/stage-2 parity split. Big enough that a block holds real
# structure, small enough that both halves interleave through every source file.
POOL_BLOCK = 131_072
# Chunk size the seed permutes within a stage's half when assembling a part.
SLICE_CHUNK = 65_536
# Skip pathological members when mining tarballs.
MAX_MEMBER = 8_000_000

# category -> what goes in its pool.
#   exts  suffixes to pull out of the downloaded tarballs
#   files exact filenames under sources/file/
#   dirs  whole directories under sources/
#   tars  the .tar.gz files themselves (already-compressed bytes)
CATEGORIES = {
    "c-source": {"exts": {".c", ".h"}},
    "rust-source": {"exts": {".rs", ".toml"}},
    "python-source": {"exts": {".py"}},
    "lean-source": {"exts": {".lean"}},
    "markdown": {"exts": {".md"}},
    "prose": {
        "files": [
            "gutenberg-war-and-peace",
            "gutenberg-moby-dick",
            "gutenberg-middlemarch",
            "gutenberg-quixote",
            "gutenberg-monte-cristo",
            "gutenberg-les-miserables",
            "gutenberg-anna-karenina",
            "gutenberg-bleak-house",
        ]
    },
    # Django/maven translation catalogues plus Chinese, Japanese and Russian novels:
    # 2- and 3-byte UTF-8 code units, which shift the literal distribution.
    "multibyte": {
        "exts": {".po"},
        "files": [
            "gutenberg-zh-dream",
            "gutenberg-zh-3kingdoms",
            "gutenberg-ja-kokoro",
            "gutenberg-ru-idiot",
        ],
    },
    "json": {
        "exts": {".json"},
        "files": ["npm-react.json", "npm-vue.json", "npm-express.json", "npm-webpack.json"],
    },
    "xml": {"exts": {".xml", ".svg"}, "files": ["arxiv-oai-cs.xml"]},
    "html": {"dirs": ["html"]},
    "csv": {
        "exts": {".csv"},
        "files": ["airports.csv", "runways.csv", "navaids.csv", "covid-timeseries.csv"],
    },
    "sql": {
        "exts": {".sql"},
        "files": [
            "chinook-postgres.sql",
            "chinook-sqlite.sql",
            "sakila-schema.sql",
            "sakila-data.sql",
            "northwind.sql",
        ],
    },
    "log": {"exts": {".log"}},
    "minified-js": {
        "exts": {".min.js"},
        "files": [
            "three.min.js",
            "lodash.min.js",
            "d3.min.js",
            "chart.min.js",
            "moment.min.js",
            "plotly.min.js",
            "echarts.min.js",
            "jquery.min.js",
            "katex.min.js",
        ],
    },
    # Source maps: JSON wrapping base64 VLQ. Dense 64-symbol alphabet, real.
    "sourcemap": {"exts": {".map"}},
    "genomic": {"files": ["ecoli-genome.fna", "yeast-genome.fna"]},
    # SQLite test databases and compiled gettext catalogues: real binary with real
    # internal structure, and unlike a local build artifact they are the same
    # everywhere, so the committed corpus does not depend on this machine.
    "binary": {"exts": {".db", ".mo"}},
    "image": {"exts": {".png", ".jpg", ".jpeg", ".gif"}},
    # Jars are zips, and the downloaded tarballs are gzip. Already-compressed bytes:
    # nothing left for a match finder to find.
    "compressed": {"exts": {".jar"}, "tars": True},
    # Machine code. Silesia carries `mozilla` for this and nothing here reached it;
    # WebAssembly is the modern form of the same thing and comes with a clean extension.
    "machine-code": {
        "exts": {".wasm"},
        "files": ["pyodide.asm.wasm", "resvg.wasm", "tiktoken.wasm", "sql.wasm"],
    },
    # Enormous in the real world -- CI, Kubernetes, Ansible -- and absent until now.
    # corpus-coverage.py rates it REDUNDANT (0.027 from source.py.txt: both are
    # indentation-structured text and they aggregate alike). Kept anyway, and kept
    # small: the metric's reference is Silesia, assembled in 2003, which cannot speak
    # to a format younger than it, and a benchmark aimed at real-world data should
    # carry the config language of modern infrastructure. See CORPUS-SOURCES.md.
    "yaml": {"exts": {".yml", ".yaml"}},
    # Real checkpoints, one category per dtype, each the first 16 MB of a real file.
    # Mantissa bytes are noise under a handful of exponent bytes, so matches are short,
    # strided and very near -- and the two GGUF quantizations bring block layouts
    # (Q8_0's 34-byte blocks, Q4_K's 256-element superblocks with 6-bit scales) that no
    # generator here was ever going to reproduce faithfully.
    "weights-f32": {"files": ["weights-f32.safetensors"]},
    "weights-f16": {"files": ["weights-f16.safetensors"]},
    "weights-bf16": {"files": ["weights-bf16.safetensors"]},
    "weights-q8": {"files": ["weights-q8_0.gguf"], "gguf_tensors_only": True},
    "weights-q4k": {"files": ["weights-q4_k_m.gguf"], "gguf_tensors_only": True},
}

# name, format label, byte cap, category ("synthetic-sparse" is the only generated one)
#
# Caps are set by discrimination per unit of parse time, measured with
# scripts/pareto-bench's corpus-profile, not by taste. `gap` there is optimal-parse
# bytes over greedy-parse bytes -- the entire quantity this competition scores -- and
# the headroom a file offers is greedy minus optimal. Real logs and SQL dumps turn out
# to be so redundant that `optimal` costs 38x and 41x the incumbent's time on them for
# little headroom, while prose, markdown and C source buy more at 3-5x. Weighting
# toward the cheap discriminators took the pooled speed ratio from 7.6x to 5.8x against
# the harness's 8.0x floor -- a parser that is better but slower needs room to land --
# and raised total headroom 16% at the same time.
PARTS = [
    # Most parts are concatenations of many real files, so they take the repository's
    # existing `<what>.<ext>.txt` / `.bin` convention -- `catalog.xml.txt` is XML, but it
    # is not one XML document. The weight files and `server.log`, `genome.fasta` are
    # valid as they stand.
    ("source.c.txt", "c-source", 1_400_000, "c-source"),
    ("source.rs.txt", "rust-source", 700_000, "rust-source"),
    ("source.py.txt", "python-source", 600_000, "python-source"),
    ("lean.txt", "lean-source", 1_000_000, "lean-source"),
    ("docs.md.txt", "markdown", 800_000, "markdown"),
    ("prose.txt", "prose", 1_500_000, "prose"),
    ("multibyte.txt", "utf8-multibyte", 1_100_000, "multibyte"),
    ("records.json.txt", "json", 400_000, "json"),
    ("catalog.xml.txt", "xml", 500_000, "xml"),
    ("page.html.txt", "html", 600_000, "html"),
    ("metrics.csv.txt", "csv", 1_300_000, "csv"),
    ("dump.sql.txt", "sql", 150_000, "sql"),
    ("server.log", "log", 300_000, "log"),
    ("bundle.min.js.txt", "minified-js", 1_000_000, "minified-js"),
    ("sourcemap.map.txt", "sourcemap", 350_000, "sourcemap"),
    ("genome.fasta", "genomic", 900_000, "genomic"),
    ("binary.db.bin", "binary", 500_000, "binary"),
    ("images.bin", "image-bundle", 250_000, "image"),
    ("compressed.bin", "compressed", 300_000, "compressed"),
    ("machine-code.bin", "machine-code", 500_000, "machine-code"),
    ("config.yaml.txt", "yaml", 400_000, "yaml"),
    # Five real dtypes. Only bf16 moves under a better parse (gap 0.984); f32 and f16
    # are near flat and the two quantizations are dead flat at 1.000 -- quantized
    # weights are genuinely incompressible. They are sized accordingly: present because
    # weights are real input a DEFLATE encoder meets and a parser must not choke or
    # crawl on them, not because they can rank anyone.
    ("weights-f32.bin", "weights-f32", 350_000, "weights-f32"),
    ("weights-f16.bin", "weights-f16", 250_000, "weights-f16"),
    ("weights-bf16.bin", "weights-bf16", 450_000, "weights-bf16"),
    # Only one quantization: Q8_0 and Q4_K_M profile 0.002 apart in
    # scripts/corpus-coverage.py's feature space -- different schemes, same behaviour
    # to a match finder, so the second is budget spent twice. The pool still carries
    # Q4_K_M if that ever stops being true.
    ("weights-q8.bin", "weights-int8", 250_000, "weights-q8"),
    ("sparse.bin", "sparse", 40_000, "synthetic-sparse"),
    # Below the 32 KB window: a regime every other file is far above.
    ("tiny-config.json.txt", "tiny-json", 12_000, "json"),
    ("tiny-app.log", "tiny-log", 28_000, "log"),
]


def part_rng(seed, name):
    """One independent PRNG per part, so parts never perturb each other."""
    h = hashlib.sha256(f"{seed}:{name}".encode()).digest()
    return random.Random(int.from_bytes(h[:16], "big"))


# --- pools ------------------------------------------------------------------

# GGUF value-type -> fixed width, for the types that are not strings or arrays.
_GGUF_W = {0: 1, 1: 1, 2: 2, 3: 2, 4: 4, 5: 4, 6: 4, 7: 1, 10: 8, 11: 8, 12: 8}


def gguf_tensor_data(raw):
    """A GGUF's tensor data, past the metadata and the tensor table.

    Two quantizations of the same model share their metadata byte for byte -- for
    SmolLM2 that is 1.8 MB of tokenizer vocabulary, 11% of the 16 MB head fetched.
    Pooling it made weights-q8 and weights-q4k profile identically (gap 1.00011 vs
    1.00002, zlib 94.77% vs 94.78%), which wastes the budget of carrying both: the
    whole reason for two is that Q8_0's flat 34-byte blocks and Q4_K_M's 256-element
    superblocks are different layouts. Skipping the metadata leaves each part
    measuring its own. Anything unparseable falls through to the whole file, which
    only means the vocabulary stays in.
    """
    try:
        if raw[:4] != b"GGUF":
            return raw
        ntensor, nkv = struct.unpack("<QQ", raw[8:24])
        o, align = 24, 32

        def rstr(o):
            n = struct.unpack("<Q", raw[o : o + 8])[0]
            return raw[o + 8 : o + 8 + n], o + 8 + n

        def rval(o, t):
            if t == 8:
                return rstr(o)[1]
            if t == 9:  # array: element type, count
                et = struct.unpack("<I", raw[o : o + 4])[0]
                n = struct.unpack("<Q", raw[o + 4 : o + 12])[0]
                o += 12
                for _ in range(n):
                    o = rval(o, et)
                return o
            return o + _GGUF_W[t]

        for _ in range(nkv):
            k, o = rstr(o)
            t = struct.unpack("<I", raw[o : o + 4])[0]
            o += 4
            if k == b"general.alignment":
                align = struct.unpack("<I", raw[o : o + 4])[0]
            o = rval(o, t)
        for _ in range(ntensor):
            o = rstr(o)[1]
            nd = struct.unpack("<I", raw[o : o + 4])[0]
            o += 4 + 8 * nd + 12  # dims, then ggml type + offset
        start = o + (-o % align)
        return raw[start:] if 0 < start < len(raw) else raw
    except (struct.error, IndexError, KeyError):
        return raw


def _suffix(name):
    n = name.lower()
    return ".min.js" if n.endswith(".min.js") else pathlib.PurePath(n).suffix


def build_pools(repool=False):
    """One pass over the downloaded sources, routing every file to its category.

    Cached, because mining fifteen gzipped tarballs takes far longer than everything
    else here put together and the result never changes until the sources do.
    """
    cache = SOURCES / ".pools"
    names = list(CATEGORIES)
    contrib_path = cache / "contrib.json"
    if (
        not repool
        and cache.is_dir()
        and contrib_path.exists()
        and all((cache / f"{c}.bin").exists() for c in names)
    ):
        return {c: (cache / f"{c}.bin").read_bytes() for c in names}

    if not SOURCES.is_dir():
        sys.exit(f"no source pool at {SOURCES} -- run scripts/fetch-corpus-sources.sh first.")

    pools = {c: bytearray() for c in names}
    # Which download fed which category, in bytes -- the raw material for
    # CORPUS-SOURCES.md, recorded here because this is the only pass that knows.
    contrib = {c: {} for c in names}
    ext_to_cat = {}
    for cat, spec in CATEGORIES.items():
        for e in spec.get("exts", ()):
            ext_to_cat.setdefault(e, cat)

    tars = sorted((SOURCES / "tar").glob("*.tar.gz"))
    print(f"building pools from {len(tars)} archives (cached afterwards) ...")
    for t in tars:
        try:
            with tarfile.open(t, "r:gz") as tf:
                for m in tf:
                    if not m.isfile() or not (0 < m.size <= MAX_MEMBER):
                        continue
                    cat = ext_to_cat.get(_suffix(m.name))
                    if cat is None:
                        continue
                    f = tf.extractfile(m)
                    if f is not None:
                        b = f.read()
                        pools[cat] += b
                        contrib[cat][t.name[:-7]] = contrib[cat].get(t.name[:-7], 0) + len(b)
        except (tarfile.TarError, OSError) as e:
            print(f"  skipping {t.name}: {e}")
        for cat, spec in CATEGORIES.items():
            if spec.get("tars"):
                b = t.read_bytes()
                pools[cat] += b
                contrib[cat][t.name[:-7]] = contrib[cat].get(t.name[:-7], 0) + len(b)

    for cat, spec in CATEGORIES.items():
        for fn in spec.get("files", ()):
            p = SOURCES / "file" / fn
            if p.exists():
                b = p.read_bytes()
                if spec.get("gguf_tensors_only"):
                    b = gguf_tensor_data(b)
                pools[cat] += b
                contrib[cat][fn] = contrib[cat].get(fn, 0) + len(b)
        for d in spec.get("dirs", ()):
            for p in sorted((SOURCES / d).glob("*")):
                if p.is_file():
                    b = p.read_bytes()
                    pools[cat] += b
                    contrib[cat][d] = contrib[cat].get(d, 0) + len(b)

    cache.mkdir(parents=True, exist_ok=True)
    for c, b in pools.items():
        (cache / f"{c}.bin").write_bytes(bytes(b))
    contrib_path.write_text(json.dumps(contrib, indent=1, sort_keys=True))
    return {c: bytes(b) for c, b in pools.items()}


def stage_half(pool, stage):
    """The half of a pool this stage may draw from. Disjoint by block index parity."""
    blocks = [pool[i : i + POOL_BLOCK] for i in range(0, len(pool), POOL_BLOCK)]
    return b"".join(blocks[(stage - 1) % 2 :: 2])


def slice_part(rng, half, cap):
    """cap bytes out of this stage's half, in a seed-chosen chunk order."""
    if not half:
        return b""
    chunks = [half[i : i + SLICE_CHUNK] for i in range(0, len(half), SLICE_CHUNK)]
    rng.shuffle(chunks)
    return b"".join(chunks)[:cap]


def build_sparse(rng, cap):
    """The only fully synthetic part. Long zero runs: distance-1 matches capped at 258,
    back to back. Real files are sparse in ways that are never this clean, and the
    degenerate end of the range is worth one 80 KB file."""
    out = bytearray()
    while len(out) < cap:
        out += b"\0" * rng.randrange(64, 3000)
        for _ in range(rng.randrange(1, 6)):
            out += struct.pack(
                "<IIf", rng.randrange(1 << 28), rng.randrange(1 << 20), rng.gauss(0, 1)
            )
    return bytes(out[:cap])


# --- driver -----------------------------------------------------------------


def resolve_seed(args):
    if args.stage == 1:
        return args.seed or STAGE1_SEED
    seed = args.seed or os.environ.get("BENCHMARK_STAGE2_SEED")
    if not seed:
        sys.exit(
            "stage 2 has no default seed -- that is the point. Pass --seed <secret>, or\n"
            "set BENCHMARK_STAGE2_SEED in .env (gitignored). Anyone holding it can\n"
            "rebuild the held-out corpus byte for byte."
        )
    if seed == STAGE1_SEED:
        sys.exit("stage 2 was given stage 1's published seed; it would be the same corpus.")
    return seed


def update_formats(out):
    """Filename -> format label for the analysis tools, written as a *sibling* of the
    corpus directory (corpus-stageN.formats.json next to corpus-stageN/) rather than
    a member of it -- so nothing that iterates the corpus directory (the real scoring
    engine included) ever finds it. Labels only, never content -- stage 2's copy is
    safe to commit while its bytes stay held out. Stage 1 and stage 2 get
    byte-identical copies: they share one manifest. Copy it into each dataset repo's
    own root as plain `formats.json`, alongside its `SOURCES.md`, same convention."""
    doc = {
        "_comment": (
            "Maps filename -> a human-chosen format label, so benchmark analysis "
            "can group and normalize by file format instead of pooling raw bytes. "
            'A file missing here gets "unknown" at collection time.'
        ),
        **{name: fmt for name, fmt, _c, _s in PARTS},
    }
    sidecar = out.with_name(f"{out.name}.formats.json")
    sidecar.write_text(json.dumps(doc, indent=4) + "\n")


# category -> (data-type family, what it is as a kind of data). Drives the taxonomy
# table in CORPUS-SOURCES.md.
TYPE_NOTES = {
    "c-source": ("source code", "C and headers: heavy #include and boilerplate repetition"),
    "rust-source": ("source code", "Rust and TOML"),
    "python-source": ("source code", "Python: indentation-structured, high identifier reuse"),
    "lean-source": ("source code", "Lean 4 proofs: unusually long repeated term structure"),
    "markdown": ("prose / markup", "documentation prose with code fences"),
    "prose": ("natural language", "English literary prose, the classic text regime"),
    "multibyte": (
        "natural language",
        "Chinese, Japanese, Russian and gettext catalogues: 2- and 3-byte UTF-8",
    ),
    "json": ("structured text", "JSON: repeated keys, deep nesting"),
    "xml": ("structured text", "XML and SVG: tag repetition at long distance"),
    "html": ("structured text", "rendered HTML: markup plus inline CSS and JS"),
    "csv": ("tabular", "CSV: columnar, low-cardinality categoricals, fixed strides"),
    "sql": ("structured text", "SQL dumps: an identical INSERT prefix, a varying tail"),
    "log": ("machine-generated text", "near-duplicate lines at long distance"),
    "yaml": ("configuration", "YAML: CI, Kubernetes and Ansible"),
    "minified-js": (
        "dense text",
        "minified bundles: one- and two-character identifiers, few newlines",
    ),
    "sourcemap": (
        "encoded text",
        "source maps: base64 VLQ inside JSON, a dense 64-symbol alphabet",
    ),
    "genomic": ("scientific", "FASTA: a 4-symbol alphabet with real repeat structure"),
    "binary": ("binary records", "SQLite databases and compiled gettext catalogues"),
    "machine-code": ("machine code", "WebAssembly: real compiled binaries"),
    "image": ("compressed media", "PNG and JPEG: already-compressed pixel data"),
    "compressed": ("compressed archive", "jars and gzip tarballs: nothing left to find"),
    "weights-f32": ("model weights", "float32 tensors from a trained sentence encoder"),
    "weights-f16": ("model weights", "float16 tensors"),
    "weights-bf16": ("model weights", "bfloat16 tensors, the common LLM training dtype"),
    "weights-q8": ("model weights", "GGUF Q8_0: 32-weight blocks, 34 bytes each"),
    "weights-q4k": ("model weights", "GGUF Q4_K_M: 256-element superblocks with 6-bit scales"),
    "synthetic-sparse": ("degenerate", "long zero runs: distance-1 matches pinned at the 258 cap"),
}

# Popular data types this corpus does NOT contain, and why. Kept honest on purpose:
# the first group is deliberate, the second is a real gap someone may want to close.
NOT_COVERED = [
    (
        "Office documents (.docx/.xlsx/.pptx)",
        "measured, rejected",
        "A .docx is a zip of XML. Built as a candidate and profiled 0.035 from `images.bin` "
        "-- a near-duplicate. Different format, same behaviour.",
    ),
    (
        "GGUF Q4_K_M weights",
        "measured, rejected",
        "Profiled 0.002 from `weights-q8.bin`. Still in the source pool if that changes.",
    ),
    (
        "Base64 text (PEM, data URIs)",
        "covered by proxy",
        "`sourcemap.map.txt` is base64 VLQ: the same dense 64-symbol alphabet.",
    ),
    (
        "NDJSON / JSON Lines",
        "covered by proxy",
        "Between `records.json.txt` and `server.log`, both regimes are present.",
    ),
    (
        "ELF / PE executables",
        "covered by proxy",
        "`machine-code.bin` is WebAssembly, the same compiled-code regime with a cleaner "
        "extension to mine. Native ELF would be a closer match to Silesia's `mozilla`.",
    ),
    ("PDF", "GAP", "Mixed text with embedded compressed streams; nothing here is quite that mix."),
    (
        "Columnar analytics (Parquet, ORC, Arrow, Avro)",
        "GAP",
        "Dictionary and RLE encoding under a block compressor. Common in data engineering.",
    ),
    (
        "Audio and video (WAV, MP3, MP4)",
        "GAP",
        "Uncompressed PCM is very compressible and unlike anything here; MP3/MP4 would land "
        "near `compressed.bin`.",
    ),
    (
        "Uncompressed raster (BMP, TIFF, PPM, DICOM)",
        "GAP",
        "Silesia's `x-ray` and `mr` are this regime and sit at 0.130 and 0.119 -- the two "
        "loosest reaches after `osdb`.",
    ),
    (
        "Binary serialization (protobuf, MessagePack, CBOR)",
        "GAP",
        "Varint-dense records; no natural source in the current pool.",
    ),
    ("Email / MIME archives (mbox)", "GAP", "Extremely repetitive headers around base64 bodies."),
    ("Fonts (TTF/OTF/WOFF)", "GAP", "Present in the pool but too small to carry a part."),
    (
        "Database page dumps",
        "GAP",
        "Silesia's `osdb` is the worst-reached reference file at 0.161. `binary.db.bin` is "
        "SQLite and behaves differently.",
    ),
]


COVERAGE_NOTE = [
    "`scripts/corpus-coverage.py` measures coverage over parse *behaviour*, not over",
    "format names -- an LZ77 parser does not see formats, and two extensions can be",
    "one behaviour. Each file becomes a point in six axes taken from its profile (gap,",
    "literal fraction, mean match length, near and far distance share, and the",
    "fraction of matches pinned at the 258-byte cap). It reports two things:",
    "",
    "- **reach** -- for each file in an external reference corpus, the distance to the",
    "  nearest benchmark file. This is the number that can fail, because the reference",
    "  is not ours. Silesia is the reference: it is what modern compressors report",
    "  against.",
    "- **spacing** -- for each benchmark file, the distance to its nearest neighbour",
    "  *inside* the benchmark. Small means two parts measure the same thing, and one of",
    "  them is budget spent twice.",
    "",
    "Neither is a percentage, deliberately. A denominator over all the data that exists",
    "would be invented; a worst-case distance, named with the file that produced it, is",
    "not.",
    "",
    "```bash",
    "just corpus-download        # Silesia, the reference",
    "just corpus-coverage",
    "```",
    "",
    "It has already changed this manifest three times. A `.docx` part was built,",
    "measured at 0.035 from `images.bin`, and dropped -- a zip of XML behaves like any",
    "other compressed container. `weights-q4k.bin` and `weights-q8.bin` profiled 0.002",
    "apart, two real quantization schemes and one behaviour, so only Q8_0 is carried.",
    "And WebAssembly was added because Silesia's `mozilla` had nothing within 0.125 of",
    "it; that is now 0.066.",
    "",
    "### Where it is overruled",
    "",
    "Two places, both deliberate.",
    "",
    "`config.yaml.txt` is rated **redundant**, 0.027 from `source.py.txt` -- both are",
    "indentation-structured text and they aggregate alike. It is carried anyway,",
    "because the metric can only measure against the reference it is given and Silesia",
    "was assembled in 2003, so it has nothing to say about a format younger than it.",
    "Prevalence is a coverage criterion too, and YAML is the config language of modern",
    "infrastructure. It is kept small for the same reason.",
    "",
    "The text files cluster: `source.c.txt`, `source.py.txt`, `lean.txt`,",
    "`docs.md.txt`, `multibyte.txt` and `config.yaml.txt` all sit within 0.04 of one",
    "another. That is accepted rather than fixed. Text is the bulk of what a DEFLATE",
    "encoder actually compresses, and drawing it from six unrelated projects guards",
    "against tuning to one codebase's idiom even where the aggregate statistics",
    "coincide -- spacing measures whether two files look alike in six numbers, not",
    "whether they contain the same words.",
]


def write_sources_doc():
    """Render CORPUS-SOURCES.md: every download, its licence, and what it feeds.

    Generated rather than hand-kept, from three things that already exist -- the
    licence table fetch-corpus-sources.sh writes, the category map above, and the
    byte contributions recorded while pooling -- so it cannot drift from what was
    actually downloaded and actually used.
    """
    if not SOURCES_TSV.exists():
        return False
    rows = [
        dict(zip(("kind", "name", "license", "url"), ln.rstrip("\n").split("\t")))
        for ln in SOURCES_TSV.read_text().splitlines()[1:]
        if ln.strip()
    ]
    by_name = {r["name"]: r for r in rows}
    contrib_path = SOURCES / ".pools" / "contrib.json"
    contrib = json.loads(contrib_path.read_text()) if contrib_path.exists() else {}

    # The pool records the `html` directory under its directory name; the licence
    # table records the pages that fill it under one entry.
    DIR_ALIAS = {"html": "wikipedia-articles"}

    def base_licence(r):
        """Group the summary by licence, not by which model a checkpoint came from.

        Only the `range` rows name a model in parentheses; "arXiv metadata (CC0)" and
        "curl (MIT-like)" mean something and are left alone.
        """
        return r["license"].split(" (", 1)[0].strip() if r["kind"] == "range" else r["license"]

    def display(name, r):
        """Model checkpoints read better by model than by the filename they land in."""
        if r and r["kind"] == "range" and "(" in r["license"]:
            return r["license"].split("(", 1)[1].rstrip(")").split(",")[0].strip()
        return name

    wiki = next((n for n in by_name if n.startswith("wikipedia-articles")), None)
    DIR_ALIAS["html"] = wiki or "wikipedia-articles"

    def link(name):
        key = DIR_ALIAS.get(name, name)
        r = by_name.get(key)
        return f"[{display(key, r)}]({r['url']})" if r else name

    out = [
        "# Corpus sources",
        "",
        "Everything `data/benchmark/corpus-stage1/` and `corpus-stage2/` are cut from.",
        "",
        "**Generated by `scripts/make-benchmark-corpus.py`** from `scripts/SOURCES.tsv`,",
        "the category map in that same script, and the byte counts recorded while the",
        "pools are built -- so it reflects what was actually downloaded and actually",
        "used, not what someone remembered to write down. Re-run",
        "`.venv/bin/python scripts/make-benchmark-corpus.py --stage 1 --repool` to refresh it.",
        "",
        "Nobody redistributes the pool itself: `data/benchmark/sources/` is gitignored",
        "and each machine fetches its own",
        "with `scripts/fetch-corpus-sources.sh`. What is published",
        "is `corpus-stage1/`, in its own repository, and it contains slices of the",
        "material below -- all of it permissively licensed or public domain. Attribution",
        "is the table at the end. This is preliminary work: a record of what each project",
        "states, not a vetted legal review.",
        "",
        "The corpus is published as bytes rather than rebuilt from this list because 38 of",
        "the 73 sources are floating URLs -- branch heads, live Wikipedia, current npm",
        "metadata, daily CSVs, an arXiv query that answers differently each call -- so a",
        "fresh pool is not the pool stage 1 was cut from. `just corpus-verify` reports",
        "exactly that when it happens.",
        "",
    ]

    out += [
        "## What each corpus file is cut from",
        "",
        "| corpus file | bytes | drawn from |",
        "|---|---:|---|",
    ]
    for fname, _fmt, cap, cat in PARTS:
        if cat == "synthetic-sparse":
            src = "*generated* — long zero runs, the one part with no natural source"
        else:
            c = sorted(contrib.get(cat, {}).items(), key=lambda kv: -kv[1])
            shown = ", ".join(link(n) for n, _b in c[:6])
            if len(c) > 6:
                shown += f", +{len(c) - 6} more"
            src = shown or f"*(category `{cat}`)*"
        out.append(f"| `{fname}` | {cap:,} | {src} |")

    out += [
        "",
        "## Data types covered",
        "",
        "Grouped by what the data *is*.",
        "",
        "| family | corpus file | what it is |",
        "|---|---|---|",
    ]
    fam_order, seen = [], set()
    for _f, _fm, _c, cat in PARTS:
        fam = TYPE_NOTES.get(cat, ("other", ""))[0]
        if fam not in seen:
            seen.add(fam)
            fam_order.append(fam)
    for fam in fam_order:
        for fname, _fm, _c, cat in PARTS:
            note = TYPE_NOTES.get(cat)
            if note and note[0] == fam:
                out.append(f"| {fam} | `{fname}` | {note[1]} |")

    out += [
        "",
        "## What is not here",
        "",
        "A coverage claim is only worth as much as its list of holes.",
        "`covered by proxy` means something else already exercises the same parse",
        "behaviour; `measured, rejected` means it was built as a candidate and the",
        "numbers said no; `GAP` means genuinely missing.",
        "",
        "| data type | status | note |",
        "|---|---|---|",
    ]
    for name, status, why in NOT_COVERED:
        out.append(f"| {name} | {status} | {why} |")
    out += ["", "### How that list was decided", ""] + COVERAGE_NOTE

    out += [
        "",
        "## Every download",
        "",
        f"{len(rows)} sources. `kind` is how the builder treats it: `tar` is unpacked and",
        "mined by file extension, `file` is used whole, `gz` is gunzipped, `range` is the",
        "first 16 MB of a much larger file (the model checkpoints), `html` is a set of",
        "fetched pages.",
        "",
        "| source | kind | licence |",
        "|---|---|---|",
    ]
    for r in sorted(rows, key=lambda r: (r["kind"], r["name"])):
        out.append(f"| [{r['name']}]({r['url']}) | {r['kind']} | {r['license']} |")

    counts = {}
    for r in rows:
        k = base_licence(r)
        counts[k] = counts.get(k, 0) + 1
    out += ["", "## Licences at a glance", "", "| licence | sources |", "|---|---:|"]
    for k, v in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])):
        out.append(f"| {k} | {v} |")
    out.append("")
    SOURCES_DOC.write_text("\n".join(out))
    return True


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--stage", type=int, choices=(1, 2), required=True)
    ap.add_argument("--seed", help="stage 1 defaults to the published seed; stage 2 has none")
    ap.add_argument("--out", help="default data/benchmark/corpus-stage<N>")
    ap.add_argument("--repool", action="store_true", help="rebuild the cached category pools")
    ap.add_argument("--force", action="store_true", help="overwrite a non-empty output directory")
    args = ap.parse_args()

    seed = resolve_seed(args)
    out = pathlib.Path(args.out) if args.out else BENCH / f"corpus-stage{args.stage}"
    if out.exists() and any(out.iterdir()) and not args.force:
        sys.exit(f"{out} is not empty; pass --force to replace it.")

    pools = build_pools(args.repool)
    halves = {c: stage_half(p, args.stage) for c, p in pools.items()}

    out.mkdir(parents=True, exist_ok=True)
    for old in out.iterdir():
        if old.is_file():
            old.unlink()

    print(f"\nstage {args.stage} -> {out}")
    print(
        f"seed        {'(published) ' if args.stage == 1 else '(held) '}"
        f"{hashlib.sha256(seed.encode()).hexdigest()[:16]}"
    )
    print(
        f"pool        {SOURCES}  "
        f"({sum(len(p) for p in pools.values()) / 1e6:.0f} MB, "
        f"{'even' if args.stage == 1 else 'odd'} blocks)\n"
    )
    print(f"{'file':<26} {'format':<16} {'bytes':>9} {'fill':>6} {'pool MB':>8}  sha256")

    total, thin, tight = 0, [], []
    for fname, fmt, cap, cat in PARTS:
        rng = part_rng(seed, fname)
        if cat == "synthetic-sparse":
            data, pool_mb = build_sparse(rng, cap), 0.0
        else:
            data = slice_part(rng, halves[cat], cap)
            pool_mb = len(halves[cat]) / 1e6
            if len(halves[cat]) < 3 * cap:
                tight.append(
                    f"{fname}: half is {pool_mb:.1f} MB for a "
                    f"{cap / 1e6:.1f} MB part ({len(halves[cat]) / cap:.1f}x)"
                )
        (out / fname).write_bytes(data)
        total += len(data)
        pct = 100.0 * len(data) / cap
        if pct < 99 and not cat.startswith("synthetic-"):
            thin.append(
                f"{fname}: {pct:.0f}% of its {cap:,} byte budget "
                f"(category '{cat}' half is only {pool_mb:.1f} MB)"
            )
        print(
            f"{fname:<26} {fmt:<16} {len(data):>9} {pct:>5.0f}% {pool_mb:>8.1f}  "
            f"{hashlib.sha256(data).hexdigest()[:16]}"
        )

    print(f"{'TOTAL':<26} {len(PARTS):<16} {total:>9}")

    # Only a build of a real stage touches tracked files. A build to a scratch
    # directory -- what verify-corpus.py does, and any --out elsewhere -- must not,
    # or every throwaway run leaves a stale formats.json/CORPUS-SOURCES.md behind.
    canonical = out.resolve().parent == BENCH.resolve()
    if canonical:
        update_formats(out)
        print(
            f"format labels        -> {out.with_name(f'{out.name}.formats.json').relative_to(REPO)}"
        )
        if write_sources_doc():
            print(f"source attribution   -> {SOURCES_DOC.relative_to(REPO)}")
    else:
        print(f"\n{out} is outside {BENCH.name}/: leaving formats.json and CORPUS-SOURCES.md alone")
    if thin:
        print("\nWARNING: parts that came up short -- their category pool is too small:")
        for t in thin:
            print(f"  {t}")
        print("  add sources to scripts/fetch-corpus-sources.sh, then --repool.")
    if tight:
        print("\nNOTE: categories with little slack -- the seed has few distinct slices")
        print("to choose from, so stage 2 overlaps stage 1 more in kind than elsewhere:")
        for t in tight:
            print(f"  {t}")
    print(f"\n  VERIFY_CORPUS={out.name} just check miner/template")


if __name__ == "__main__":
    main()
