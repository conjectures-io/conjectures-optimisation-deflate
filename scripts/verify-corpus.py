#!/usr/bin/env python3
"""Check a downloaded source pool: everything present, and still cuts the same corpus.

    scripts/verify-corpus.py            check the pool
    scripts/verify-corpus.py --quick    presence only, skip the rebuild

WHY THE CORPUS IS DISTRIBUTED AS BYTES AND THIS ONLY CHECKS THE POOL

The obvious alternative to publishing ~16 MB of corpus is to publish the fetch script
and verify the download instead. It does not work here, and this script is partly how
you can see that: 38 of the 73 sources are floating URLs. Eighteen are GitHub branch
heads -- sqlite, curl, mathlib4, django and TypeScript all take commits most days --
and the rest are live Wikipedia articles, current npm metadata, CSVs regenerated
daily, and an arXiv OAI query that returns different records every call.

So a fresh pool is not the pool stage 1 was cut from, and two people fetching a week
apart do not get the same corpus. For a competition where submissions are ranked on
compressed bytes, that is fatal: a miner has to be able to score against exactly what
the validator scores against. The published bytes ARE the specification -- they live in
conjectures-compression-corpus-1, and `just corpus-pull` puts them in place. The pool
is only needed to cut a new stage, and to run the reproduction check below.

WHAT IT CHECKS

  presence      every source in SOURCES.tsv is on disk and non-empty
  reproduction  the pool, as it stands, still cuts byte-identical stage 1 -- so the
                pool in front of you is the pool the published corpus came from.
                When it fails, the published bytes are still right and the pool has
                moved under you. Needs `just corpus-pull` to have run.

There was a per-source checksum manifest here too. It was dropped: it recorded one
machine's snapshot, so 38 of 73 entries would report drift for anyone else the day
they fetched, and the rebuild answers the same question properly -- if any source
moved in a way that matters, stage 1 stops reproducing. A checksum nobody can act on
is noise.

Exit codes distinguish the two kinds of problem, because they need different
responses: 0 all good, 1 the pool is incomplete (re-fetch), 2 there is no pool at
all, 3 the pool is complete but has drifted from what stage 1 was cut from -- which
is expected eventually and breaks nothing, since the published bytes are the
reference.
"""

import argparse
import csv
import hashlib
import pathlib
import shutil
import subprocess
import sys
import tempfile

REPO = pathlib.Path(__file__).resolve().parent.parent
SOURCES = REPO / "data" / "benchmark" / "sources"
STAGE1 = REPO / "data" / "benchmark" / "corpus-stage1"
SOURCES_TSV = REPO / "scripts" / "SOURCES.tsv"
BUILDER = REPO / "scripts" / "make-benchmark-corpus.py"


def sha(path, chunk=1 << 20):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        while True:
            b = fh.read(chunk)
            if not b:
                return h.hexdigest()
            h.update(b)


def pool_files():
    """Every downloaded file, by path relative to sources/. The .pools cache is
    derived from these and is not checked."""
    out = {}
    for sub in ("tar", "file", "html"):
        d = SOURCES / sub
        if not d.is_dir():
            continue
        for p in sorted(d.iterdir()):
            if p.is_file():
                out[f"{sub}/{p.name}"] = p
    return out


def expected_names():
    """What SOURCES.tsv says should be on disk, as relative paths."""
    if not SOURCES_TSV.exists():
        return {}
    want = {}
    for r in csv.DictReader(open(SOURCES_TSV), delimiter="\t"):
        if r["kind"] == "tar":
            want[f"tar/{r['name']}.tar.gz"] = r
        elif r["kind"] == "html":
            want["html/"] = r          # a directory of pages, checked by count
        else:
            want[f"file/{r['name']}"] = r
    return want


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--quick", action="store_true", help="skip the rebuild check")
    args = ap.parse_args()

    if not SOURCES.is_dir():
        print(f"no source pool at {SOURCES}", file=sys.stderr)
        print("run `just corpus-sources` first.", file=sys.stderr)
        return 2

    have = pool_files()

    bad, drift = 0, 0

    # --- presence -----------------------------------------------------------
    want = expected_names()
    missing = [n for n in want if not n.endswith("/") and n not in have]
    html_n = sum(1 for k in have if k.startswith("html/"))
    print(f"presence     {len(have)} files on disk for {len(want)} manifest entries "
          f"(the Wikipedia pages are one entry)")
    if missing:
        bad = 1
        print(f"  MISSING {len(missing)}:")
        for n in missing[:12]:
            print(f"    {n}")
        print("  re-run `just corpus-sources` (it skips what is already there).")
    if "html/" in want and html_n == 0:
        bad = 1
        print("  MISSING the Wikipedia pages under html/")
    empty = [n for n, p in have.items() if p.stat().st_size == 0]
    if empty:
        bad = 1
        print(f"  EMPTY {len(empty)}: {', '.join(empty[:6])}")
    if not missing and not empty:
        print(f"             ok, including {html_n} Wikipedia pages")

    # --- reproduction -------------------------------------------------------
    if args.quick:
        print("reproduction skipped (--quick)")
    elif not STAGE1.is_dir():
        print("reproduction no corpus-stage1/ to compare against -- run `just corpus-pull`")
        bad = 1
    else:
        tmp = pathlib.Path(tempfile.mkdtemp(prefix="corpus-verify-"))
        try:
            # --repool is required, not an optimisation: the category pools are
            # cached, so without it a drifted tarball would still rebuild from the
            # old cache and this check would pass while the pool had moved.
            r = subprocess.run([sys.executable, str(BUILDER), "--stage", "1",
                                "--out", str(tmp), "--force", "--repool"],
                               capture_output=True, text=True)
            if r.returncode != 0:
                print("reproduction builder failed:")
                print("  " + (r.stderr.strip().splitlines() or ["?"])[-1])
                bad = 1
            else:
                published = {p.name: sha(p) for p in STAGE1.iterdir() if p.is_file()}
                rebuilt = {p.name: sha(p) for p in tmp.iterdir() if p.is_file()}
                diff = sorted(set(published) ^ set(rebuilt)) + \
                    sorted(n for n in set(published) & set(rebuilt)
                           if published[n] != rebuilt[n])
                if diff:
                    drift = 1
                    print(f"reproduction {len(diff)} of {len(published)} files DIFFER")
                    for n in diff[:12]:
                        print(f"    {n}")
                    print("  The pool has drifted from the one stage 1 was cut from.")
                    print("  The published bytes remain the reference; nothing is broken,")
                    print("  but a stage 2 cut now is not the complement of that stage 1.")
                else:
                    print(f"reproduction ok, all {len(published)} files byte-identical")
        finally:
            shutil.rmtree(tmp, ignore_errors=True)

    if bad:
        print("\nINCOMPLETE -- the pool is missing files; re-run `just corpus-sources`.")
        return 1
    if drift:
        print("\nDRIFTED -- the pool is complete but no longer matches what stage 1 was")
        print("cut from. Nothing is broken: the published corpus-stage1/ is the reference")
        print("and is unaffected. A stage 2 cut now is simply not its exact complement.")
        return 3
    print("\nOK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
