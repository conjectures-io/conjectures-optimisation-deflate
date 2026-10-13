#!/usr/bin/env bash
# Recreate the wrap-up results, stage by stage (docs/wrapup/METHODOLOGY.md §9).
#
#   reproduce.sh STAGE...      stages run in the order given
#
# Stages, in pipeline order:
#   build      build wrapup/arena (pinned nightly) and run its tests
#   tools      build the external compressors into $ROOT/tools
#   data       fetch scenario data S1-S7 into $ROOT/data (S6 = this host's own logs)
#   setA       generate the robustness set
#   c4         generate the fresh holdout C4 (needs `data`)
#   sources    unpack the PROD sources export (needs $ROOT/prod-export/*.csv.gz)
#   stats      competition statistics from the PROD dump's tables
#   pool       behaviour groups and the preliminary general frontier (rerun data)
#   bars       references and controls on c1, c2, c3                 (~20 min)
#   stage1     public general-frontier groups + contrasts on C4, set A (~40 min)
#   stage1b    PROD-only groups, record-holders, withheld on C4, set A (~35 min)
#   withheld   size-only c1-c3 check of the four withheld frontier points
#   select     the screen (revised and strict) and the selection
#   scenarios  S1-S7 for the selected parsers                         (~7.5 h)
#   report     per-scenario tables
#
# Environment: ROOT (default /root/deflate-wrapup, with this checkout at $ROOT/src),
# CORE (timing core, default 7), CORPUS_c1/_c2/_c3 (competition corpora).
# Every timed stage runs on one pinned core; run nothing else heavy meanwhile.
set -euo pipefail

ROOT=${ROOT:-/root/deflate-wrapup}
SRC=$ROOT/src
S=$SRC/wrapup/scripts
export PATH=/root/.cargo/bin:$PATH
export CORE=${CORE:-7}
export WORK=$ROOT/crates
export CORPUS_c1=${CORPUS_c1:-/root/conjectures-optimisation-deflate/data/benchmark/corpus-stage1}
export CORPUS_c2=${CORPUS_c2:-/root/conjectures-optimisation-deflate/data/benchmark/corpus-stage2}
export CORPUS_c3=${CORPUS_c3:-/opt/conjectures-benchmark-corpus-stage3/corpus}
export CORPUS_c4=$ROOT/data/c4/files CORPUS_setA=$ROOT/data/setA
X=prod-export/sources
V=src/validator
M=src/miner/examples
L=$ROOT/tools/lib
R=$ROOT/results
cd "$ROOT"

slots() { for i in "$@"; do echo "slot:p$i=$X/$i/parse.rs"; done; }
controls() {
    echo "slot:incumbent=$V/incumbent/parse.rs"
    echo "slot:mo-lazy=$M/mo-lazy/parse.rs"
    echo "slot:optimal-iter=$M/optimal-iter/parse.rs"
}
refs() {
    echo ref:libdeflate-1 ref:libdeflate-6 ref:libdeflate-9 ref:libdeflate-12 ref:zlib-6 ref:zlib-9 \
        ref:miniz_oxide-9 "ref:so:zlib-ng=$L/zlib-ng.so@6" "ref:so:zlib-ng=$L/zlib-ng.so@9" | tr ' ' '\n'
}

# The candidate lists exactly as run (2026-10-12).
STAGE1_IDS="88 34 33 57 61 148 55 48 59 23 17 232 443 252 360 280 294 355 444 473 120 239 243 112 140 196 113 85 125 87"
STAGE1B_IDS="521 653 656 657 296 357 635 645 639 649 644 636 655 632 405 518 562 638"
WITHHELD_IDS="405 518 562 638"

stage() {
    case $1 in
    build)
        (cd "$SRC/wrapup/arena" && cargo +nightly-2026-08-18 build --release && cargo +nightly-2026-08-18 test --release)
        ;;
    tools) "$S/build-tools.sh" "$ROOT/tools" ;;
    data) "$S/fetch-scenarios.sh" "$ROOT/data" ;;
    setA) python3 "$S/gen-setA.py" "$ROOT/data/setA" --scale-source "$ROOT/data/s2-large/enwik8" ;;
    c4)
        python3 "$S/make-c4.py" "$ROOT/data" "$ROOT/data/c4"
        echo "C4 manifest sha256 (pre-registered: 870e0590a3f00aa8...):"
        sha256sum "$ROOT/data/c4/MANIFEST.tsv"
        ;;
    sources)
        python3 "$S/unpack-prod-sources.py" prod-export/deflate-prod-sources-*.csv.gz prod-export/sources
        ;;
    stats)
        mkdir -p prod-export/tables "$R/04-summary"
        for t in submissions registrations weight_sets score_snapshots bounty_accruals bounty_epochs bounty_caps; do
            docker exec -i conjectures_deflate_db pg_restore --data-only -t "$t" -f - \
                < prod-export/deflate-prod-*.dump > "prod-export/tables/$t.sql"
        done
        python3 "$S/competition-stats.py" prod-export/tables --json "$R/04-summary/competition-stats.json"
        ;;
    pool)
        mkdir -p "$R/00-pool"
        cp /var/www/competition-dashboard/reruns-operator/prod.json "$R/00-pool/operator-prod.json"
        python3 "$S/pool.py" "$R/00-pool/operator-prod.json" --out "$R/00-pool/pool.csv"
        ;;
    bars)
        mapfile -t m < <(controls; slots 112 243 140 196 113 85 125 87; refs | grep -v zlib-ng; \
            printf '%s\n' ref:zlib-1 ref:miniz_oxide-1 ref:miniz_oxide-6 retok:libdeflate-12 retok:libdeflate-6 retok:zlib-9)
        REPS=11 WARMUP=1 "$S/run-bench.sh" "$R/01-bars" whole "c1 c2 c3" "${m[@]}"
        python3 "$S/rank.py" --json "$R/01-bars/rank.json" "$R"/01-bars/c{1,2,3}-whole.jsonl
        ;;
    stage1)
        mapfile -t m < <(controls; slots $STAGE1_IDS; refs)
        REPS=5 WARMUP=1 "$S/run-bench.sh" "$R/02-stage1" whole c4 "${m[@]}"
        REPS=3 WARMUP=1 "$S/run-bench.sh" "$R/02-stage1" whole setA "${m[@]}"
        ;;
    stage1b)
        mapfile -t cand < <(controls; slots $STAGE1B_IDS)
        mapfile -t ok < <("$S/probe.sh" "$R/03-stage1b/probe" whole "$CORPUS_setA" 300 "${cand[@]}")
        mapfile -t r < <(refs)
        REPS=5 WARMUP=1 "$S/run-bench.sh" "$R/03-stage1b" whole c4 "${ok[@]}" "${r[@]}"
        REPS=3 WARMUP=1 "$S/run-bench.sh" "$R/03-stage1b" whole setA "${ok[@]}" "${r[@]}"
        ;;
    withheld)
        mapfile -t m < <(echo "slot:incumbent=$V/incumbent/parse.rs"; slots $WITHHELD_IDS)
        REPS=1 WARMUP=0 "$S/run-bench.sh" "$R/05-select/withheld" whole "c1 c2 c3" "${m[@]}"
        # The revised size rule (select.py) on these sizes -> supplementary screen failures.
        python3 - "$R/05-select/withheld" > "$R/05-select/withheld-fails.tsv" <<'PY'
import json, sys
from pathlib import Path
fails = {}
for c in ("c1", "c2", "c3"):
    rows = [json.loads(x) for x in (Path(sys.argv[1]) / f"{c}-whole.jsonl").read_text().splitlines()[1:]]
    inc = {r["file"]: r["bytes"] for r in rows if r["method"] == "incumbent"}
    for r in rows:
        if r["method"] == "incumbent":
            continue
        d = r["bytes"] - inc[r["file"]]
        if not r["verified"] or (d > 32 and d > 0.01 * r["raw"] and d / inc[r["file"]] > 0.2):
            name = r["file"] if c != "c2" else "(held-out file)"
            fails.setdefault(r["method"], []).append(f"{c}/{name} {100 * d / inc[r['file']]:+.1f}%")
for m, f in fails.items():
    print(f"{m}\t{f[0]} and {len(f) - 1} more (supplementary c1-c3 run)")
PY
        cat "$R/05-select/withheld-fails.tsv"
        ;;
    select)
        for rules in revised strict; do
            python3 "$S/select.py" --rules "$rules" --extra-fails "$R/05-select/withheld-fails.tsv" \
                --index prod-export/sources/index.tsv --operator "$R/00-pool/operator-prod.json" \
                --pool "$R/00-pool/pool.csv" --map data/c4/map.json \
                --c4 "$R/02-stage1/c4-whole.jsonl" "$R/03-stage1b/c4-whole.jsonl" \
                --setA "$R/02-stage1/setA-whole.jsonl" "$R/03-stage1b/setA-whole.jsonl" \
                --boot 2000 --json "$R/05-select/select-$rules.json" | tee "$R/05-select/select-$rules.txt"
        done
        ;;
    scenarios)
        {
            echo "# selected (revised screen)"; slots 55 232 657 355 243
            echo "# strict-screen survivors not selected above"; slots 85 521
            echo "# contrasts: best c1 bytes, fastest official frontier, the 09-30 dossier showcase"; slots 649 632 125
            echo "slot:incumbent=$V/incumbent/parse.rs"
        } > "$R/05-select/parsers.txt"
        "$S/run-scenarios.sh" "$R/05-select/parsers.txt" "$R/06-scenarios"
        ;;
    report)
        mkdir -p "$R/07-report"
        python3 "$S/scenario-report.py" "$R/06-scenarios" --json "$R/07-report/scenarios.json" \
            --md "$R/07-report/scenarios.md"
        ;;
    *) echo "unknown stage $1" >&2; exit 2 ;;
    esac
}

[ $# -gt 0 ] || { sed -n '2,30p' "$0"; exit 2; }
for st in "$@"; do
    echo "=== $st ($(date -Is))"
    stage "$st"
done
