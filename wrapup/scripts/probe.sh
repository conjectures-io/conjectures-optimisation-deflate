#!/usr/bin/env bash
# Timeout probe before a timed run: one untimed pass per method over CORPUS, each
# method in its own process under `timeout` (PLAN: 300 s per file). Prints the
# methods that finished; methods that timed out or failed go to OUT/probe-failed.tsv
# with the reason, and are recorded as screen failures rather than run.
#
#   probe.sh OUT_DIR MODE CORPUS_DIR SECONDS_PER_FILE METHOD...
set -uo pipefail

out=$1 mode=$2 corpus=$3 per_file=$4
shift 4
here=$(cd "$(dirname "$0")" && pwd)
ARENA=${ARENA:-$here/../arena/target/release/arena}
VALIDATOR=${VALIDATOR:-$here/../../validator}
WORK=${WORK:-/root/deflate-wrapup/crates}
CORE=${CORE:-7}
mkdir -p "$out"
nfiles=$(find "$corpus" -type f ! -name '.*' | wc -l)
limit=$((per_file * nfiles))
: > "$out/probe-failed.tsv"
for m in "$@"; do
    log="$out/probe-$(echo "$m" | cut -d= -f1 | tr ':/' '__').jsonl"
    timeout "$limit" taskset -c "$CORE" "$ARENA" bench --corpus "$corpus" --label probe --mode "$mode" \
        --reps 1 --warmup 0 --validator "$VALIDATOR" --work "$WORK" --method "$m" --out "$log" 2>/dev/null
    rc=$?
    if [ $rc -eq 124 ]; then
        printf '%s\ttimeout after %ss on %s\n' "$m" "$limit" "$corpus" >> "$out/probe-failed.tsv"
    elif [ $rc -ne 0 ]; then
        printf '%s\texit %s\n' "$m" "$rc" >> "$out/probe-failed.tsv"
    else
        echo "$m"
    fi
done
