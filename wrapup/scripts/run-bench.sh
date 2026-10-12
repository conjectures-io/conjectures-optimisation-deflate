#!/usr/bin/env bash
# Run `arena bench` over named corpora with one method list, pinned to one core,
# and record what else the host was doing. Results stay on the host that ran them
# (corpus-stage2 is held out: never copy its per-file rows anywhere public).
#
#   run-bench.sh OUT_DIR MODE "c1 c2 c3" METHOD...
#
# Environment: ARENA (binary), VALIDATOR (validator/ dir), WORK (crate cache),
# CORE (cpu to pin, default 7), REPS (11), WARMUP (1), HUFFMAN (fast),
# CORPUS_c1 / CORPUS_c2 / CORPUS_c3 / CORPUS_<name> (directories).
set -euo pipefail

out=$1 mode=$2 corpora=$3
shift 3
here=$(cd "$(dirname "$0")" && pwd)
ARENA=${ARENA:-$here/../arena/target/release/arena}
VALIDATOR=${VALIDATOR:-$here/../../validator}
WORK=${WORK:-/root/deflate-wrapup/crates}
CORE=${CORE:-7}
REPS=${REPS:-11}
WARMUP=${WARMUP:-1}
HUFFMAN=${HUFFMAN:-fast}
: "${CORPUS_c1:=/root/conjectures-optimisation-deflate/data/benchmark/corpus-stage1}"
: "${CORPUS_c2:=/root/conjectures-optimisation-deflate/data/benchmark/corpus-stage2}"
: "${CORPUS_c3:=/opt/conjectures-benchmark-corpus-stage3/corpus}"

mkdir -p "$out" "$WORK"
methods=()
for m in "$@"; do methods+=(--method "$m"); done

busy() {
    # Anything that competes for the CPU: the DEV gate, a rerun pass, another bench.
    pgrep -af 'verify\.py|rerun\.py|measure/target|cargo build' | grep -v pgrep || true
}

for c in $corpora; do
    var=CORPUS_$c
    dir=${!var:?no directory for corpus $c}
    tag=$(echo "$mode" | tr ':' '-')
    file="$out/$c-$tag.jsonl"
    {
        echo "# $(date -Is) host=$(hostname) load=$(cut -d' ' -f1-3 /proc/loadavg)"
        echo "# busy-before: $(busy | tr '\n' ';')"
    } > "$file.log"
    taskset -c "$CORE" "$ARENA" bench --corpus "$dir" --label "$c" --mode "$mode" \
        --huffman "$HUFFMAN" --reps "$REPS" --warmup "$WARMUP" \
        --validator "$VALIDATOR" --work "$WORK" "${methods[@]}" --out "$file"
    {
        echo "# $(date -Is) done load=$(cut -d' ' -f1-3 /proc/loadavg)"
        echo "# busy-after: $(busy | tr '\n' ';')"
    } >> "$file.log"
    echo "$file"
done
