#!/usr/bin/env bash
# Scenarios S1-S7 (PLAN.md §5) for a list of parsers, on this host.
#
#   run-scenarios.sh PARSERS_FILE OUT_DIR [s1 s2 s3 s4 s5 s6 s7]
#
# PARSERS_FILE: one `slot:NAME=PATH` per line. Parsers use adaptive blocks (what a
# production encoder would do); `retok-libdeflate-12` puts libdeflate's own parse
# through the same encoder. Every run is preceded by a timeout probe.
set -euo pipefail

parsers_file=$1 out=$2
shift 2
want=${*:-"s1 s2 s3 s4 s5 s6 s7"}
here=$(cd "$(dirname "$0")" && pwd)
ROOT=${ROOT:-/root/deflate-wrapup}
DATA=$ROOT/data
LIB=$ROOT/tools/lib
export TOOLS_DIR=$ROOT/tools/bin PATH=/root/.cargo/bin:$PATH
CORE=${CORE:-7}
mapfile -t P < <(grep -v '^\s*#' "$parsers_file" | sed '/^\s*$/d')
mkdir -p "$out"

zng() { echo "ref:so:zlib-ng=$LIB/zlib-ng.so@$1"; }
zcf() { echo "ref:so:zlib-cloudflare=$LIB/zlib-cloudflare.so@$1"; }

bench() { # tag corpus mode reps container extra-args... -- methods...
    local tag=$1 corpus=$2 mode=$3 reps=$4 container=$5
    shift 5
    local extra=()
    while [ "$1" != "--" ]; do extra+=("$1"); shift; done
    shift
    local ok
    mapfile -t ok < <(CORE=$CORE "$here/probe.sh" "$out/$tag" "$mode" "$corpus" 300 "$@")
    cp "$out/$tag/probe-failed.tsv" "$out/$tag-probe-failed.tsv"
    echo "== $tag: ${#ok[@]} of $# methods passed the probe" >&2
    local args=()
    for m in "${ok[@]}"; do args+=(--method "$m"); done
    {
        echo "# $(date -Is) load=$(cut -d' ' -f1-3 /proc/loadavg)"
    } > "$out/$tag.jsonl.log"
    taskset -c "$CORE" "$here/../arena/target/release/arena" bench --corpus "$corpus" --label "$tag" \
        --mode "$mode" --reps "$reps" --warmup 1 --container "$container" --huffman fast "${extra[@]}" \
        --validator "$here/../../validator" --work "$ROOT/crates" "${args[@]}" --out "$out/$tag.jsonl"
    echo "# $(date -Is) done load=$(cut -d' ' -f1-3 /proc/loadavg)" >> "$out/$tag.jsonl.log"
}

ext() { # tag corpus reps tools...
    local tag=$1 corpus=$2 reps=$3
    shift 3
    local args=()
    for t in "$@"; do args+=(--tool "$t"); done
    taskset -c "$CORE" python3 "$here/ext-bench.py" --corpus "$corpus" --label "$tag" --reps "$reps" \
        --warmup 1 "${args[@]}" --out "$out/$tag-ext.jsonl"
}

for s in $want; do
    case $s in
    s1) # Static web precompression: whole files, gzip framing.
        bench s1-web "$DATA/s1-web" whole 3 gzip --blocks adaptive -- "${P[@]}" \
            ref:zlib-6 ref:zlib-9 "$(zng 9)" ref:libdeflate-6 ref:libdeflate-9 ref:libdeflate-12 \
            ref:miniz_oxide-9 retok:libdeflate-12
        ext s1-web "$DATA/s1-web" 1 gzip-9 7z-gzip-9 zopfli-15
        ;;
    s2) # Large files: streamed in 1 MiB chunks, and whole-buffer for the whole-buffer libraries.
        bench s2-large-stream "$DATA/s2-large" stream:1m 3 gzip --blocks adaptive -- "${P[@]}" \
            ref:zlib-6 ref:zlib-9 "$(zng 6)" "$(zng 9)" "$(zcf 6)"
        bench s2-large-whole "$DATA/s2-large" whole 3 gzip --blocks adaptive -- "${P[@]}" \
            ref:libdeflate-6 ref:libdeflate-9 ref:libdeflate-12 ref:miniz_oxide-9 retok:libdeflate-12
        ext s2-large "$DATA/s2-large" 3 gzip-6 gzip-9 pigz-6 pigz-9 igzip-3 7z-gzip-9
        ;;
    s3) # BGZF genomics: 64 KiB independent blocks.
        bench s3-bgzf "$DATA/s3-bgzf" bgzf 3 raw --blocks adaptive -- "${P[@]}" \
            ref:libdeflate-1 ref:libdeflate-6 ref:libdeflate-12 ref:zlib-6 "$(zng 6)"
        ;;
    s4) # PNG: IDAT recompressed with the image's own filters; optimisers choose their own.
        bench s4-png "$DATA/s4-png" png 3 raw --blocks adaptive -- "${P[@]}" \
            ref:zlib-9 ref:libdeflate-12 ref:zopfli-i15
        ext s4-png "$DATA/s4-png" 1 oxipng-4 zopflipng-m
        ;;
    s5) # Archive members: every file its own stream (ZIP entries, git blobs).
        bench s5-archive "$DATA/s5-archive" whole 5 raw --blocks adaptive -- "${P[@]}" \
            ref:zlib-6 ref:zlib-9 "$(zng 6)" ref:libdeflate-6 ref:libdeflate-12 ref:miniz_oxide-9
        ;;
    s6) # Logs: streamed with a sync flush every 64 KiB.
        bench s6-logs "$DATA/s6-logs" stream:1m:64k 3 gzip --blocks adaptive -- "${P[@]}" \
            ref:zlib-1 ref:zlib-6 "$(zng 1)" "$(zng 6)" "$(zcf 6)"
        ;;
    s7) # Messages with context takeover, full and 4 KiB windows.
        bench s7-msg-w15 "$DATA/s7-messages" messages:15 3 raw --blocks adaptive -- "${P[@]}" \
            ref:zlib-6 "$(zng 6)"
        bench s7-msg-w12 "$DATA/s7-messages" messages:12 3 raw --blocks adaptive -- "${P[@]}" \
            ref:zlib-6 "$(zng 6)"
        ;;
    *) echo "unknown scenario $s" >&2; exit 2 ;;
    esac
done
