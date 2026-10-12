#!/usr/bin/env bash
# Fetch and prepare the real-world scenario data (PLAN.md §5) into DATA_DIR.
# Idempotent: a scenario whose directory has a .done marker is skipped. Every
# source is pinned (version or date); MANIFEST.tsv records sha256 and size of
# every prepared file. Sizes are capped so the whole set stays a few GB.
#
#   fetch-scenarios.sh [DATA_DIR] [s1 s2 s3 s4 s5 s6 s7]
#
# S6 (logs) reads this host's own logs: the files stay on this host; only
# aggregate numbers may leave it.
set -euo pipefail

DATA=${1:-/root/deflate-wrapup/data}
shift || true
want=${*:-"s1 s2 s3 s4 s5 s6 s7"}
mkdir -p "$DATA/_dl"
DL=$DATA/_dl

fetch() { # url [name]
    local url=$1 name=${2:-$(basename "${1%%\?*}")}
    if [ ! -s "$DL/$name" ]; then
        echo "  fetch $url" >&2
        curl -fsSL --retry 3 -o "$DL/$name.part" "$url"
        mv "$DL/$name.part" "$DL/$name"
    fi
    echo "$DL/$name"
}

done_or_start() { # dir
    [ -e "$1/.done" ] && { echo "skip $(basename "$1") (done)"; return 1; }
    rm -rf "$1"; mkdir -p "$1"; return 0
}

# ── S1: static web assets (gzip_static / CDN precompression) ────────────────────
s1() {
    local out=$DATA/s1-web
    done_or_start "$out" || return 0
    local pkgs="react-dom@18.3.1 react@18.3.1 three@0.169.0 d3@7.9.0 lodash@4.17.21 bootstrap@5.3.3
        jquery@3.7.1 vue@3.5.12 chart.js@4.4.4 leaflet@1.9.4 bootstrap-icons@1.11.3 @angular/core@18.2.8
        rxjs@7.8.1 moment@2.30.1 typescript@5.6.3 highlight.js@11.10.0 katex@0.16.11 mathjax@3.2.2
        echarts@5.5.1 pdfjs-dist@4.7.76 ace-builds@1.36.2 font-awesome@4.7.0 bulma@1.0.2 alpinejs@3.14.1"
    local p name ver tgz scope base
    for p in $pkgs; do
        name=${p%@*} ver=${p##*@}
        base=$(basename "$name")
        tgz=$(fetch "https://registry.npmjs.org/$name/-/$base-$ver.tgz" "npm-${name//\//_}-$ver.tgz")
        mkdir -p "$out/${name//\//_}"
        tar -xzf "$tgz" -C "$out/${name//\//_}" --strip-components=1
    done
    local docs
    docs=$(fetch https://docs.python.org/3.13/archives/python-3.13-docs-html.tar.bz2 python-3.13-docs-html.tar.bz2)
    mkdir -p "$out/python-docs" && tar -xjf "$docs" -C "$out/python-docs" --strip-components=1
    # Keep what a web server precompresses; drop everything else and empties.
    find "$out" -type f ! \( -name '*.js' -o -name '*.mjs' -o -name '*.cjs' -o -name '*.css' -o -name '*.html' \
        -o -name '*.svg' -o -name '*.json' -o -name '*.map' -o -name '*.xml' -o -name '*.txt' -o -name '*.d.ts' \) -delete
    find "$out" -type f -size 0 -delete
    find "$out" -type d -empty -delete
    touch "$out/.done"
}

# ── S2: large-file gzip ─────────────────────────────────────────────────────────
s2() {
    local out=$DATA/s2-large
    done_or_start "$out" || return 0
    local z
    z=$(fetch https://sun.aei.polsl.pl/~sdeor/corpus/silesia.zip)
    unzip -q -o "$z" -d "$out/silesia"
    z=$(fetch https://mattmahoney.net/dc/enwik8.zip)
    unzip -q -o "$z" -d "$out"
    z=$(fetch https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-6.6.tar.xz)
    xz -dc "$z" | head -c $((256 * 1024 * 1024)) > "$out/linux-6.6.tar.head256m" || true
    z=$(fetch https://www.python.org/ftp/python/3.13.0/Python-3.13.0.tar.xz)
    xz -dc "$z" > "$out/Python-3.13.0.tar"
    z=$(fetch https://data.gharchive.org/2024-01-01-15.json.gz gharchive-2024-01-01-15.json.gz)
    gzip -dc "$z" | head -c $((128 * 1024 * 1024)) > "$out/gharchive-2024-01-01-15.json.head128m" || true
    touch "$out/.done"
}

# ── S3: BGZF genomics ───────────────────────────────────────────────────────────
s3() {
    local out=$DATA/s3-bgzf
    done_or_start "$out" || return 0
    local base=https://ftp.1000genomes.ebi.ac.uk/vol1/ftp
    # Streamed and cut: the full files are tens of GB.
    curl -fsSL "$base/release/20130502/ALL.chr22.phase3_shapeit2_mvncall_integrated_v5b.20130502.genotypes.vcf.gz" \
        | gzip -dc 2>/dev/null | head -c $((192 * 1024 * 1024)) > "$out/chr22.vcf.head192m" || true
    curl -fsSL "$base/phase3/data/HG00096/sequence_read/SRR062634_1.filt.fastq.gz" \
        | gzip -dc 2>/dev/null | head -c $((192 * 1024 * 1024)) > "$out/SRR062634_1.fastq.head192m" || true
    # The first 48 MB of a BAM's BGZF blocks, decoded: raw BAM records, what bgzip re-encodes.
    curl -fsSL -r 0-$((48 * 1024 * 1024 - 1)) \
        "$base/phase3/data/HG00096/alignment/HG00096.mapped.ILLUMINA.bwa.GBR.low_coverage.20120522.bam" \
        -o "$DL/HG00096.head48m.bam" || true
    python3 - "$DL/HG00096.head48m.bam" "$out/HG00096.bam.records" <<'EOF'
import sys, zlib
data = open(sys.argv[1], "rb").read()
out, pos = bytearray(), 0
while pos + 18 <= len(data):
    if data[pos:pos + 4] != b"\x1f\x8b\x08\x04":
        break
    bsize = int.from_bytes(data[pos + 16:pos + 18], "little") + 1
    if pos + bsize > len(data):
        break
    out += zlib.decompress(data[pos + 18:pos + bsize - 8], -15)
    pos += bsize
open(sys.argv[2], "wb").write(out)
print(f"  BAM: {pos} bytes of blocks -> {len(out)} bytes of records", file=sys.stderr)
EOF
    find "$out" -type f -size 0 -delete
    touch "$out/.done"
}

# ── S4: PNG image data ──────────────────────────────────────────────────────────
s4() {
    local out=$DATA/s4-png
    done_or_start "$out" || return 0
    mkdir -p "$out/kodak" "$out/emoji" "$out/docs"
    local i
    for i in $(seq -w 1 24); do
        cp "$(fetch "https://r0k.us/graphics/kodak/kodak/kodim$i.png" "kodim$i.png")" "$out/kodak/"
    done
    # A fixed list of Fluent UI emoji (MIT): 3D-rendered graphics with alpha. The
    # branch moves; MANIFEST.tsv pins the bytes actually used.
    local raw=https://raw.githubusercontent.com/microsoft/fluentui-emoji/main/assets
    local e
    for e in "Grinning face" "Red heart" "Rocket" "Thumbs up" "Fire" "Party popper" "Sparkles" "Star" \
             "Sun" "Rainbow" "Globe showing europe-africa" "Laptop" "Light bulb" "Books" "Hammer and wrench" "Gear"; do
        local f=${e,,}; f=${f// /_}
        curl -fsSL "$raw/${e// /%20}/3D/${f}_3d.png" -o "$out/emoji/${f}_3d.png" || echo "  missing emoji $e" >&2
    done
    # Screenshots and diagrams that ship with the Python docs (S1 must run first).
    find "$DATA/_dl" -maxdepth 1 -name 'python-3.13-docs-html.tar.bz2' -exec tar -xjf {} -C "$out/docs" --wildcards '*.png' \; 2>/dev/null || true
    find "$out/docs" -name '*.png' -exec mv -t "$out/docs" {} + 2>/dev/null || true
    find "$out/docs" -mindepth 1 -type d -exec rm -rf {} + 2>/dev/null || true
    find "$out" -type f -size 0 -delete
    touch "$out/.done"
}

# ── S5: archives and many small members (ZIP entries, git blobs) ────────────────
s5() {
    local out=$DATA/s5-archive
    done_or_start "$out" || return 0
    local z
    z=$(fetch https://www.python.org/ftp/python/3.13.0/Python-3.13.0.tar.xz)
    mkdir -p "$out/cpython-lib"
    xz -dc "$z" | tar -x -C "$out/cpython-lib" --strip-components=2 Python-3.13.0/Lib
    z=$(fetch https://repo1.maven.org/maven2/com/google/guava/guava/33.3.1-jre/guava-33.3.1-jre.jar)
    mkdir -p "$out/guava-jar" && unzip -q -o "$z" -d "$out/guava-jar"
    find "$out" -type f -size 0 -delete
    touch "$out/.done"
}

# ── S6: logs (this host's own; they stay here) ──────────────────────────────────
s6() {
    local out=$DATA/s6-logs
    done_or_start "$out" || return 0
    journalctl -o short-iso --since "2026-09-28" --until "2026-10-12" --no-pager 2>/dev/null \
        | head -c $((256 * 1024 * 1024)) > "$out/journal.log" || true
    { cat /var/log/nginx/access.log.1 2>/dev/null; zcat /var/log/nginx/access.log.*.gz 2>/dev/null; } \
        | head -c $((128 * 1024 * 1024)) > "$out/nginx-access.log" || true
    find /home/root/.pm2/logs -name '*.log' -size +1M -printf '%s %p\n' 2>/dev/null | sort -rn | head -3 \
        | while read -r _ f; do head -c $((96 * 1024 * 1024)) "$f" > "$out/pm2-$(basename "$f")"; done
    chmod 600 "$out"/*
    touch "$out/.done"
}

# ── S7: small messages with context takeover (WebSocket permessage-deflate) ─────
s7() {
    local out=$DATA/s7-messages
    done_or_start "$out" || return 0
    local z
    z=$(fetch https://data.gharchive.org/2024-01-01-15.json.gz gharchive-2024-01-01-15.json.gz)
    # One JSON event per line: a message stream. 20,000 messages, as they come.
    gzip -dc "$z" | head -n 20000 > "$out/gharchive-events.jsonl" || true
    touch "$out/.done"
}

for s in $want; do
    echo "== $s"
    "$s"
done

# Manifest of everything prepared (not the downloads).
( cd "$DATA" && find . -path ./_dl -prune -o -type f ! -name '.done' ! -name MANIFEST.tsv -print0 \
    | sort -z | xargs -0 sha256sum | awk '{print $2"\t"$1}' > MANIFEST.tsv.tmp \
  && while IFS=$'\t' read -r f h; do printf '%s\t%s\t%s\n' "$f" "$(stat -c %s "$f")" "$h"; done < MANIFEST.tsv.tmp > MANIFEST.tsv \
  && rm MANIFEST.tsv.tmp )
du -sh "$DATA"/s* 2>/dev/null
