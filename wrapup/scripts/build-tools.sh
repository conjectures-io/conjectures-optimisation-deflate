#!/usr/bin/env bash
# Build the external DEFLATE implementations the scenarios compare against, into
# TOOLS (default /root/deflate-wrapup/tools). Nothing is installed system-wide.
# Pinned versions; each tool is skipped when already built.
#
#   build-tools.sh [TOOLS]
#
# Results:
#   lib/zlib-madler.so  lib/zlib-ng.so  lib/zlib-cloudflare.so   (load with `ref:so:NAME=PATH@LEVEL`)
#   bin/zopfli bin/zopflipng bin/7zz bin/oxipng bin/igzip bin/nasm
set -euo pipefail

TOOLS=${1:-/root/deflate-wrapup/tools}
mkdir -p "$TOOLS"/{src,lib,bin}
cd "$TOOLS/src"
export PATH=$TOOLS/bin:/root/.cargo/bin:$PATH
JOBS=$(nproc)

get() { # url dir
    [ -d "$2" ] && return 0
    echo "fetch $1" >&2
    mkdir -p "$2.tmp"
    curl -fsSL --retry 3 "$1" | tar -xz -C "$2.tmp" --strip-components=1 2>/dev/null \
        || curl -fsSL --retry 3 "$1" | tar -xJ -C "$2.tmp" --strip-components=1
    mv "$2.tmp" "$2"
}

zlib_like() { # name url configure-args...
    local name=$1 url=$2
    shift 2
    [ -e "$TOOLS/lib/$name.so" ] && return 0
    get "$url" "$name"
    (cd "$name" && ./configure "$@" >/dev/null && make -j"$JOBS" >/dev/null)
    local so
    so=$(cd "$name" && ls libz.so.1.* 2>/dev/null | head -1)
    cp "$name/$so" "$TOOLS/lib/$name.so"
    echo "built lib/$name.so ($so)"
}

zlib_like zlib-madler https://zlib.net/fossils/zlib-1.3.1.tar.gz
zlib_like zlib-ng https://github.com/zlib-ng/zlib-ng/archive/refs/tags/2.2.2.tar.gz --zlib-compat
zlib_like zlib-cloudflare https://github.com/cloudflare/zlib/archive/refs/heads/gcc.amd64.tar.gz

if [ ! -x "$TOOLS/bin/zopflipng" ]; then
    get https://github.com/google/zopfli/archive/refs/tags/zopfli-1.0.3.tar.gz zopfli
    (cd zopfli && make -j"$JOBS" zopfli zopflipng >/dev/null && cp zopfli zopflipng "$TOOLS/bin/")
    echo "built bin/zopfli bin/zopflipng"
fi

if [ ! -x "$TOOLS/bin/7zz" ]; then
    mkdir -p 7zip && curl -fsSL https://www.7-zip.org/a/7z2501-linux-x64.tar.xz | tar -xJ -C 7zip
    cp 7zip/7zz "$TOOLS/bin/"
    echo "installed bin/7zz"
fi

if [ ! -x "$TOOLS/bin/oxipng" ]; then
    cargo install oxipng --version 9.1.2 --locked --root "$TOOLS" -q
    echo "built bin/oxipng"
fi

if [ ! -x "$TOOLS/bin/nasm" ]; then
    get https://www.nasm.us/pub/nasm/releasebuilds/2.16.03/nasm-2.16.03.tar.gz nasm
    (cd nasm && ./configure --prefix="$TOOLS" >/dev/null && make -j"$JOBS" >/dev/null && make install >/dev/null)
    echo "built bin/nasm"
fi

if [ ! -x "$TOOLS/bin/igzip" ]; then
    get https://github.com/intel/isa-l/archive/refs/tags/v2.31.0.tar.gz isa-l
    (cd isa-l && make -f Makefile.unx -j"$JOBS" programs/igzip >/dev/null && cp programs/igzip "$TOOLS/bin/")
    echo "built bin/igzip"
fi

for so in "$TOOLS"/lib/*.so; do echo "$so"; done
"$TOOLS/bin/7zz" i 2>/dev/null | head -2 | tail -1 || true
"$TOOLS/bin/oxipng" --version || true
"$TOOLS/bin/igzip" --version 2>&1 | head -1 || true
