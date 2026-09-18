#!/usr/bin/env bash
# Toolchain pins and paths, all overridable from the environment; `just init` installs into `.work/`. Source this; do not run it.

_cfg_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
_work="$_cfg_root/.work"

# --- Pins: pinned to each other, bump all or none. Aeneas reads LLBC only from its `charon-pin` Charon, which needs this nightly.
# LEAN_TOOLCHAIN must match `lean/lean-toolchain`, the Aeneas Lean backend, and the Mathlib pin in `lean/lake-manifest.json`.
: "${AENEAS_TAG:=nightly-2026.08.27-5b9dcf3}"
: "${CHARON_REV:=4ad295c1bf982b5533ce7d85f4ddc889ff3127f8}"
: "${CHARON_TOOLCHAIN:=nightly-2026-08-18}"
: "${LEAN_TOOLCHAIN:=leanprover/lean4:v4.31.0}"

# --- Download pins: every fetch sha256-checked so all validators get a byte-identical `Slot/Funs.lean`; Mathlib and Aeneas are pinned by git revision in the lake manifest, rustup checks the nightly itself.
# The Aeneas tarball digest was taken from a download on 2026-09-11, the one the smoke numbers were measured with.
AENEAS_URL="https://github.com/AeneasVerif/aeneas/releases/download/$AENEAS_TAG/aeneas-linux-x86_64.tar.gz"
AENEAS_SHA256="bd6e2379969796af6d1784532a7f5a162ec27d01237fdde8570244052f297e94"
ELAN_VERSION="v4.2.4"
ELAN_URL="https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-x86_64-unknown-linux-gnu.tar.gz"
ELAN_SHA256="42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63"
RUSTUP_VERSION="1.29.1"
RUSTUP_URL="https://static.rust-lang.org/rustup/archive/$RUSTUP_VERSION/x86_64-unknown-linux-gnu/rustup-init"
RUSTUP_SHA256="dda7234360b7f578ca8b0ddcb80145646fa61a67c1720a5abc7051b35c9fcb71"

# fetch_pinned URL DEST SHA256 - download and verify, or remove the file and return 2; a mismatch is never installed.
fetch_pinned() {
    curl -sSfL -o "$2" "$1" || { echo "download failed: $1" >&2; return 2; }
    local got; got="$(sha256sum "$2" | cut -d' ' -f1)"
    if [ "$got" != "$3" ]; then
        rm -f "$2"
        echo "sha256 mismatch for $1" >&2
        echo "  expected $3" >&2
        echo "  got      $got" >&2
        return 2
    fi
}

# --- Charon and Aeneas: release tarball ($AENEAS_WORK/{aeneas,charon}) or cargo install ($AENEAS_WORK/charon/bin/charon) ---
# `just init` uses the tarball, whose Charon matches its Aeneas; both layouts produce identical models.
: "${AENEAS_WORK:=$_work/aeneas}"

# The directory to put on PATH so that `charon` resolves, whichever layout it is.
if [ -x "$AENEAS_WORK/charon/bin/charon" ]; then
    CHARON_DIR="$AENEAS_WORK/charon/bin"
else
    CHARON_DIR="$AENEAS_WORK"
fi

# --- Lean -------------------------------------------------------------------
# elan: the one `init` installs, or an existing user install; anything with `bin/lake`.
if [ -z "${ELAN_HOME:-}" ]; then
    for _c in "$_work/elan" "$HOME/.elan"; do
        if [ -x "$_c/bin/lake" ]; then ELAN_HOME="$(cd "$_c" && pwd)"; break; fi
    done
    : "${ELAN_HOME:=$_work/elan}"
fi

# LEAN_PACKAGES: an existing Mathlib + Aeneas checkout at the same pins to share; empty fetches our own 7 GB.
: "${LEAN_PACKAGES:=}"

export AENEAS_TAG CHARON_REV CHARON_TOOLCHAIN LEAN_TOOLCHAIN
export AENEAS_URL AENEAS_SHA256 ELAN_URL ELAN_SHA256 RUSTUP_URL RUSTUP_SHA256
export AENEAS_WORK CHARON_DIR ELAN_HOME LEAN_PACKAGES
export PATH="$ELAN_HOME/bin:$PATH"
unset _cfg_root _work _c 2>/dev/null || true
