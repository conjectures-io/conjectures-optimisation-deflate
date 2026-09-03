#!/usr/bin/env bash
# Toolchain pins and paths. Source this; do not run it.
#
# `just init` installs everything named here into `.work/`. Every path can be
# overridden from the environment, and if a suitable toolchain already exists
# elsewhere on the machine it is reused rather than downloaded again.

_cfg_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
_work="$_cfg_root/.work"

# --- Pins -------------------------------------------------------------------
#
# These four are pinned TO EACH OTHER, not chosen independently.
#
# Aeneas refuses LLBC produced by any Charon but the one it was built against,
# so CHARON_REV is whatever `charon-pin` carries at AENEAS_TAG, and
# CHARON_TOOLCHAIN is the nightly that revision of Charon compiles with -- it is
# a rustc driver, so it needs that exact compiler and its `rustc-dev` component.
# Bump all of them together or none of them.
#
# LEAN_TOOLCHAIN must match `lean/lean-toolchain`, which must match what the
# pinned Aeneas Lean backend requires, which is also what
# `lean/lake-manifest.json` pins Mathlib against.
: "${AENEAS_TAG:=nightly-2026.08.27-5b9dcf3}"
: "${CHARON_REV:=4ad295c1bf982b5533ce7d85f4ddc889ff3127f8}"
: "${CHARON_TOOLCHAIN:=nightly-2026-08-18}"
: "${LEAN_TOOLCHAIN:=leanprover/lean4:v4.31.0}"

# --- Charon and Aeneas ------------------------------------------------------
#
# Two layouts are accepted, because there are two ways to get these tools:
#
#   release tarball   $AENEAS_WORK/aeneas, $AENEAS_WORK/charon
#   cargo install     $AENEAS_WORK/aeneas, $AENEAS_WORK/charon/bin/charon
#
# The tarball ships a Charon built against the matching Aeneas, so `just init`
# uses it and nobody has to build a rustc driver. Checked: the two produce
# identical models, differing only in the paths inside doc comments.
_have_pair() {
    [ -x "$1/aeneas" ] && { [ -x "$1/charon" ] || [ -x "$1/charon/bin/charon" ]; }
}
if [ -z "${AENEAS_WORK:-}" ]; then
    for _c in "$_work/aeneas" \
              "$_cfg_root/../../conjectures-rust/.work/aeneas"; do
        if _have_pair "$_c"; then AENEAS_WORK="$(cd "$_c" && pwd)"; break; fi
    done
    : "${AENEAS_WORK:=$_work/aeneas}"
fi

# The directory to put on PATH so that `charon` resolves, whichever layout it is.
if [ -x "$AENEAS_WORK/charon/bin/charon" ]; then
    CHARON_DIR="$AENEAS_WORK/charon/bin"
else
    CHARON_DIR="$AENEAS_WORK"
fi

# --- Lean -------------------------------------------------------------------
# Anything with a `bin/lake`.
if [ -z "${ELAN_HOME:-}" ]; then
    for _c in "$_work/elan" "$HOME/.elan" \
              "$_cfg_root/../../conjectures-validator/.elan"; do
        if [ -x "$_c/bin/lake" ]; then ELAN_HOME="$(cd "$_c" && pwd)"; break; fi
    done
    : "${ELAN_HOME:=$_work/elan}"
fi

# An existing Mathlib + Aeneas checkout at the same pins, to share rather than
# fetch again. Mathlib's olean cache is about 7 GB, so this is worth the
# coupling. Leave it empty to always fetch our own.
if [ -z "${LEAN_PACKAGES:-}" ]; then
    for _c in "$_cfg_root/../../conjectures-research/probes/aeneas-reach/.lake/packages"; do
        if [ -d "$_c/mathlib/.lake/build/lib/lean" ]; then
            LEAN_PACKAGES="$(cd "$_c" && pwd)"; break
        fi
    done
    : "${LEAN_PACKAGES:=}"
fi

export AENEAS_TAG CHARON_REV CHARON_TOOLCHAIN LEAN_TOOLCHAIN
export AENEAS_WORK CHARON_DIR ELAN_HOME LEAN_PACKAGES
export PATH="$ELAN_HOME/bin:$PATH"
unset _cfg_root _work _c
