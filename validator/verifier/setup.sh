#!/usr/bin/env bash
# First-time setup: give the Lean package its dependencies.
#
# Aeneas pulls Mathlib, whose olean cache is about 7 GB. If `LEAN_PACKAGES` names
# an existing checkout at the same pins, `.lake/packages` is symlinked at it and
# nothing is downloaded. Otherwise lake fetches its own and `lake exe cache get`
# pulls Mathlib's prebuilt oleans rather than building them.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
# shellcheck source=config.sh
. "$root/verifier/config.sh"

command -v lake >/dev/null || { echo "no lake on PATH -- set ELAN_HOME" >&2; exit 2; }
lean --version

cd "$root/lean"
if [ -L .lake/packages ] || [ -d .lake/packages ]; then
    echo ".lake/packages already present; nothing to do"
elif [ -d "$LEAN_PACKAGES/mathlib/.lake/build/lib/lean" ]; then
    mkdir -p .lake
    ln -sfn "$LEAN_PACKAGES" .lake/packages
    echo "symlinked .lake/packages -> $LEAN_PACKAGES"
else
    echo "no shared checkout at $LEAN_PACKAGES; fetching our own (this is slow)"
    lake update
    (cd .lake/packages/mathlib && lake exe cache get) || true
fi

lake build Lz77
echo
echo "setup ok"
