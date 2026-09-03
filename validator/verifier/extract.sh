#!/usr/bin/env bash
# Translate the submitted Rust into Lean with charon and aeneas.
#
#   verifier/extract.sh [path/to/parse.rs]
#
# The verifier runs this **itself**, on every submission. An extraction that
# arrives inside a submission is a claim about a program made by the person whose
# program it is, and is worth nothing.
#
# A submission that reaches outside Aeneas's model of `core` produces a
# `FunsExternal_Template.lean` full of `axiom` declarations. Accepting those would
# mean adding hand-written axioms to the trusted base on a miner's say-so, so this
# script rejects instead.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
# shellcheck source=config.sh
. "$root/verifier/config.sh"
src="${1:-$root/slot/src/parse.rs}"

for tool in "$CHARON_DIR/charon" "$AENEAS_WORK/aeneas"; do
    [ -x "$tool" ] || { echo "missing $tool -- run \`just init\`" >&2; exit 2; }
done

cd "$root/slot"
PATH="$CHARON_DIR:$PATH" charon rustc --preset=aeneas \
    --dest-file "$root/lean/slot.llbc" \
    -- --crate-name=slot --crate-type=lib --edition=2021 "$src" 2>&1 \
    | grep -v "cargo miri setup\|rustup component add" || true

rm -rf "$root/lean/.extract" && mkdir -p "$root/lean/.extract"
cd "$AENEAS_WORK"
./aeneas -backend lean -dest "$root/lean/.extract" -split-files -no-progress-bar \
    "$root/lean/slot.llbc" >/dev/null

cd "$root/lean"
if [ -f .extract/FunsExternal_Template.lean ]; then
    echo "REJECTED: the submission reaches outside Aeneas's model of core;" >&2
    echo "  it would need hand-written axioms, which the trusted base does not take." >&2
    grep -oE "^axiom [a-zA-Z_0-9.]+" .extract/FunsExternal_Template.lean >&2
    exit 1
fi
cp .extract/Types.lean Slot/Types.lean
cp .extract/Funs.lean  Slot/Funs.lean
echo "extracted: lean/Slot/Types.lean lean/Slot/Funs.lean"
