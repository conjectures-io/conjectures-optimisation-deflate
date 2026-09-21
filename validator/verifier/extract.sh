#!/usr/bin/env bash
# Translate the submitted Rust into Lean with charon and aeneas: verifier/extract.sh [path/to/parse.rs]
# The verifier runs this itself on every submission; an extraction that needs `axiom`s for foreign `core` items is rejected.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
# shellcheck source=config.sh
. "$root/verifier/config.sh"
src="${1:-$root/slot/generated/parse.rs}"
out="${2:?usage: extract.sh SOURCE OUTPUT_DIRECTORY}"
mkdir -p "$out"
mode="${3:-all}"

case "$mode" in
    compile) tools=("$CHARON_DIR/charon") ;;
    translate) tools=("$AENEAS_WORK/aeneas") ;;
    all) tools=("$CHARON_DIR/charon" "$AENEAS_WORK/aeneas") ;;
    *) echo "unknown extraction mode: $mode" >&2; exit 2 ;;
esac
for tool in "${tools[@]}"; do
    [ -x "$tool" ] || { echo "missing $tool -- run \`just init\`" >&2; exit 2; }
done

if [ "$mode" != "translate" ]; then
cd "$out"
# Truncate before compiling: a failed compiler must never reuse a prior model.
: > "$out/slot.llbc"
PATH="$CHARON_DIR:$PATH" charon rustc --preset=aeneas \
    --dest-file "$out/slot.llbc" \
    -- --out-dir /tmp -C debug-assertions=no -C overflow-checks=yes --crate-name=slot --crate-type=lib --edition=2021 "$src" 2>&1 || exit 1
[ -s "$out/slot.llbc" ] || { echo "missing Charon output" >&2; exit 1; }
fi
[ "$mode" != "compile" ] || exit 0

mkdir -p "$out/.extract"
find "$out/.extract" -mindepth 1 -delete
cd "$AENEAS_WORK"
./aeneas -backend lean -dest "$out/.extract" -split-files -no-progress-bar \
    "$out/slot.llbc" >/dev/null

cd "$out"
if find .extract -name "*External*" -print -quit | grep -q .; then
    echo "REJECTED: the submission reaches outside Aeneas's model of core;" >&2
    echo "  it would need hand-written axioms, which the trusted base does not take." >&2
    grep -h -oE "^axiom [a-zA-Z_0-9.]+" .extract/*External* >&2 || true
    exit 1
fi
test -s .extract/Types.lean && test -s .extract/Funs.lean
mkdir -p Slot
cp .extract/Types.lean Slot/Types.lean
cp .extract/Funs.lean  Slot/Funs.lean
echo "extracted: lean/Slot/Types.lean lean/Slot/Funs.lean"
