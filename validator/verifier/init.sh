#!/usr/bin/env bash
# Install everything needed to verify a submission, starting from nothing.
#
#   verifier/init.sh                 install what is missing, then self-test
#   verifier/init.sh --check         report what is present; install nothing
#   verifier/init.sh --force         reinstall even if present
#   verifier/init.sh --build-charon  build Charon from source instead of using
#                                    the one in the Aeneas release
#
# Six stages, each idempotent and each skipped when its output already exists.
# On a machine that already has a suitable toolchain -- `config.sh` looks in the
# sibling repositories -- most are no-ops.
#
# Budget on a bare machine: roughly 15 minutes and 9 GB. Nearly all of it is
# Mathlib's olean cache; the Rust nightly with `rustc-dev` is about 1.5 GB.
#
# Charon is NOT built from source. The Aeneas release tarball ships a `charon`
# and `charon-driver` built against that exact Aeneas, which is the pairing that
# matters -- Aeneas refuses LLBC from any other Charon. Checked: the bundled pair
# and a `cargo install`ed Charon at the pinned revision produce byte-identical
# `Slot/Funs.lean`. What the bundled binaries still need is the nightly they were
# compiled against, with `rustc-dev`, because `charon-driver` links rustc's own
# internals; stage 3 installs that and nothing else.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$root/.." && pwd)"
work="$root/.work"
CHECK=0 FORCE=0 BUILD_CHARON=0
for a in "$@"; do
    case "$a" in
        --check) CHECK=1 ;;
        --force) FORCE=1 ;;
        --build-charon) BUILD_CHARON=1 ;;
        -h|--help) sed -n '2,26p' "$0" | sed 's/^# \?//'; exit 0 ;;
        *) echo "unknown flag: $a (try --help)" >&2; exit 2 ;;
    esac
done
# shellcheck source=config.sh
. "$root/verifier/config.sh"

ok()   { printf '  \033[32m✓\033[0m %s\n' "$*"; }
miss() { printf '  \033[33m·\033[0m %s\n' "$*"; }
bad()  { printf '  \033[31m✗\033[0m %s\n' "$*"; }
step() { printf '\n\033[1m%s\033[0m\n' "$*"; }
missing=0

# In `--check` mode every stage reports and installs nothing. `--force` makes
# each presence test fail so the stage runs again.
present() { [ "$FORCE" = 1 ] && [ "$CHECK" = 0 ] && return 1; "$@"; }

# ---------------------------------------------------------------------------
step "1/6  Lean toolchain ($LEAN_TOOLCHAIN)"
if present test -x "$ELAN_HOME/bin/lake"; then
    ok "elan at $ELAN_HOME"
else
    miss "elan not found — installing into $work/elan"
    missing=1
    if [ "$CHECK" = 0 ]; then
        mkdir -p "$work"
        curl -sSfL https://elan.lean-lang.org/elan-init.sh -o "$work/elan-init.sh"
        ELAN_HOME="$work/elan" sh "$work/elan-init.sh" -y --no-modify-path \
            --default-toolchain "$LEAN_TOOLCHAIN" >/dev/null
        rm -f "$work/elan-init.sh"
        export ELAN_HOME="$work/elan"
        export PATH="$ELAN_HOME/bin:$PATH"
        ok "installed elan at $ELAN_HOME"
    fi
fi
if [ "$CHECK" = 0 ] && command -v elan >/dev/null; then
    elan toolchain install "$LEAN_TOOLCHAIN" >/dev/null 2>&1 || true
fi
# The version the PROJECT resolves, not elan's global default: they are routinely
# different and only the project's matters.
if command -v lean >/dev/null; then
    want="$(tr -d '[:space:]' < "$root/lean/lean-toolchain")"
    got="$(cd "$root/lean" && lean --version 2>/dev/null || true)"
    if [ -n "$got" ]; then
        ok "$got"
        case "$got" in
            *"${want##*:v}"*) ;;
            *) bad "lean/lean-toolchain wants $want — the above does not match"; missing=1 ;;
        esac
    fi
fi

# ---------------------------------------------------------------------------
step "2/6  Aeneas + Charon ($AENEAS_TAG release)"
if present test -x "$AENEAS_WORK/aeneas"; then
    ok "aeneas at $AENEAS_WORK/aeneas"
    if [ -x "$CHARON_DIR/charon" ]; then
        ok "charon at $CHARON_DIR/charon"
    else
        bad "aeneas is present but charon is not"
        missing=1
    fi
else
    miss "not found — fetching the $AENEAS_TAG release (~120 MB)"
    missing=1
    if [ "$CHECK" = 0 ]; then
        export AENEAS_WORK="$work/aeneas"
        mkdir -p "$AENEAS_WORK"
        url="https://github.com/AeneasVerif/aeneas/releases/download/$AENEAS_TAG/aeneas-linux-x86_64.tar.gz"
        curl -sSfL -o "$AENEAS_WORK/aeneas.tar.gz" "$url"
        tar xzf "$AENEAS_WORK/aeneas.tar.gz" -C "$AENEAS_WORK"
        rm -f "$AENEAS_WORK/aeneas.tar.gz"
        export CHARON_DIR="$AENEAS_WORK"
        ok "installed aeneas and charon at $AENEAS_WORK"
    fi
fi

# ---------------------------------------------------------------------------
step "3/6  Rust nightly for charon-driver ($CHARON_TOOLCHAIN + rustc-dev)"
# The release ships its own `rust-toolchain`; if it disagrees with our pin, the
# release wins, because the binaries were compiled against it.
if [ -f "$AENEAS_WORK/rust-toolchain" ]; then
    shipped=$(sed -n 's/^ *channel *= *"\(.*\)"/\1/p' "$AENEAS_WORK/rust-toolchain")
    if [ -n "$shipped" ] && [ "$shipped" != "$CHARON_TOOLCHAIN" ]; then
        miss "release ships $shipped, config pins $CHARON_TOOLCHAIN — using the release's"
        CHARON_TOOLCHAIN="$shipped"
    fi
fi
if present rustup toolchain list 2>/dev/null | grep -q "^$CHARON_TOOLCHAIN"; then
    ok "$CHARON_TOOLCHAIN installed"
else
    miss "not installed — adding it with rustc-dev, llvm-tools, rust-src (~1.5 GB)"
    missing=1
    if [ "$CHECK" = 0 ]; then
        if ! command -v rustup >/dev/null; then
            miss "rustup not found — installing it too"
            curl -sSfL https://sh.rustup.rs | sh -s -- -y --no-modify-path >/dev/null
            # shellcheck source=/dev/null
            . "$HOME/.cargo/env"
        fi
        rustup toolchain install "$CHARON_TOOLCHAIN" \
            --component rustc-dev,llvm-tools,rust-src --profile minimal
        ok "installed $CHARON_TOOLCHAIN"
    fi
fi
if [ "$BUILD_CHARON" = 1 ] && [ "$CHECK" = 0 ]; then
    miss "--build-charon: building Charon $CHARON_REV from source (~15 min)"
    cargo "+$CHARON_TOOLCHAIN" install --locked \
        --git https://github.com/AeneasVerif/charon --rev "$CHARON_REV" \
        --root "$AENEAS_WORK/charon" charon
    export CHARON_DIR="$AENEAS_WORK/charon/bin"
    ok "built charon at $CHARON_DIR/charon"
fi

# ---------------------------------------------------------------------------
step "4/6  Lean dependencies (Aeneas backend + Mathlib)"
if present test -e "$root/lean/.lake/packages"; then
    ok "lean/.lake/packages present"
elif [ -n "$LEAN_PACKAGES" ] && [ -d "$LEAN_PACKAGES/mathlib/.lake/build/lib/lean" ]; then
    miss "not linked yet — symlinking at $LEAN_PACKAGES"
    missing=1
    if [ "$CHECK" = 0 ]; then
        mkdir -p "$root/lean/.lake"
        # A symlink and not a `packagesDir =` line: see the note in lakefile.toml.
        ln -sfn "$LEAN_PACKAGES" "$root/lean/.lake/packages"
        ok "symlinked lean/.lake/packages -> $LEAN_PACKAGES"
    fi
else
    miss "no shared checkout — fetching our own (~7 GB, ~10 min)"
    missing=1
    if [ "$CHECK" = 0 ]; then
        cd "$root/lean"
        lake update
        (cd .lake/packages/mathlib && lake exe cache get) || true
        ok "fetched dependencies into lean/.lake/packages"
    fi
fi

# ---------------------------------------------------------------------------
step "5/6  Build"
if [ "$CHECK" = 1 ]; then
    present test -d "$root/lean/.lake/build/lib" \
        && ok "contract built" || { miss "contract not built"; missing=1; }
    present test -x "$root/harness/target/release/harness" \
        && ok "harness built" || { miss "harness not built"; missing=1; }
else
    (cd "$root/lean" && lake build Lz77) >/dev/null
    ok "contract (lean/Lz77)"
    (cd "$root/slot" && cargo build --release -q)
    (cd "$root/harness" && cargo build --release -q)
    ok "slot and harness crates"
fi

# ---------------------------------------------------------------------------
step "6/6  Self-test"
if [ "$CHECK" = 1 ]; then
    if [ "$missing" = 0 ]; then
        ok "everything present — run without --check to self-test"
        exit 0
    fi
    printf '\n\033[1mSomething is missing.\033[0m Run: just init\n'
    exit 1
fi
# The reference submission through the proof gate. If this passes, the toolchain
# is not merely installed, it agrees with itself.
python3 "$root/verifier/verify.py" "$repo/miner/template" --no-score

printf '\n\033[1minit ok.\033[0m Toolchain in use:\n'
printf '  AENEAS_WORK    %s\n' "$AENEAS_WORK"
printf '  CHARON_DIR     %s\n' "$CHARON_DIR"
printf '  ELAN_HOME      %s\n' "$ELAN_HOME"
printf '  LEAN_PACKAGES  %s\n' "${LEAN_PACKAGES:-(own checkout under lean/.lake)}"
printf '\nNext:  just smoke\n'
