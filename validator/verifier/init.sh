#!/usr/bin/env bash
# Install everything needed to verify a submission, starting from nothing; idempotent, every download sha256-pinned in config.sh.
#   verifier/init.sh                 install what is missing, then self-test (~15 min and 9 GB bare, seconds warm)
#   verifier/init.sh --check         report what is present; install nothing
#   verifier/init.sh --force         reinstall even if present
#   verifier/init.sh --build-charon  build Charon from source instead of the one in the Aeneas release
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$root/.." && pwd)"
PYTHON="${PYTHON:-$repo/.venv/bin/python}"
[ -x "$PYTHON" ] || PYTHON=python3
work="$root/.work"
CHECK=0 FORCE=0 BUILD_CHARON=0
for a in "$@"; do
    case "$a" in
        --check) CHECK=1 ;;
        --force) FORCE=1 ;;
        --build-charon) BUILD_CHARON=1 ;;
        -h|--help) sed -n '2,6p' "$0" | sed 's/^# \?//'; exit 0 ;;
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

# `--check` installs nothing; `--force` makes every presence test fail so the stage reruns.
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
        fetch_pinned "$ELAN_URL" "$work/elan.tar.gz" "$ELAN_SHA256" || exit 2
        tar xzf "$work/elan.tar.gz" -C "$work" elan-init
        ELAN_HOME="$work/elan" "$work/elan-init" -y --no-modify-path \
            --default-toolchain "$LEAN_TOOLCHAIN" >/dev/null
        rm -f "$work/elan.tar.gz" "$work/elan-init"
        export ELAN_HOME="$work/elan"
        export PATH="$ELAN_HOME/bin:$PATH"
        ok "installed elan at $ELAN_HOME"
    fi
fi
if [ "$CHECK" = 0 ] && command -v elan >/dev/null; then
    elan toolchain install "$LEAN_TOOLCHAIN" >/dev/null 2>&1 || true
fi
# The version the project resolves, not elan's global default.
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
        fetch_pinned "$AENEAS_URL" "$AENEAS_WORK/aeneas.tar.gz" "$AENEAS_SHA256" || exit 2
        tar xzf "$AENEAS_WORK/aeneas.tar.gz" -C "$AENEAS_WORK"
        rm -f "$AENEAS_WORK/aeneas.tar.gz"
        export CHARON_DIR="$AENEAS_WORK"
        ok "installed aeneas and charon at $AENEAS_WORK"
    fi
fi

# ---------------------------------------------------------------------------
step "3/6  Rust nightly for charon-driver ($CHARON_TOOLCHAIN + rustc-dev)"
# If the release's own rust-toolchain disagrees with the pin, the release wins: the binaries were built with it.
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
            miss "rustup not found — installing $RUSTUP_VERSION"
            fetch_pinned "$RUSTUP_URL" "$work/rustup-init" "$RUSTUP_SHA256" || exit 2
            chmod +x "$work/rustup-init"
            "$work/rustup-init" -y --no-modify-path >/dev/null
            rm -f "$work/rustup-init"
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
    present test -x "$root/precheck/target/release/submission-precheck" \
        && ok "syntax checker built" || { miss "syntax checker not built"; missing=1; }
    present test -x "$root/measure/target/release/measure" \
        && ok "engine built" || { miss "measurement engine not built"; missing=1; }
else
    (cd "$root/lean" && lake build Lz77) >/dev/null
    ok "contract (lean/Lz77)"
    (cd "$root/precheck" && cargo build --release --locked -q)
    # The standalone slot uses a trusted template; verification has private inputs.
    mkdir -p "$root/slot/generated"
    cp "$repo/miner/template/parse.rs" "$root/slot/generated/parse.rs"
    (cd "$root/slot" && cargo build --release -q)
    (cd "$root/measure" && cargo build --release -q)
    ok "slot and measure crates"
fi

# Things init does not install: a C linker for the engine's zlib and libdeflate,
# the proof sandbox (needs root), and the service's Python deps. Report, do not guess.
if command -v cc >/dev/null || [ -n "${CC:-}" ]; then
    ok "C compiler for the engine (${CC:-cc})"
else
    bad "no C compiler — ./setup.sh installs build-essential, or set CC"
    missing=1
fi
if "$PYTHON" -c "import loguru, fastapi, bittensor_wallet, pytest" 2>/dev/null; then
    ok "python deps in $PYTHON"
else
    bad "python deps missing — run ./setup.sh (creates .venv via uv sync from pyproject.toml)"
    missing=1
fi
if command -v bwrap >/dev/null; then
    ok "bubblewrap for the proof sandbox"
elif [ "${VERIFY_SANDBOX:-bwrap}" = off ]; then
    miss "bubblewrap absent; VERIFY_SANDBOX=off so the proof runs unconfined"
else
    bad "bubblewrap not found — \`sudo apt install bubblewrap\` (or VERIFY_SANDBOX=off on a miner's machine)"
    missing=1
fi
if command -v systemd-run >/dev/null; then
    ok "systemd-run for the memory cap"
else
    miss "systemd-run not found — the proof will run without a memory cap"
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
# The reference submission through the proof gate: the toolchain agrees with itself.
"$PYTHON" "$root/verifier/verify.py" "$repo/miner/template" --no-score

printf '\n\033[1minit ok.\033[0m Toolchain in use:\n'
printf '  AENEAS_WORK    %s\n' "$AENEAS_WORK"
printf '  CHARON_DIR     %s\n' "$CHARON_DIR"
printf '  ELAN_HOME      %s\n' "$ELAN_HOME"
printf '  LEAN_PACKAGES  %s\n' "${LEAN_PACKAGES:-(own checkout under lean/.lake)}"
printf '\nNext:  just smoke\n'
