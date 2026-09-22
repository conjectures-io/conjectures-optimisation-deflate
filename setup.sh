#!/usr/bin/env bash
# setup.sh - from a fresh clone to a passing self-test, in one idempotent run.
#   ./setup.sh                 apt packages, just, .venv, pins check, .env, corpus-stage1, Lean/Aeneas toolchain (~15 min, 9 GB), self-test
#   ./setup.sh --no-toolchain  everything except the toolchain (seconds)
#   ./setup.sh --chain         also install the bittensor SDK (validators only, large)
#   ./setup.sh --check         report what is present; install nothing
# Then `just check miner/template`; miners without root set VERIFY_SANDBOX=off in .env.
set -euo pipefail

root="$(cd "$(dirname "$0")" && pwd)"
CHECK=0 TOOLCHAIN=1 CHAIN=0
for a in "$@"; do
    case "$a" in
        --check) CHECK=1 ;;
        --no-toolchain) TOOLCHAIN=0 ;;
        --chain) CHAIN=1 ;;
        -h|--help) sed -n '2,7p' "$0" | sed 's/^# \?//'; exit 0 ;;
        *) echo "unknown flag: $a (try --help)" >&2; exit 2 ;;
    esac
done

JUST_VERSION="1.58.0"
JUST_SHA256="4a5cc2f53e6f0f8c59092a6cc38291eb729d46a7dd95d3ae582008881b84931d"
JUST_URL="https://github.com/casey/just/releases/download/${JUST_VERSION}/just-${JUST_VERSION}-x86_64-unknown-linux-musl.tar.gz"
UV_VERSION="0.12.15"
UV_SHA256="f97935763c04be3e692460a7aaeaaab8fc3b78fcf8b389da820b38ae7423a638"
UV_URL="https://github.com/astral-sh/uv/releases/download/${UV_VERSION}/uv-x86_64-unknown-linux-gnu.tar.gz"
APT_PKGS="build-essential bubblewrap curl python3 git"

ok()   { printf '  \033[32m✓\033[0m %s\n' "$*"; }
miss() { printf '  \033[33m·\033[0m %s\n' "$*"; }
bad()  { printf '  \033[31m✗\033[0m %s\n' "$*"; }
step() { printf '\n\033[1m%s\033[0m\n' "$*"; }
missing=0

# True when `$1 --version` reports at least $2. A pinned tool that is merely present
# is not enough: apt ships just 1.21, which refuses a variadic parameter after a
# defaulted one and so rejects this repo's justfile outright -- every recipe with it.
# Checking presence alone reported "ok" while the pin went uninstalled.
at_least() {
    local got
    got="$("$1" --version 2>/dev/null | tr -cd '0-9.\n ' | tr ' ' '\n' | grep -m1 '[0-9]\.')" || return 1
    [ -n "$got" ] || return 1
    [ "$(printf '%s\n%s\n' "$2" "$got" | sort -V | head -1)" = "$2" ]
}

# Warn when an older copy of $1 still wins on PATH after we installed the pinned one.
shadowed() {
    local resolved
    resolved="$(command -v "$1" 2>/dev/null || true)"
    [ "$resolved" != "$HOME/.local/bin/$1" ] && [ -n "$resolved" ]
}

# ---------------------------------------------------------------------------
step "1/9  System packages"
need=()
{ command -v cc >/dev/null || [ -n "${CC:-}" ]; } || need+=(build-essential)
command -v curl    >/dev/null || need+=(curl)
command -v python3 >/dev/null || need+=(python3)
command -v git     >/dev/null || need+=(git)
command -v bwrap   >/dev/null || need+=(bubblewrap)
if [ ${#need[@]} -eq 0 ]; then
    ok "cc, curl, python3, git, bubblewrap present"
elif [ "$CHECK" = 1 ]; then
    bad "missing: ${need[*]}"; missing=1
elif [ "$(id -u)" = 0 ] || sudo -n true 2>/dev/null; then
    miss "installing: ${need[*]}"
    sudo_cmd=""; [ "$(id -u)" = 0 ] || sudo_cmd="sudo"
    $sudo_cmd apt-get -qq update >/dev/null
    DEBIAN_FRONTEND=noninteractive $sudo_cmd apt-get -qq install -y --no-install-recommends "${need[@]}" >/dev/null
    ok "installed ${need[*]}"
else
    bad "missing: ${need[*]} - run:  sudo apt-get install -y $APT_PKGS"
    # bubblewrap alone is optional for a miner (VERIFY_SANDBOX=off); anything else blocks the build.
    if [ "${need[*]}" != "bubblewrap" ]; then exit 2; fi
    miss "continuing without the sandbox; set VERIFY_SANDBOX=off in .env"
fi

# ---------------------------------------------------------------------------
step "2/9  just ($JUST_VERSION)"
if command -v just >/dev/null && at_least just "$JUST_VERSION"; then
    ok "just $(just --version | awk '{print $2}') at $(command -v just)"
elif [ "$CHECK" = 1 ]; then
    if command -v just >/dev/null; then
        bad "just $(just --version | awk '{print $2}') at $(command -v just) is older than $JUST_VERSION"
    else
        bad "just not found"
    fi
    missing=1
else
    miss "installing into ~/.local/bin"
    tmp="$(mktemp -d)"
    curl -sSfL -o "$tmp/just.tgz" "$JUST_URL"
    echo "$JUST_SHA256  $tmp/just.tgz" | sha256sum -c - >/dev/null
    tar xzf "$tmp/just.tgz" -C "$tmp" just
    mkdir -p "$HOME/.local/bin" && install -m755 "$tmp/just" "$HOME/.local/bin/just" && rm -rf "$tmp"
    export PATH="$HOME/.local/bin:$PATH"
    ok "installed ~/.local/bin/just"
    case ":$PATH:" in *":$HOME/.local/bin:"*) ;; *) miss "add ~/.local/bin to your PATH" ;; esac
    if shadowed just; then
        bad "$(command -v just) still comes first on PATH; put ~/.local/bin ahead of it"
        missing=1
    fi
fi

# ---------------------------------------------------------------------------
step "3/9  uv ($UV_VERSION)"
if command -v uv >/dev/null && at_least uv "$UV_VERSION"; then
    ok "uv $(uv --version | awk '{print $2}') at $(command -v uv)"
elif [ "$CHECK" = 1 ]; then
    if command -v uv >/dev/null; then
        bad "uv $(uv --version | awk '{print $2}') at $(command -v uv) is older than $UV_VERSION"
    else
        bad "uv not found"
    fi
    missing=1
else
    miss "installing into ~/.local/bin"
    tmp="$(mktemp -d)"
    curl -sSfL -o "$tmp/uv.tgz" "$UV_URL"
    echo "$UV_SHA256  $tmp/uv.tgz" | sha256sum -c - >/dev/null
    tar xzf "$tmp/uv.tgz" -C "$tmp" --strip-components=1
    mkdir -p "$HOME/.local/bin" && install -m755 "$tmp/uv" "$HOME/.local/bin/uv" && rm -rf "$tmp"
    export PATH="$HOME/.local/bin:$PATH"
    ok "installed ~/.local/bin/uv"
    case ":$PATH:" in *":$HOME/.local/bin:"*) ;; *) miss "add ~/.local/bin to your PATH" ;; esac
    if shadowed uv; then
        bad "$(command -v uv) still comes first on PATH; put ~/.local/bin ahead of it"
        missing=1
    fi
fi

# ---------------------------------------------------------------------------
step "4/9  Python environment (.venv, from pyproject.toml)"
py="$root/.venv/bin/python"
core_imports="fastapi, bittensor_wallet, pytest, ruff, basedpyright, loguru, sqlalchemy, psycopg, alembic, pydantic_settings"
if [ -x "$py" ] && "$py" -c "import ${core_imports}" 2>/dev/null; then
    ok ".venv complete"
elif [ "$CHECK" = 1 ]; then
    bad ".venv missing or incomplete"; missing=1
else
    miss "syncing .venv from pyproject.toml"
    (cd "$root" && uv sync --group dev -q)
    ok ".venv ready"
fi

# The bittensor SDK is large and only the chain watcher and weight setter need it, so a
# miner running `just check` never pays for it. Validators pass --chain.
if [ -x "$py" ] && "$py" -c "import bittensor" 2>/dev/null; then
    ok "bittensor SDK present (chain workers available)"
elif [ "$CHAIN" = 1 ] && [ "$CHECK" = 0 ]; then
    miss "installing the bittensor SDK (the 'chain' dependency group)"
    (cd "$root" && uv sync --group dev --group chain -q)
    ok "bittensor SDK ready"
else
    miss "bittensor SDK absent - miners do not need it; validators run ./setup.sh --chain"
fi

# ---------------------------------------------------------------------------
# Before the ~15 min toolchain install: fail now if the checkout of the engine,
# spec or gate itself has drifted from PINS.json, not on the first submission.
step "5/9  Pins (contract, engine and gate unchanged)"
if [ -x "$py" ]; then
    pins_out="$(mktemp)"
    if "$py" "$root/validator/verifier/pins.py" --check >"$pins_out" 2>&1; then
        ok "PINS.json matches the checkout"
    else
        bad "pins drifted:"; sed 's/^/    /' "$pins_out"
        missing=1
        [ "$CHECK" = 1 ] || { rm -f "$pins_out"; exit 2; }
    fi
    rm -f "$pins_out"
else
    miss ".venv missing — cannot check pins yet"
    missing=1
fi

# ---------------------------------------------------------------------------
step "6/9  Configuration (.env)"
if [ -f "$root/.env" ]; then
    ok ".env present"
elif [ "$CHECK" = 1 ]; then
    miss ".env absent (defaults apply)"
else
    cp "$root/.env.example" "$root/.env"
    ok "created .env from .env.example - edit it for a validator"
fi

# ---------------------------------------------------------------------------
# The default corpus (validator/corpora.toml) is corpus-stage1, fetched from its own
# public repository rather than committed here. Stage 2 is private and best-effort --
# pull-corpus.sh already skips it with a note, not an error, when it is unreachable.
step "7/9  Scoring corpus (corpus-stage1, the benchmark default)"
if [ -d "$root/data/benchmark/corpus-stage1" ] && [ -n "$(ls -A "$root/data/benchmark/corpus-stage1" 2>/dev/null)" ]; then
    ok "data/benchmark/corpus-stage1 present"
elif [ "$CHECK" = 1 ]; then
    miss "data/benchmark/corpus-stage1 absent - run: just corpus-pull"
else
    miss "fetching corpus-stage1 (and corpus-stage2, if reachable)"
    if (cd "$root" && just corpus-pull); then
        ok "data/benchmark/corpus-stage1 ready"
    else
        bad "corpus-pull failed - re-run \`just corpus-pull\` once it's reachable"
        missing=1
    fi
fi

# ---------------------------------------------------------------------------
if command -v cargo >/dev/null 2>&1; then
    if [ "$CHECK" = 0 ]; then
        cargo build --release --locked --manifest-path "$root/validator/precheck/Cargo.toml" || exit 2
    elif [ ! -x "$root/validator/precheck/target/release/submission-precheck" ]; then
        miss "syntax checker missing; run ./setup.sh"
        missing=1
    fi
else
    miss "cargo missing; install Rust to build the syntax checker"
fi

step "8/9  Slot (validator/slot/src/parse.rs is a symlink to generated/, gitignored)"
if [ -s "$root/validator/slot/generated/parse.rs" ]; then
    ok "validator/slot/generated/parse.rs present"
elif [ "$CHECK" = 1 ]; then
    miss "validator/slot/generated/parse.rs absent"
else
    mkdir -p "$root/validator/slot/generated"
    cp "$root/miner/template/parse.rs" "$root/validator/slot/generated/parse.rs"
    ok "seeded validator/slot/generated/parse.rs from miner/template"
fi

# ---------------------------------------------------------------------------
step "9/9  Toolchain: Lean, Aeneas, Charon, Mathlib"
export PYTHON="$py" PATH="$HOME/.local/bin:$PATH"
if [ "$TOOLCHAIN" = 0 ] && [ "$CHECK" = 0 ]; then
    miss "skipped (--no-toolchain); run ./setup.sh later for the gate"
elif [ "$CHECK" = 1 ]; then
    "$root/validator/verifier/init.sh" --check || missing=1
else
    "$root/validator/verifier/init.sh"
fi

if [ "$CHECK" = 1 ]; then
    [ "$missing" = 0 ] && { printf '\n\033[1mready.\033[0m\n'; exit 0; }
    printf '\n\033[1mRun: ./setup.sh\033[0m\n'; exit 1
fi
printf '\n\033[1msetup done.\033[0m  Next:  just check miner/template     just --list\n'
