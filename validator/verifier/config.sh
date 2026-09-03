#!/usr/bin/env bash
# Where the toolchain lives. Every path here can be overridden from the
# environment; the defaults are what this machine happens to have.
#
# Source this, do not run it.

# Charon and Aeneas binaries. Built by `../conjectures-rust/scripts/extract.sh`.
# Must contain `charon/bin/charon` and `aeneas`.
: "${AENEAS_WORK:=/home/robert/repos/s66_repositories/conjectures-rust/.work/aeneas}"

# elan/lake/lean. Anything with a `bin/lake` will do.
: "${ELAN_HOME:=/home/robert/repos/s66_repositories/conjectures-validator/.elan}"
if [ ! -x "$ELAN_HOME/bin/lake" ] && [ -x "$HOME/.elan/bin/lake" ]; then
    ELAN_HOME="$HOME/.elan"
fi

# An existing Mathlib + Aeneas checkout to share instead of fetching our own.
# `just setup` symlinks `lean/.lake/packages` at this when it is set and exists.
# Mathlib's olean cache is ~7 GB, so sharing one copy across repositories is
# worth the coupling.
: "${LEAN_PACKAGES:=/home/robert/repos/s66_repositories/conjectures-research/probes/aeneas-reach/.lake/packages}"

export AENEAS_WORK ELAN_HOME LEAN_PACKAGES
export PATH="$ELAN_HOME/bin:$PATH"
