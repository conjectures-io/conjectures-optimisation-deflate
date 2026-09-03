# Toolchain

```bash
just init      # install everything, build, self-test
just doctor    # report what is present; install nothing; exit 1 if anything is missing
```

`just init` is idempotent — rerun it any time. On a bare machine it takes about
15 minutes and 9 GB, nearly all of it Mathlib's olean cache. On a machine that
already has a suitable toolchain it is a few seconds, because
[`../verifier/config.sh`](../verifier/config.sh) looks in the sibling
repositories before installing anything.

## What it installs, and where

| stage | what | where |
|---|---|---|
| 1 | elan and Lean **4.31.0** | `validator/.work/elan` |
| 2 | the Aeneas **`nightly-2026.08.27-5b9dcf3`** release — which ships `aeneas`, `charon` and `charon-driver` | `validator/.work/aeneas` |
| 3 | Rust **`nightly-2026-08-18`** with `rustc-dev`, `llvm-tools`, `rust-src` | rustup's own directory |
| 4 | the Aeneas Lean backend and **Mathlib** `fabf563a` | `validator/lean/.lake/packages` |
| 5 | builds the contract and both crates | |
| 6 | runs the reference submission through the proof gate | |

Everything is overridable:

```bash
AENEAS_WORK=/path/to/aeneas      # must contain `aeneas` and `charon`
ELAN_HOME=/path/to/.elan         # anything with `bin/lake`
LEAN_PACKAGES=/path/to/packages  # a Mathlib+Aeneas checkout to share
```

`LEAN_PACKAGES` is worth setting if another project on the machine already has
Mathlib at the same pin: `init` symlinks `lean/.lake/packages` at it instead of
downloading 7 GB again.

## Charon is not built from source

It used to be, and it took fifteen minutes, because Charon is a rustc driver and
compiles against rustc's internals.

It does not need to be. **The Aeneas release tarball ships a `charon` and
`charon-driver` built against that exact Aeneas** — which is the pairing that
matters, since Aeneas refuses LLBC produced by any other Charon. Checked: the
bundled pair and a `cargo install`ed Charon at the pinned revision produce a
**byte-identical** `lean/Slot/Funs.lean`.

What the bundled binaries still need is the nightly they were compiled against,
with `rustc-dev`, because `charon-driver` links rustc's own internals. That is
stage 3, and it is the only Rust component `init` adds beyond stable.

If you do need Charon from source — a pin bump before a release exists, say —
`just init --build-charon` does it, and `CHARON_DIR` picks up the
`cargo install` layout automatically.

## The pins

The four in `config.sh` are pinned **to each other**, not chosen independently:

```
AENEAS_TAG        nightly-2026.08.27-5b9dcf3
CHARON_REV        4ad295c1bf982b5533ce7d85f4ddc889ff3127f8   (charon-pin at that tag)
CHARON_TOOLCHAIN  nightly-2026-08-18                          (what that Charon compiles with)
LEAN_TOOLCHAIN    leanprover/lean4:v4.31.0                    (what that Aeneas backend needs)
```

`LEAN_TOOLCHAIN` must also match `lean/lean-toolchain`, which must match what
`lean/lake-manifest.json` pins Mathlib against. Stage 1 of `init` checks that
last one and says so if it drifts.

Bump all four together or none of them. If the release tarball's own
`rust-toolchain` disagrees with `CHARON_TOOLCHAIN`, **the release wins** — the
binaries were compiled against it — and `init` says so rather than silently
using the pin.

## Four traps

**1. `packagesDir` in a lakefile can delete your Mathlib.** Lake compares the
configured packages directory against the one recorded in `lake-manifest.json`.
When they disagree it warns *"packages directory changed"* and then **re-clones
into the configured location, deleting what is there**. Not hypothetical: it
destroyed a 7 GB shared Mathlib during development. `lean/lakefile.toml`
therefore has no `packagesDir` line, and `.lake/packages` is a symlink instead,
so both paths agree. If you ever see that warning, stop and fix it before
building.

**2. Aeneas's own Lean library contains `sorry`.** `Std/Slice.lean` and
`Std/StringIter.lean` both do, and the build prints `declaration uses 'sorry'`
every time. So **"it builds" is not the check** — a proof that reached a sorried
lemma would build cleanly. Stage 5 of the gate exists for exactly this, and it is
not optional.

**3. `lean --version` outside the project lies.** It reports elan's global
default, which is routinely a different Lean from the one `lean-toolchain`
selects. `init` reports the version resolved *inside* `lean/`.

**4. `charon rustc` prints a `cargo miri setup` warning.** Harmless — it falls
back to rustc's sysroot. `extract.sh` filters it so a real error is not lost in
it.

## Verifying

```bash
just doctor    # is everything present?
just smoke     # both reference submissions, end to end
```

Expected tail of `just smoke`:

```
score      1.00000x   no change — byte-identical to the incumbent.
score      0.85963x   ACCEPTED — 14.037% smaller than the incumbent.
```

Different *verdicts* mean something is wrong. Different byte counts mean the
corpus changed; see [`CORPUS.md`](CORPUS.md).

## What is in the trusted base

Worth being explicit, since the whole point is a proof.

* Lean's kernel, and `propext`, `Classical.choice`, `Quot.sound`.
* **Mathlib**, in whatever a submission's proof reaches.
* **Aeneas's Lean library**, including the two files with `sorry` in them. Stage 5
  proves a given submission does not depend on those, but they are in the
  dependency graph.
* **Charon and Aeneas themselves.** The extracted model is what the proof is
  about; if the translation is wrong, the proof is about the wrong program. This
  is the largest unaudited component and there is no way around it short of
  verifying the translator.
* **`harness/src/deflate.rs` and `token.rs`.** Not proved. The token encoding
  exists twice — once in Rust to run, once in Lean to reason about — and keeping
  them in step is an obligation on the operator. The correspondence is tabulated
  in `token.rs` and its arithmetic half is checked exhaustively by a test over
  every legal `(dist, len)`.

The differential round-trip check in stage 6 is the backstop for the last two: if
an accepted proof and two independent inflaters disagree, the bug is in the
contract or in the translation, and that is worth finding loudly.
