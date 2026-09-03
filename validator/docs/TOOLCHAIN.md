# Toolchain

Three things have to be present, and only the first is unusual.

| | version | why it is pinned |
|---|---|---|
| Lean | **4.31.0** | Aeneas's Lean backend requires it |
| Mathlib | rev `fabf563a` | pinned by `lean/lake-manifest.json` |
| Aeneas | `nightly-2026.08.27-5b9dcf3` | pinned by `lean/lakefile.toml` |
| Charon | built against that Aeneas | **the pair drifts; see below** |
| Rust | any recent stable | plus a nightly for Charon's driver |

Everything is configured in [`../verifier/config.sh`](../verifier/config.sh), and
every path there can be overridden from the environment:

```bash
AENEAS_WORK=/path/to/aeneas     # must contain charon/bin/charon and aeneas
ELAN_HOME=/path/to/.elan        # anything with bin/lake
LEAN_PACKAGES=/path/to/packages # an existing Mathlib+Aeneas checkout to share
```

## Setup

```bash
just setup
```

If `LEAN_PACKAGES` names a checkout at the same pins, `lean/.lake/packages` is
symlinked at it and nothing is downloaded. Otherwise lake fetches its own and
`lake exe cache get` pulls Mathlib's prebuilt oleans — which takes a while but is
far better than building Mathlib.

Charon and Aeneas are **not** installed by `just setup`; they are built from
source by `../../conjectures-rust/scripts/extract.sh` in the sibling repository.
Point `AENEAS_WORK` at the result.

## Four traps

**1. `packagesDir` in a lakefile can delete your Mathlib.** Lake compares the
configured packages directory against the one recorded in `lake-manifest.json`.
When they disagree it warns *"packages directory changed"* and then **re-clones
into the configured location, deleting what is there**. That is not hypothetical:
it destroyed a 7 GB shared Mathlib during development. `lean/lakefile.toml`
therefore has no `packagesDir` line, and `.lake/packages` is a symlink instead, so
both paths agree.

If you ever see that warning, stop and fix it before building.

**2. Aeneas's own Lean library contains `sorry`.** `Std/Slice.lean` and
`Std/StringIter.lean` both do, and the build prints
`declaration uses 'sorry'` every time. So **"it builds" is not the check** — a
proof that reached a sorried lemma would build cleanly. Stage 5 of the gate exists
for exactly this, and it is not optional.

**3. Charon and Aeneas drift as a pair.** Charon must be rebuilt against the
pinned Aeneas. A mismatched pair produces `.llbc` that Aeneas reads but translates
subtly differently, or not at all. Rebuild both together, never one.

**4. `charon rustc` prints a `cargo miri setup` warning.** Harmless — it falls
back to rustc's sysroot. `extract.sh` filters it out so a real error is not lost
in it.

## Verifying the toolchain

```bash
just smoke
```

Builds both crates and runs the two reference submissions end to end. The
expected tail:

```
score      1.00000x   no change — byte-identical to the incumbent.
score      0.85963x   ACCEPTED — 14.037% smaller than the incumbent.
```

Different corpus contents will move those numbers; different *verdicts* mean
something is wrong.

## What is in the trusted base

Worth being explicit, since the whole point is a proof.

* Lean's kernel, and `propext`, `Classical.choice`, `Quot.sound`.
* **Mathlib**, in whatever a submission's proof reaches.
* **Aeneas's Lean library**, including the two files with `sorry` in them. Stage 5
  proves a given submission does not depend on those, but they are in the
  dependency graph.
* **Charon and Aeneas themselves.** The extracted model is what the proof is
  about; if the translation is wrong, the proof is about the wrong program. This is
  the largest unaudited component and there is no way around it short of
  verifying the translator.
* **`harness/src/deflate.rs` and `token.rs`.** Not proved. The token encoding
  exists twice — once in Rust to run, once in Lean to reason about — and keeping
  them in step is an obligation on the operator. The correspondence is tabulated
  in `token.rs` and its arithmetic half is checked exhaustively by a test over
  every legal `(dist, len)`.

The differential round-trip check in stage 6 is the backstop for the last two:
if an accepted proof and two independent inflaters disagree, the bug is in the
contract or in the translation, and that is worth finding loudly.
