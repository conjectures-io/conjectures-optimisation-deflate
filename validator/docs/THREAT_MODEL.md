# Threat model

What each stage of the gate stops, and how it was checked.

The adversary is a miner who wants their submission accepted and ranked highly
without doing the work. They control exactly two files, `parse.rs` and
`Parse.lean`, and nothing else. Everything below is about what they could try with
those two files.

---

## Stage 0 — intake

**Attack:** smuggle a third file — a modified contract, a pre-baked extraction, a
build script, a 200 MB `Parse.lean` that exhausts the validator.

**Defence:** exactly `parse.rs` and `Parse.lean` are copied in. Any other `.rs` or
`.lean` in the directory is a rejection rather than a silent ignore, because a
miner who thinks they submitted three files should be told. Both files are size
capped at 512 KB before anything is run.

## Stage 1 — policy

**Attack:** `unsafe` to defeat the model; SIMD; a construct Aeneas mistranslates;
`use crate::` to reach code outside the slot; `include_bytes!` to smuggle a
precomputed table of the corpus.

**Defence:** 11 regexes over the submitted Rust, comments stripped first so a rule
*named* in a doc comment is not a violation. Documented with rejected/accepted
pairs in [`../../miner/RULES.md`](../../miner/RULES.md), because a miner who
discovers a rule by failing is a miner who leaves.

**Checked:** inserting `'outer: while` produces
`line ~90: "'outer: while" — labelled loops`.

**Limitation, stated plainly:** a regex scanner is a coarse instrument. It is a
usability feature first — it fails fast with a good message — and a security
control second. The real defence against a construct outside the subset is that
stage 3 will not translate it, or stage 4 will not prove it.

## Stage 2 — pins

**Attack:** edit the contract you are judged against. Weaken `LZ77.Valid`, add a
lemma that makes the obligation trivial, change the DEFLATE encoder so your
tokens code better, change the baseline so you beat it.

**Defence:** SHA-256 of 23 files — the whole contract, the gate, the harness, the
verifier itself — compared before anything is built.

**Note:** stage 2 protects a validator running the gate in a working tree. It is
not what protects a *distributed* competition, where the answer is that each
validator has its own checkout and only the two submission files travel.

## Stage 3 — extract

**Attack:** supply an extraction that does not correspond to the submitted Rust —
a Lean model of a program you did not write, which your proof then discharges
easily.

**Defence:** **the verifier runs Charon and Aeneas itself.** An extraction that
arrives inside a submission is a claim about a program made by the person whose
program it is, and is worth nothing. `lean/Slot/` is overwritten every run.

**Also:** a submission that reaches outside Aeneas's model of `core` produces a
`FunsExternal_Template.lean` of `axiom` declarations. Accepting those would grow
the trusted base on a miner's say-so, so it is a rejection.

## Stage 4 — statement

**Attack:** prove something weaker and call it `parse_spec`. Quantify over fewer
inputs. Drop the length precondition. Replace `Valid` with `True`. Prove a lemma
about a different function.

**Defence:** the verifier — not the miner — writes

```lean
theorem accepted : LZ77.Obligation slot.parse :=
  fun input out h => Submission.parse_spec input out h
```

into a file the submission never sees. `LZ77.Obligation` is the operator's
statement, pinned by stage 2. If the miner's theorem is weaker, this does not
typecheck.

This is the predecessor's "statement check" done as a **type check** rather than a
string comparison, and that is the only version of it that cannot be gamed. There
is nothing to read carefully and nothing to compare as text.

**Checked:** substituting a proof of `⦃ fun _ => True ⦄` gives

```
Type mismatch: weak input out h has type
  slot.parse input out ⦃ x => True ⦄
but is expected to have type
  slot.parse input out ⦃ r => ↑r.1 ≤ input.length ∧ r.2.length = out.length ∧
                              LZ77.Valid (LZ77.bytes input) (LZ77.toks r.2 ↑r.1) ⦄
```

## Stage 5 — axioms

**Attack:** `sorry`. Or a custom `axiom`. Or reach a Mathlib lemma that is itself
sorried.

**Defence:** `#print axioms accepted`, and anything beyond `propext`,
`Classical.choice` and `Quot.sound` is a rejection.

**This is not belt-and-braces.** Aeneas's own Lean library contains `sorry` in
`Std/Slice.lean` and `Std/StringIter.lean`. A proof that reached one of those
would **build cleanly**. Build success is not the check; this is.

## Stage 6 — score

**Attack:** win by being slow (unbounded search for a fraction of a percent);
produce a stream that scores well but does not decode; overfit to a corpus you
have seen.

**Defence:** the speed floor; the differential round-trip check against two
independent inflaters; and corpus governance —
[`SCORING.md`](SCORING.md) covers all three.

---

## Ordering

**Nothing is compiled for speed and nothing is timed until the proof has been
accepted.** A submission cannot buy validator time with a program that has no
proof: policy is a regex, pins are hashes, and both run before Charon.

## What this does not defend against

Stated because a threat model that only lists wins is not one.

* **A bug in Charon or Aeneas.** The extracted model is what the proof is about.
  If the translation is wrong, the proof is about the wrong program. This is the
  largest unaudited component in the trusted base and there is no way around it
  short of verifying the translator. The differential round-trip check is the
  backstop, and it is empirical.
* **A bug in the contract.** If `LZ77.decode` does not mean what RFC 1951 means,
  a correct proof accepts a wrong compressor. Same backstop, same limitation.
* **The token encoding existing twice.** `harness/src/token.rs` and `LZ77.emit`
  are the same function written twice, once to run and once to reason about.
  Keeping them in step is an operator obligation, not a proved fact. The
  correspondence is tabulated in `token.rs`; the arithmetic half is checked
  exhaustively over every legal `(dist, len)`; the structural half is not.
* **Resource exhaustion inside Lean.** A submission's `Parse.lean` is 512 KB of
  arbitrary tactic script and could take a very long time to elaborate. There is
  no timeout on stage 4 yet. It should have one.
* **Corpus overfitting across rounds**, if the corpus is not re-mixed.
* **Collusion and Sybil behaviour**, which are subnet-level concerns and not
  addressed here at all.
