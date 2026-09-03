# Making a submission

A submission is **two files in a directory**:

```
my-submission/
  parse.rs      your LZ77 parser
  Parse.lean    your proof that it satisfies the published contract
```

Nothing else is read. Not an extraction, not a build script, not a statement of
what you proved — the validator regenerates or supplies all of those itself.

---

## Step 1 — get the toolchain

One command, from nothing:

```bash
just init      # Lean 4.31.0, Mathlib, Aeneas, Charon, then build and self-test
```

About 15 minutes and 9 GB on a bare machine; seconds if you already have a Lean
and Mathlib at the same pins, which `init` will find and reuse rather than
download again. `just doctor` reports what is present without installing
anything, and
[`../validator/docs/TOOLCHAIN.md`](../validator/docs/TOOLCHAIN.md) has the pins
and the traps.

Check it works before writing anything:

```bash
just check miner/template
```

That should end in `no change — byte-identical to the incumbent`, because the
template *is* the incumbent. If it does not, fix your setup first — you do not
want to be debugging the toolchain and a proof at the same time.

## Step 2 — start from the template

```bash
cp -r miner/template my-submission
```

`miner/template/parse.rs` is a working, provable, greedy parser with a
single-slot hash table. `miner/template/Parse.lean` is its complete proof, 204
lines. Both pass the gate today. Your job is to make the parser better without
making the proof much longer.

Read [`CONTRACT.md`](CONTRACT.md) next. The single most important thing in it is
what you **do not** have to prove.

## Step 3 — improve the parser, and check the ratio first

```bash
just score my-submission     # ratio only. No proof. Seconds.
```

This compiles `parse.rs`, runs it over the corpus, checks the round trip against
two independent inflaters, and prints the score. It does **not** run the proof
gate. Iterate here until the ratio is worth having.

**Do this before touching Lean.** An idea that does not win on ratio is not worth
proving, and finding that out costs seconds instead of an afternoon.

Obey [`RULES.md`](RULES.md) while you do it — six rules, each with the rejected
and the accepted form. The validator enforces them in its first stage, and it is
much cheaper to follow them from the start than to restructure a finished parser.

## Step 4 — make it extract

```bash
just extract my-submission
```

Charon and Aeneas turn your `parse.rs` into Lean. If this fails, the message
usually points at a construct outside the translated subset; `RULES.md` covers
the ones seen so far. A submission that needs hand-written axioms is rejected —
the trusted base does not grow on a miner's say-so.

Look at `validator/lean/Slot/Funs.lean` afterwards. It is what your proof will be
about, and reading it once is the fastest way to understand what the proof has to
say.

## Step 5 — write the proof

```bash
just prove my-submission     # build the Lean side
just check my-submission --no-score
```

You must prove one theorem:

```lean
theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄
```

in `namespace Submission`. The validator applies it to the operator's statement:

```lean
theorem accepted : LZ77.Obligation slot.parse :=
  fun input out h => Submission.parse_spec input out h
```

so a weakened statement is a compile error rather than something a human has to
notice. Everything *else* in your `Parse.lean` is yours — restructure it freely.

If your change is confined to how matches are found, the diff will be small.
[`examples/hash-chains/NOTES.md`](examples/hash-chains/NOTES.md) walks through a
real one: 14% better ratio, 32 more proof lines, and exactly one lemma rewritten.

## Step 6 — submit

```bash
just check my-submission     # the full gate, then the score
```

All six stages must pass:

```
0 intake      ok — my-submission: parse.rs, Parse.lean
1 policy      ok — the submitted Rust is inside the subset
2 pins        ok — 23 contract and harness files unchanged
3 extract     ok — charon+aeneas re-run by the verifier, no new axioms
4 statement   ok — `LZ77.Obligation slot.parse` typechecks
5 axioms      ok — ['Classical.choice', 'Quot.sound', 'propext']
6 score       ACCEPTED — 14.037% smaller than the incumbent
```

Then send the directory. Note that a public pull request cannot carry a scored
submission: it publishes your proof before it is scored, and anyone can resubmit
it as their own.

---

## Two things people get wrong

**Proving before measuring.** The proof is the expensive half. Establish the ratio
win first with `just score`, then pay for it.

**Assuming the search must be proved correct.** It must not. Your candidate search
can be wrong, cyclic, or adversarial and the proof does not care — what is
load-bearing is only that the bytes were compared before a match was emitted.
`CONTRACT.md` says exactly where that line falls, and staying on the right side of
it is the difference between a 30-line diff and a rewrite.

## What it costs, measured

| | `parse.rs` | `Parse.lean` |
|---|---|---|
| `template/` — greedy, hash head | 66 | 204 |
| `examples/hash-chains/` — 16-deep chains | 90 | 236 |

For comparison, a sorted-permutation proof about an extracted radix sort — a much
smaller function — cost 449 lines. The difference is not tactics; it is that this
contract was designed so that the obligation on a submission reduces to
`∀ k < len, input[pos-dist+k] = input[pos+k]`, which is exactly what a
match-length loop already computes.
