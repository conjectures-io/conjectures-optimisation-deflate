# What you must prove

## The token stream

Your `parse` reads `input` and writes tokens into `out`, returning how many it
wrote. A token is a `u32`:

| | |
|---|---|
| `t < 256` | emit the literal byte `t` |
| `t = 2^24 + (dist-1)*256 + (len-3)` | copy `len` bytes from `dist` back |

with `1 ≤ dist ≤ 32768` and `3 ≤ len ≤ 258`. Back-references may overlap: a copy
can read bytes this same copy has just written, which is how `dist < len` works.

The encoding is arithmetic rather than bit-packed on purpose. `Nat` `+`, `*`, `/`
and `%` are what `omega` reasons about; `&&&` and `<<<` are not, and you would pay
for the difference in every obligation.

## The obligation

`LZ77.Obligation` in `validator/lean/Lz77/Interface.lean`:

```lean
def Obligation
    (parse : Slice Std.U8 → Slice Std.U32 → Result (Std.Usize × Slice Std.U32)) : Prop :=
  ∀ (input : Slice Std.U8) (out : Slice Std.U32), input.length ≤ out.length →
    parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      Valid (bytes input) (toks r.2 r.1.val) ⦄
```

Four things, and it is worth being clear about how strong each one is.

**It never fails.** Living in `Result` and being proved `⦃ _ ⦄` means no
out-of-bounds index, no arithmetic overflow, no panic — on *every* input, not on
the ones you tested.

**It always terminates.** Every loop needs a measure that decreases. This is why
rule 4 in [`RULES.md`](RULES.md) exists: a chain walk must terminate on a counter,
not on the chain being acyclic, because nothing guarantees the chain is acyclic.

**It does not disturb the buffer.** `r.2.length = out.length`.

**The tokens decode back to the input.** `LZ77.Valid`, which is
`LZ77.decode toks = some input` — the LZ77 layer of RFC 1951 with the Huffman
coding stripped off, written out in `validator/lean/Lz77/Spec.lean`.

## What you do **not** have to prove

This is the part that decides how much work a submission is, so read it twice.

**Nothing about how you find matches.** Concretely, in both reference proofs:

```lean
-- The hash lands in range. That is all. What it computes is irrelevant:
-- a bad hash finds worse matches, it cannot find invalid ones.
theorem hash3_spec (a b c : Std.U8) :
    slot.hash3 a b c ⦃ fun h => h.val < 32768 ⦄

-- The loop that maintains the search structure. Postcondition: True.
-- It must terminate and stay in bounds. It need not be correct, because
-- correctness does not depend on it.
theorem parse_loop0_loop0_spec … ⦃ fun r => r.2.2 = true → … ⦄
```

**Nothing about the match being the best one.** `Found` — the predicate between
the search and the emission — says the reported `(distance, length)` is *in range
and its bytes were compared*. It does not say it is the longest match, or the
nearest, or that a better one does not exist. A worse parse scores worse; it is
never rejected.

**Nothing about your data structures being consistent.** The reference submission
stores positions as truncated `u32`s in a cyclic array. A truncated value can
point anywhere. That is harmless, and provably so, because `match_len` compares
the bytes before anything is emitted.

## Where the line falls

```
        your search                    │        the emission
   (anything at all)                   │   (this is what is proved)
                                       │
   hash / tree / automaton /  ────► Found ────►  token written
   optimal parse / table lookup        │         invariant stepped
                                       │
   proved: terminates, in bounds       │   proved: decodes back
```

```lean
def Found (input : Slice Std.U8) (n pos best_len best_dist : Std.Usize) : Prop :=
  best_len.val < 3 ∨
    (3 ≤ best_len.val ∧ best_len.val ≤ 258 ∧ pos.val + best_len.val ≤ n.val ∧
      1 ≤ best_dist.val ∧ best_dist.val ≤ 32768 ∧ best_dist.val ≤ pos.val ∧
      Matches input (pos.val - best_dist.val) pos.val best_len.val)
```

Either you found nothing, or you found something in range whose bytes agree.
`Matches` is the postcondition of a byte-comparison loop and nothing more.

**If your change is on the left of that line, you rewrite one lemma.** That is
what happened in [`examples/hash-chains`](examples/hash-chains/NOTES.md): the
entire diff to the proof was `find_match_spec`, a new lemma establishing `Found`
for a chain walk, plus the state-tuple bookkeeping that follows from adding an
array to `parse`.

## The lemmas the contract gives you

You will use exactly two, from `validator/lean/Lz77/Lemmas.lean`:

```lean
theorem valid_lit (input ts : List Nat) (pos : Nat)
    (hd : decode ts = some (input.take pos))
    (hpos : pos < input.length) (hb : input[pos]! < 256) :
    decode (ts ++ [input[pos]!]) = some (input.take (pos + 1))

theorem valid_match (input ts : List Nat) (pos d L : Nat)
    (hd : decode ts = some (input.take pos))
    (hd1 : 1 ≤ d) (hdp : d ≤ pos) (hdmax : d ≤ MAX_DIST)
    (hl3 : 3 ≤ L) (hlmax : L ≤ MAX_LEN) (hL : pos + L ≤ input.length)
    (hm : ∀ k, k < L → input[pos - d + k]! = input[pos + k]!) :
    decode (ts ++ [mkMatch d L]) = some (input.take (pos + L))
```

Your loop invariant is *"the tokens written so far decode to the input consumed so
far"*, and these step it. Note `hm`: it is the only interesting hypothesis, and it
is exactly what a match-length loop computes. You never touch `copyN`, the
recursive definition underneath, and that is deliberate — describing a
back-reference as *the accumulator extended one byte at a time* rather than as a
list-valued function of the window is what keeps this affordable.

## What the contract does not cover, and why

**Huffman coding.** It is a bijection the harness implements once, identically for
every submission, in `validator/harness/src/deflate.rs`. Nothing about it is in
your obligation, and you cannot change it — which is also what makes the score a
fair comparison of parses.

**Block splitting.** Same: fixed in the harness. Worth ratio, and a natural second
slot, but not this one.

**Stability or determinism beyond the above.** The score is a byte count, so any
valid parse is acceptable. Two submissions that produce different token streams of
the same length tie.
