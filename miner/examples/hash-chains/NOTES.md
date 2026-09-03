# A worked improvement: hash chains

**14.0% smaller output. 32 more proof lines.** This directory is the diff between
`../../template` and a submission that beats it, and it exists because the ratio
between those two numbers is the only thing that decides whether this competition
is worth entering.

```bash
diff -u ../../template/parse.rs   parse.rs
diff -u ../../template/Parse.lean Parse.lean
just check miner/examples/hash-chains
```

| | template | this | change |
|---|---|---|---|
| `parse.rs` | 66 lines | 90 | +24 |
| `Parse.lean` | 204 lines | 236 | **+32** |
| score | 1.000x | **0.860x** | −14.0% |
| parse time | 4.8 ms/MiB | 11.9 ms/MiB | budget is 8000 ms/MiB |

## What changed in the Rust

The template keeps one candidate per hash: `head[h]` is the most recent position
whose three bytes hash to `h`. This keeps a **chain** of them.

```rust
let mut head = [0u32; 32768];
let mut prev = [0u32; 32768];       // new
…
let start = head[h] as usize;
prev[pos % 32768] = head[h];        // link the old head into the chain
head[h] = (pos + 1) as u32;
```

and walks up to 16 of them, keeping the longest match:

```rust
pub fn find_match(input: &[u8], prev: &[u32], pos: usize, cap: usize,
                  start: usize) -> (usize, usize) {
    let mut best_len = 0usize;
    let mut best_dist = 0usize;
    let mut cur = start;
    let mut probes = 0usize;
    while probes < 16 && cur > 0 && cur <= pos {
        let cpos = cur - 1;
        if pos - cpos <= 32768 {
            let l = match_len(input, cpos, pos, cap);
            if l > best_len { best_len = l; best_dist = pos - cpos; }
            cur = prev[cpos % 32768] as usize;
        } else {
            cur = 0;
        }
        probes += 1;
    }
    (best_len, best_dist)
}
```

`prev` is indexed cyclically by `pos % 32768`, so it is a fixed-size array rather
than one allocation per input. Positions are stored as truncated `u32`s, so a
chain entry can point anywhere; that is harmless, and provably so.

Two rules from [`../../RULES.md`](../../RULES.md) were forced here:

* **Rule 5.** The chain walk started life as a loop nested inside `parse`'s outer
  loop, reading `prev` from the enclosing scope. Aeneas reports `Unimplemented`.
  Lifting it into `find_match` with `prev: &[u32]` translates.
* **Rule 4.** The walk terminates on `probes < 16`, not on the chain being
  acyclic — because nothing makes it acyclic.

## What changed in the proof

Three things, and only the first is interesting.

**One new lemma, `find_match_loop_spec`.** Its postcondition is `Found`, and
`Found` is also its loop invariant:

```lean
apply Std.loop.spec_decr_nat
  (measure := fun s => 16 - s.2.2.2.val)
  (inv := fun s => Found input n pos s.1 s.2.1)
```

When a candidate beats the incumbent best, the new pair has to satisfy `Found`:
either it is shorter than 3 (the left disjunct, nothing to prove) or every range
condition holds and `Matches` comes straight from `match_len_spec`. That is the
whole argument.

Nothing in it says the chain is acyclic, that `prev` points anywhere sensible, or
that the match found is the best available. It could not: none of those are true.

**Bookkeeping for the new array.** `parse` gained a second `[u32; 32768]`, so the
state tuples in `parse_loop0_spec` and `parse_loop0_loop0_spec` grew a component
and every projection index shifted. Mechanical, and most of the +32 lines.

**Nothing else.** `valid_lit`, `valid_match`, `parse_spec`, the loop invariant
"the tokens written so far decode to the input consumed so far", and the entire
emission argument are byte-identical to the template's.

That is the point of `Found`. Read
[`../../CONTRACT.md`](../../CONTRACT.md) for where the line falls.

## What was left on the table

This submission still makes a **greedy** decision: whatever the search returns at
`pos` is emitted at `pos`. Lazy matching — check `pos+1` before committing — is
the obvious next step, and unlike this change it touches the *emission*, so the
proof diff will be larger. libdeflate remains 10.1% below this submission on the
same corpus.
