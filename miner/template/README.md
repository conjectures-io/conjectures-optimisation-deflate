# template/

A complete submission that passes the gate today. Copy it and start from here.

```bash
cp -r miner/template my-submission
just check my-submission
```

It scores `1.000x` — byte-identical to the incumbent, because it *is* the
incumbent. Your job is to beat it.

| file | lines | what it is |
|---|---|---|
| `parse.rs` | 66 | greedy matching against a single-slot hash table |
| `Parse.lean` | 204 | its proof of `LZ77.Obligation` |
| `submission.toml` | — | metadata; edit the name |

## What is in `parse.rs`

Three functions, and it is worth knowing which is which before you change
anything:

* `hash3` — three bytes to a table index. **Correctness does not depend on it**;
  its proof says only that the result is below 32768.
* `match_len` — how many bytes agree at two positions. **The only function whose
  result the proof depends on.** Its postcondition is exactly the hypothesis the
  contract's `valid_match` wants.
* `parse` — the outer loop: hash, look up one candidate, verify it, emit a match
  or a literal, and keep the table current.

## Where the easy wins are

The template deliberately leaves a lot on the table.

1. **Look at more than one candidate.** It keeps only the most recent position per
   hash. Chaining them is worth 14% and costs 32 proof lines — done, with the
   diff, in [`../examples/hash-chains`](../examples/hash-chains/NOTES.md).
2. **Lazy matching.** Before emitting a match at `pos`, check whether `pos+1` has
   a longer one; if so emit a literal instead. Classic, and worth several percent.
   Note this one changes the *emission*, so the proof diff is larger than a
   search-only change.
3. **Better tie-breaking.** Among equal-length matches, a nearer one costs fewer
   extra bits. The template takes the first it finds.
4. **Optimal parsing.** The real prize, and what libdeflate does. A dynamic
   program over the whole block, which is still just a search — so the proof stays
   on the cheap side of the line in [`../CONTRACT.md`](../CONTRACT.md).

## Before you change the proof

Read `Parse.lean` once with `../CONTRACT.md` open. The structure is:

```
hash3_spec              the hash lands in range        (search — cheap)
match_len_loop_spec     the bytes really do agree      (the load-bearing one)
parse_loop0_loop0_spec  the table update terminates    (search — postcondition True)
Found                   the interface between them
parse_loop0_spec        the invariant: tokens so far decode to input so far
parse_spec              the obligation
```

If your change is confined to the search, you touch the first three and `Found`
stays as it is.
