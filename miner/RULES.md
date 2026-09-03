# Prover-friendly Rust

Six rules. Every one was found by something failing, not by reading a manual.
Stage 1 of the gate enforces the mechanical ones; the rest fail later and more
expensively, which is why they are here.

The background: Charon and Aeneas translate 9 of 12 common hot-loop shapes into
Lean. The three they do not are all iterator-shaped. Imperative, index-based Rust
— which is how hot loops are written anyway — is inside the subset.

---

## 1. Indices, `while`, and plain `if`

**Rejected:** `unsafe`, labelled loops, labelled `break`/`continue`, `for … in`,
iterator adapters (`.iter()`, `.map()`, `.fold()`, `.chunks()`, …), trait objects,
`impl Trait`, SIMD intrinsics, `extern`, `asm!`, `static mut`, `mod`,
`include_str!`, `use crate::`.

```rust
// rejected — Iterator is opaque, so there is nothing to reason about
let total: usize = xs.iter().map(|x| x.len()).sum();

// accepted
let mut total = 0usize;
let mut i = 0usize;
while i < xs.len() {
    total += xs[i].len();
    i += 1;
}
```

`use crate::` is rejected because your file is compiled as its own crate root —
`charon rustc … src/parse.rs`. It must be self-contained.

## 2. Prefer `i <= n - k` to `i + k <= n`

```rust
// rejected — in the extracted model a slice may have length usize::MAX, and
// then this ADDITION overflows, so `parse` is not total and the proof fails
if pos + 3 <= n { … }

// accepted — the subtraction is guarded and cannot overflow
let has3 = n >= 3;
let lim = if has3 { n - 3 } else { 0 };
if has3 && pos <= lim { … }
```

This one surprises people. The two forms are equivalent for any input that fits in
memory, but the model does not know that, and "not total on a slice nobody can
allocate" is still not total.

Hoist `has3`/`lim` out of the loop rather than recomputing: they become loop state
either way, and hoisting keeps the loop body smaller.

## 3. Bound array indices with `%`, not `&`

```rust
// rejected in practice — provable, but every index costs you a bitvector argument
let h = hash & 0x7fff;

// accepted — `h % 32768 < 32768` is one `omega` step
let h = hash % 32768;
```

Not a hard rejection by the scanner, but it will dominate your proof if you ignore
it.

## 4. Every loop needs a counter that decreases regardless of the data

```rust
// rejected — terminates only if the chain is acyclic, and nothing makes it so:
// a truncated `as u32` can point anywhere
while cur > 0 && cur <= pos {
    cur = prev[cur % 32768] as usize;
}

// accepted — terminates on `probes`, whatever the chain looks like
let mut probes = 0usize;
while probes < 16 && cur > 0 && cur <= pos {
    …
    cur = prev[cpos % 32768] as usize;
    probes += 1;
}
```

Walking a corrupt chain is harmless because `match_len` compares the bytes before
anything is emitted. That is the same property that lets you use any search you
like — see [`CONTRACT.md`](CONTRACT.md).

## 5. Lift a nested loop into its own function if it reads an array from the enclosing scope

```rust
// rejected — Aeneas reports `Unimplemented` for a second loop nested in the
// body of `parse`'s outer loop when it also reads a local array
pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let mut prev = [0u32; 32768];
    while pos < n {
        …
        while probes < 16 && cur > 0 {
            cur = prev[cur % 32768] as usize;
            probes += 1;
        }
    }
}

// accepted — the array becomes a parameter
pub fn find_match(input: &[u8], prev: &[u32], pos: usize, cap: usize,
                  start: usize) -> (usize, usize) { … }
```

This is better structure regardless: `find_match` is exactly the unit a
submission replaces, and giving it a name is what keeps the rest of the proof
untouched when you change the search.

## 6. No fallible arithmetic where it cannot be guarded

A `while` guard is fine with comparisons and with arithmetic that provably cannot
fail; move anything else into the body. Divisions and `%` need a non-zero divisor,
and subtraction on `usize` needs the operands ordered — guard both, or restructure:

```rust
// awkward: the subtraction has to be justified inside a boolean chain
while probes < 16 && cur > 0 && cur <= pos && pos - (cur - 1) <= 32768 { … }

// clearer, and the same program
while probes < 16 && cur > 0 && cur <= pos {
    let cpos = cur - 1;
    if pos - cpos <= 32768 { … } else { cur = 0; }
    probes += 1;
}
```

`cur = 0` ends the walk without a `break`.

---

## Two Aeneas facts that will cost you an afternoon

**`step*` will not enter a `do` block whose first statement is an `if`.** Cut it
with `Std.WP.spec_bind` and an explicit intermediate postcondition:

```lean
apply Std.WP.spec_bind (Pₘ := fun r => Found input n pos r.1 r.2)
· -- the block behind the `if`
· -- the continuation, with `Found` in hand
```

In practice that cut lands where you wanted a named property anyway. `Found` *is*
one of these cuts, and it is the better structure.

**`if b then ok x else ok y` must be rewritten before `step*` continues:**

```lean
rw [show ((if cap > 258#usize then ok 258#usize else ok cap) : Result Std.Usize)
    = ok (if cap > 258#usize then 258#usize else cap) from by split <;> rfl]
```

## And one that will save you an afternoon

Register your own lemmas with `@[local step]`. Once `hash3_spec`,
`match_len_spec`, `find_match_spec` and `parse_loop0_loop0_spec` are registered,
`step*` discharges nearly all the plumbing by itself — and once `Found` is
unfolded in context, every range obligation of the token encoding as well.
