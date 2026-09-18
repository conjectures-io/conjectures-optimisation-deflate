//! # The slot: LZ77 parsing.
//!
//! This whole file is what a miner replaces. It must be compilable as its own
//! crate root (`charon rustc … src/parse.rs`), so it may not `use crate::…`.
//!
//! ## The contract
//!
//! `parse` reads `input` and writes a token stream into `out`, returning how many
//! tokens it wrote. A token is a `u32`:
//!
//! * `t < 256`                           — emit the literal byte `t`
//! * `t = 2^24 + (dist-1)*256 + (len-3)` — copy `len` bytes from `dist` back
//!
//! with `1 ≤ dist ≤ 32768` and `3 ≤ len ≤ 258`. The arithmetic encoding (rather
//! than shifts and masks) is deliberate: `Nat` `+`, `*`, `/` and `%` are what
//! `omega` reasons about on the Lean side, and `&&&`/`<<<` are not.
//!
//! The only thing that must be proved is that the token stream **decodes back to
//! `input`**, and that `parse` neither panics nor diverges.
//!
//! ## This variant
//!
//! Same sixteen-probe search as `hash-chains`, but the hash table is only
//! *updated* every fourth position (`pos % 4 == 0`), never on the other three.
//! A different way to spend less time than `hash-chains`: cheaper table
//! upkeep instead of a shallower search, in the spirit of the low insertion
//! rate zlib/miniz_oxide use at their own fastest levels. Included as a
//! second "not much potential" fast candidate, for comparison against
//! `hc-d4`'s shallow-search approach to the same time budget.
//!
//! Correctness does not care how sparse the table is: a hash bucket that is
//! never updated just never offers a candidate, which `find_match` already
//! handles (an empty chain returns no match).
//!
//! ## Prover-friendly Rust — the rules
//!
//! 1. No labelled `break`/`continue`, no early `return` from a nested loop, no
//!    trait objects, no iterator adapters. Indices, `while`, and plain `if`.
//! 2. Prefer `i <= n - k` to `i + k <= n`. In the extracted model a slice may
//!    have length `usize::MAX`, and then the *addition* overflows and the program
//!    is not total. The guarded subtraction cannot.
//! 3. Bound every array index with `%`, not `&`. `h % 32768 < 32768` is one
//!    `omega` step; the same fact about `h & 0x7fff` is a bitvector argument.
//! 4. Give every loop a decreasing counter that does not depend on the data. The
//!    chain walk below terminates because `probes` increases, not because the
//!    chain is acyclic — which it need not be.

pub const MIN_MATCH: usize = 3;
pub const MAX_MATCH: usize = 258;
pub const WINDOW: usize = 32768;
pub const HASH_SIZE: usize = 32768;

/// How far down a hash chain to look.
pub const MAX_PROBES: usize = 16;

/// Hash of the three bytes at a position. Any function of the right range works;
/// `% 32768` rather than `& 0x7fff` so that the index bound is arithmetic.
pub fn hash3(a: u8, b: u8, c: u8) -> usize {
    let x = (a as u32)
        .wrapping_mul(2654435761)
        .wrapping_add((b as u32).wrapping_mul(2246822519))
        .wrapping_add((c as u32).wrapping_mul(3266489917));
    ((x >> 15) % 32768) as usize
}

/// How many bytes match at `a` and `b`, up to `cap`. This is the *only* function
/// whose result the correctness proof depends on.
pub fn match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// Record `pos` in the hash table for its bucket `h`, if `pos` is due for
/// insertion (`pos % 4 == 0`). A separate function, not an `if` inline in
/// `parse`'s loop body: Aeneas reports `Unimplemented` on the array writes
/// otherwise, the same limitation that made `find_match` its own function.
pub fn maybe_insert(head: &mut [u32; 32768], prev: &mut [u32; 32768], h: usize, pos: usize) {
    if pos % 4 == 0 {
        prev[pos % 32768] = head[h];
        head[h] = (pos + 1) as u32;
    }
}

/// Walk a hash chain and return the best `(length, distance)` it finds.
pub fn find_match(
    input: &[u8],
    prev: &[u32],
    pos: usize,
    cap: usize,
    start: usize,
) -> (usize, usize) {
    let mut best_len = 0usize;
    let mut best_dist = 0usize;
    let mut cur = start;
    let mut probes = 0usize;
    while probes < 16 && cur > 0 && cur <= pos {
        let cpos = cur - 1;
        if pos - cpos <= 32768 {
            let l = match_len(input, cpos, pos, cap);
            if l > best_len {
                best_len = l;
                best_dist = pos - cpos;
            }
            cur = prev[cpos % 32768] as usize;
        } else {
            cur = 0;
        }
        probes += 1;
    }
    (best_len, best_dist)
}

/// Greedy matching over hash chains, inserted sparsely.
///
/// `head[h]` is the most recent *inserted* position whose three bytes hash to
/// `h`, plus one (zero means "none"). A position `p` is inserted only when
/// `p % 4 == 0`; every other position is searched but never recorded, which
/// costs nothing to prove -- the insert loop's postcondition is `True`
/// whether or not it runs on a given iteration.
pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut head = [0u32; 32768];
    let mut prev = [0u32; 32768];
    let mut ntok = 0usize;
    let mut pos = 0usize;
    let has3 = n >= 3;
    let lim = if has3 { n - 3 } else { 0 };
    while pos < n {
        let mut best_len = 0usize;
        let mut best_dist = 0usize;
        if has3 && pos <= lim {
            let h = hash3(input[pos], input[pos + 1], input[pos + 2]);
            let start = head[h] as usize;
            maybe_insert(&mut head, &mut prev, h, pos);

            let mut cap = n - pos;
            if cap > 258 {
                cap = 258;
            }
            let found = find_match(input, &prev, pos, cap, start);
            best_len = found.0;
            best_dist = found.1;
        }
        if best_len >= 3 {
            out[ntok] = 16777216u32 + ((best_dist - 1) as u32) * 256 + ((best_len - 3) as u32);
            ntok += 1;
            let end = pos + best_len;
            let mut k = pos + 1;
            // Round `k` up to the next inserted (multiple-of-4) position once,
            // outside the loop, so the loop body itself is unconditional --
            // the same shape as `hash-chains`' inner loop, just stepping by 4.
            let rem = k % 4;
            if rem != 0 {
                k += 4 - rem;
            }
            while k < end && has3 && k <= lim {
                let h2 = hash3(input[k], input[k + 1], input[k + 2]);
                prev[k % 32768] = head[h2];
                head[h2] = (k + 1) as u32;
                k += 4;
            }
            pos = end;
        } else {
            out[ntok] = input[pos] as u32;
            ntok += 1;
            pos += 1;
        }
    }
    ntok
}
