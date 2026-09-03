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
//! ## What is *not* constrained
//!
//! Nothing about the search. The hash chains below could be a suffix automaton, a
//! binary tree, or a full optimal-parse dynamic program and the proof would not
//! grow, because correctness rests only on the bytes `match_len` actually
//! compared before a match was emitted. `hash3_spec` in the proof says the hash
//! lands in range and says nothing whatever about what it computes.
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

/// How far down a hash chain to look. The whole speed/ratio dial.
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

/// Walk a hash chain and return the best `(length, distance)` it finds.
///
/// A separate function rather than a loop inside `parse`, and that is **not**
/// cosmetic: Aeneas reports `Unimplemented` for a second loop nested in the body
/// of `parse`'s outer loop when that loop also reads a local array of the
/// enclosing scope. Lifting it out, with the array as a `&[u32]` parameter,
/// translates. Prover-friendly rule 5.
///
/// `prev` must be at least 32768 long; `parse` passes a `[u32; 32768]`.
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
            // Everything further down the chain is older still, so the walk is
            // over. `cur = 0` ends it without a `break`.
            cur = 0;
        }
        probes += 1;
    }
    (best_len, best_dist)
}

/// Greedy matching over hash chains.
///
/// `head[h]` is the most recent position whose three bytes hash to `h`, plus one
/// (zero means "none"). `prev[p % 32768]` is the position before `p` in the same
/// chain, plus one. The `+ 1` is what lets zero be the sentinel without a
/// separate occupancy array, and `% 32768` keeps `prev` a fixed-size array rather
/// than one allocation per input.
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
            prev[pos % 32768] = head[h];
            head[h] = (pos + 1) as u32;

            let mut cap = n - pos;
            if cap > 258 {
                cap = 258;
            }
            // The chain walk. It terminates on `probes`, never on the chain
            // being acyclic — a truncated `as u32` can point anywhere, and the
            // byte comparison inside `match_len` is what keeps that harmless.
            let found = find_match(input, &prev, pos, cap, start);
            best_len = found.0;
            best_dist = found.1;
        }
        if best_len >= 3 {
            out[ntok] = 16777216u32 + ((best_dist - 1) as u32) * 256 + ((best_len - 3) as u32);
            ntok += 1;
            let end = pos + best_len;
            let mut k = pos + 1;
            while k < end && has3 && k <= lim {
                let h2 = hash3(input[k], input[k + 1], input[k + 2]);
                prev[k % 32768] = head[h2];
                head[h2] = (k + 1) as u32;
                k += 1;
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
