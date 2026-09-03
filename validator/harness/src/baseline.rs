//! The incumbent. **Frozen** — a copy of the reference `slot/src/parse.rs` as of
//! the round in which it was promoted.
//!
//! The score is a submission's total compressed bytes against this one's, through
//! the same trusted encoder in `deflate.rs`. When a submission wins, the operator
//! promotes its `parse.rs` here and the bar moves.
//!
//! It is a plain copy rather than a dependency so that the file the miner edits
//! and the file they are measured against can never be the same object.

#![allow(dead_code)]

pub const MIN_MATCH: usize = 3;
pub const MAX_MATCH: usize = 258;
pub const WINDOW: usize = 32768;
pub const HASH_SIZE: usize = 32768;

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

/// Greedy matching against a single-slot hash head table. The baseline.
pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut head = [0u32; 32768];
    let mut ntok = 0usize;
    let mut pos = 0usize;
    // `pos <= n - 3` rather than `pos + 3 <= n`. The two are equivalent for real
    // inputs, but in the extracted model a slice may have length `usize::MAX`,
    // and then the *addition* overflows and the program is not total. The
    // subtraction is guarded and cannot. This is the second prover-friendly rule
    // after "no labelled control flow", and it is the one miners trip over.
    let has3 = n >= 3;
    let lim = if has3 { n - 3 } else { 0 };
    while pos < n {
        let mut best_len = 0usize;
        let mut best_dist = 0usize;
        if has3 && pos <= lim {
            let h = hash3(input[pos], input[pos + 1], input[pos + 2]);
            let cand = head[h] as usize;
            head[h] = (pos + 1) as u32;
            if cand > 0 && cand <= pos {
                let cpos = cand - 1;
                if pos - cpos <= 32768 {
                    let mut cap = n - pos;
                    if cap > 258 {
                        cap = 258;
                    }
                    let l = match_len(input, cpos, pos, cap);
                    if l >= 3 {
                        best_len = l;
                        best_dist = pos - cpos;
                    }
                }
            }
        }
        if best_len >= 3 {
            out[ntok] = 16777216u32 + ((best_dist - 1) as u32) * 256 + ((best_len - 3) as u32);
            ntok += 1;
            let end = pos + best_len;
            let mut k = pos + 1;
            while k < end && has3 && k <= lim {
                let h2 = hash3(input[k], input[k + 1], input[k + 2]);
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
