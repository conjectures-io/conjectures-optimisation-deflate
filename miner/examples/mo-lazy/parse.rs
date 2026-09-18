//! # The slot: LZ77 parsing -- a faithful reproduction of `miniz_oxide`'s own
//! level-9 strategy (`miniz_oxide::deflate::core`, as vendored at 0.8.9),
//! reimplemented in this repo's provable subset.
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
//! with `1 ≤ dist ≤ 32768` and `3 ≤ len ≤ 258`.
//!
//! ## What this reproduces, and why
//!
//! `miniz_oxide`'s reference bars (`mo1`, `mo9`) are the harness's own points
//! of comparison, but neither `template` (miniz_oxide level 1's shape: a
//! single hash-head candidate, greedy) nor `lazy` (lazy matching over hash
//! chains, but tuned far shallower than miniz_oxide ever runs) actually *is*
//! what miniz_oxide's better levels do. This is an attempt at the real thing,
//! ported line-for-line from `deflate/core.rs`'s `find_match` and its lazy
//! decision loop, level 9's parameters:
//!
//! * The exact hash: `(a << 10) ^ (b << 5) ^ c`, masked to 15 bits. Their
//!   code masks with `& 0x7FFF`; this uses `% 32768` instead, which is the
//!   same operation (32768 is a power of two) done in the form `omega` can
//!   reason about arithmetically rather than as a bitvector fact.
//! * The **split probe budget** real miniz_oxide uses and none of this
//!   repo's other examples do: up to 257 probes while the best match found
//!   so far is under 32 bytes, dropping to 65 once it reaches 32 -- spend
//!   less further effort once a match is already decent.
//! * Lazy matching (defer one byte, take the better of the two), *except*
//!   accept immediately without deferring when a match reaches 128 bytes --
//!   already excellent, not worth the lookahead.
//! * The "far and small" rule: a length-3 match at distance ≥ 8192 is
//!   discarded (falls back to a literal) -- not worth the distance code for
//!   that little payoff.
//!
//! What is *not* reproduced: `miniz_oxide`'s low-level match-length shortcut
//! (comparing two bytes at a time via a `u16`/`u64` read rather than one at a
//! time) and its RLE/filtered-match modes (level 9 default uses neither).
//! These are speed micro-optimizations and encoder strategy switches, not
//! part of *this* strategy, and the byte-at-a-time `match_len` below is the
//! same one every other example in this repo uses, so its cost is already
//! accounted for identically across candidates.
//!
//! ## Prover-friendly Rust — the rules
//!
//! Same four rules as every other slot in this repo: guarded subtraction,
//! `%`-bounded indices, no labelled control flow, a decreasing loop counter
//! independent of the data. `find_match` takes its probe budget as a
//! parameter (`probe_cap`) rather than a fixed constant, since miniz_oxide's
//! own budget varies call to call -- the loop still terminates on `probes`,
//! whatever `probe_cap` happens to be.

pub const MIN_MATCH: usize = 3;
pub const MAX_MATCH: usize = 258;
pub const WINDOW: usize = 32768;
pub const HASH_SIZE: usize = 32768;

/// `miniz_oxide`'s own split: many probes while the match is still short,
/// fewer once it is already long. Level 9's numbers (`NUM_PROBES[9] = 768`
/// fed through `probes_from_flags`).
pub const PROBES_SHORT: usize = 257;
pub const PROBES_LONG: usize = 65;
pub const LONG_THRESHOLD: usize = 32;
/// Accept a match immediately, without checking the next position, once it
/// reaches this length.
pub const IMMEDIATE_ACCEPT: usize = 128;
/// A length-3 match this far away or farther is not worth its distance code.
pub const FAR_DIST: usize = 8192;

/// `miniz_oxide`'s own hash: `(a << 10) ^ (b << 5) ^ c`, 15 bits. `% 32768`
/// here is the arithmetic form of their `& 0x7FFF`; same value either way.
pub fn hash3(a: u8, b: u8, c: u8) -> usize {
    let x = ((a as u32) << 10) ^ ((b as u32) << 5) ^ (c as u32);
    (x % 32768) as usize
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

/// Walk a hash chain and return the best `(length, distance)` it finds,
/// spending at most `probe_cap` probes.
pub fn find_match(
    input: &[u8],
    prev: &[u32],
    pos: usize,
    cap: usize,
    start: usize,
    probe_cap: usize,
) -> (usize, usize) {
    let mut best_len = 0usize;
    let mut best_dist = 0usize;
    let mut cur = start;
    let mut probes = 0usize;
    while probes < probe_cap && cur > 0 && cur <= pos && best_len < cap {
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

/// The probe budget for a search that already knows about a match of length
/// `hint` (0 if none yet) -- `miniz_oxide`'s own dial: ease off once a match
/// is already decent.
pub fn probe_budget(hint: usize) -> usize {
    if hint >= LONG_THRESHOLD {
        PROBES_LONG
    } else {
        PROBES_SHORT
    }
}

/// Reject a match not worth its own encoding: a minimum-length match at a
/// large distance costs more in the distance code than the three literal
/// bytes it would otherwise be.
pub fn far_and_small(len: usize, dist: usize) -> bool {
    len == MIN_MATCH && dist >= FAR_DIST
}

/// Lazy matching over hash chains, `miniz_oxide` level 9's own dials.
pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut head = [0u32; 32768];
    let mut prev = [0u32; 32768];
    let mut ntok = 0usize;
    let mut pos = 0usize;
    let has3 = n >= 3;
    let lim = if has3 { n - 3 } else { 0 };
    let mut pend_len = 0usize;
    let mut pend_dist = 0usize;
    while pos < n {
        let mut cur_len = 0usize;
        let mut cur_dist = 0usize;
        if has3 && pos <= lim {
            let h = hash3(input[pos], input[pos + 1], input[pos + 2]);
            let start = head[h] as usize;
            prev[pos % 32768] = head[h];
            head[h] = (pos + 1) as u32;

            let mut cap = n - pos;
            if cap > 258 {
                cap = 258;
            }
            let budget = probe_budget(pend_len);
            let found = find_match(input, &prev, pos, cap, start, budget);
            cur_len = found.0;
            cur_dist = found.1;
            if cur_len < 3 || far_and_small(cur_len, cur_dist) {
                cur_len = 0;
                cur_dist = 0;
            }
        }

        if pend_len >= 3 {
            if cur_len > pend_len {
                // The lookahead beat the pending match: `pos - 1` is a
                // literal, and this new match either replaces it as pending
                // (still worth a further look) or, if already excellent, is
                // taken immediately.
                out[ntok] = input[pos - 1] as u32;
                ntok += 1;
                if cur_len >= IMMEDIATE_ACCEPT {
                    out[ntok] =
                        16777216u32 + ((cur_dist - 1) as u32) * 256 + ((cur_len - 3) as u32);
                    ntok += 1;
                    let end = pos + cur_len;
                    let mut k = pos + 1;
                    while k < end && has3 && k <= lim {
                        let h2 = hash3(input[k], input[k + 1], input[k + 2]);
                        prev[k % 32768] = head[h2];
                        head[h2] = (k + 1) as u32;
                        k += 1;
                    }
                    pos = end;
                    pend_len = 0;
                    pend_dist = 0;
                } else {
                    pend_len = cur_len;
                    pend_dist = cur_dist;
                    pos += 1;
                }
            } else {
                // The pending match still wins: emit it, insert the
                // positions it covers, continue after it.
                out[ntok] = 16777216u32 + ((pend_dist - 1) as u32) * 256 + ((pend_len - 3) as u32);
                ntok += 1;
                let end = pos - 1 + pend_len;
                let mut k = pos + 1;
                while k < end && has3 && k <= lim {
                    let h2 = hash3(input[k], input[k + 1], input[k + 2]);
                    prev[k % 32768] = head[h2];
                    head[h2] = (k + 1) as u32;
                    k += 1;
                }
                pos = end;
                pend_len = 0;
                pend_dist = 0;
            }
        } else if cur_len >= IMMEDIATE_ACCEPT {
            // No pending match, and this one is already excellent: take it
            // without spending a lookahead on it.
            out[ntok] = 16777216u32 + ((cur_dist - 1) as u32) * 256 + ((cur_len - 3) as u32);
            ntok += 1;
            let end = pos + cur_len;
            let mut k = pos + 1;
            while k < end && has3 && k <= lim {
                let h2 = hash3(input[k], input[k + 1], input[k + 2]);
                prev[k % 32768] = head[h2];
                head[h2] = (k + 1) as u32;
                k += 1;
            }
            pos = end;
        } else if cur_len >= 3 {
            pend_len = cur_len;
            pend_dist = cur_dist;
            pos += 1;
        } else {
            out[ntok] = input[pos] as u32;
            ntok += 1;
            pos += 1;
        }
    }
    // Provably unreachable (see Parse.lean): the loop above never leaves
    // `pos == n` with a pending match still unemitted, since the last
    // position that could start a match has `pos <= lim < n`.
    if pend_len >= 3 {
        out[ntok] = 16777216u32 + ((pend_dist - 1) as u32) * 256 + ((pend_len - 3) as u32);
        ntok += 1;
    }
    ntok
}
