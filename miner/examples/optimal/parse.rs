//! The slot: LZ77 parsing by optimal parse over 32 KB blocks. A forward pass finds the
//! best match at every position, a backward dynamic program picks the cheapest path
//! under a static bit-cost model, and the emission pass re-verifies each chosen match
//! with `match_len` before writing it. Tokens: `t < 256` literal, else `2^24 + (dist-1)*256 + (len-3)`.

pub const MIN_MATCH: usize = 3;
pub const MAX_MATCH: usize = 258;
pub const WINDOW: usize = 32768;
pub const HASH_SIZE: usize = 32768;

/// How far down a hash chain to look.
pub const MAX_PROBES: usize = 24;
/// Stop the chain walk once a match at least this long is found.
pub const NICE_LEN: usize = 128;
/// Positions per dynamic-programming block; a match never crosses a block end.
pub const BLOCK: usize = 32768;
/// Besides the full match, the DP also tries every shorter length up to this.
pub const TRY_SHORT: usize = 8;
/// Estimated bits of a literal.
pub const LIT_BITS: u32 = 9;

/// Three bytes to a table index; `% 32768` so the bound is arithmetic. Correctness does not depend on it.
pub fn hash3(a: u8, b: u8, c: u8) -> usize {
    let x = (a as u32)
        .wrapping_mul(2654435761)
        .wrapping_add((b as u32).wrapping_mul(2246822519))
        .wrapping_add((c as u32).wrapping_mul(3266489917));
    ((x >> 15) % 32768) as usize
}

/// How many bytes agree at `a` and `b`, up to `cap`. The only function the proof depends on.
pub fn match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// Walk a hash chain for the best `(length, distance)`; first found wins ties, so the nearest.
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
    while probes < MAX_PROBES && cur > 0 && cur <= pos {
        let cpos = cur - 1;
        if pos - cpos <= 32768 {
            let l = match_len(input, cpos, pos, cap);
            if l > best_len {
                best_len = l;
                best_dist = pos - cpos;
            }
            if best_len >= NICE_LEN {
                cur = 0;
            } else {
                cur = prev[cpos % 32768] as usize;
            }
        } else {
            cur = 0;
        }
        probes += 1;
    }
    (best_len, best_dist)
}

/// Estimated bits to code a match of `len` bytes at `dist` back: length code plus distance code and extra bits.
pub fn match_bits(len: usize, dist: usize) -> u32 {
    let lb = if len <= 10 {
        7
    } else if len <= 18 {
        8
    } else if len <= 34 {
        9
    } else if len <= 66 {
        10
    } else if len <= 130 {
        11
    } else if len <= 257 {
        12
    } else {
        8
    };
    let mut extra = 0u32;
    let mut top = 4usize;
    while top < dist && extra < 13 {
        top = top * 2;
        extra += 1;
    }
    lb + 5 + extra
}

/// Cheapest way to leave position `i`: a literal, or the match `(mlen, dist)` at any tried length.
/// Returns `(bits, length)` with length `0` for a literal. Search only: the DP never has to be right.
pub fn relax(cost: &[u32], i: usize, mlen: usize, dist: usize, blen: usize) -> (u32, usize) {
    let mut best = cost[i + 1].saturating_add(LIT_BITS);
    let mut choice = 0usize;
    if mlen >= 3 && dist >= 1 && mlen <= blen - i {
        let c = cost[i + mlen].saturating_add(match_bits(mlen, dist));
        choice = if c < best { mlen } else { choice };
        best = if c < best { c } else { best };
        let mut l = 3usize;
        let stop = if mlen < TRY_SHORT { mlen } else { TRY_SHORT };
        while l < stop {
            let c2 = cost[i + l].saturating_add(match_bits(l, dist));
            choice = if c2 < best { l } else { choice };
            best = if c2 < best { c2 } else { best };
            l += 1;
        }
    }
    (best, choice)
}

/// True iff the chosen match `(ch, d)` at `pos` is in range and its bytes agree. The only
/// check the proof relies on; the dynamic program that chose it is never trusted.
pub fn verified(input: &[u8], pos: usize, d: usize, ch: usize, k: usize, blen: usize) -> bool {
    if ch < 3 || ch > 258 || d < 1 || d > 32768 || d > pos || k + ch > blen {
        return false;
    }
    let v = match_len(input, pos - d, pos, ch);
    v >= ch
}

/// Optimal parse: candidates forward, costs backward, emission forward with each match re-verified.
pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut head = [0u32; 32768];
    let mut prev = [0u32; 32768];
    let mut mlen = [0u32; 32768];
    let mut mdist = [0u32; 32768];
    let mut cost = [0u32; 32769];
    let mut choice = [0u32; 32769];
    let mut ntok = 0usize;
    let mut pos0 = 0usize;
    let has3 = n >= 3;
    let lim = if has3 { n - 3 } else { 0 };
    while pos0 < n {
        let rest = n - pos0;
        let blen = if rest > BLOCK { BLOCK } else { rest };
        // Forward: the best match at every position of the block, inserting each into the tables.
        let mut i = 0usize;
        while i < blen {
            let pos = pos0 + i;
            let mut l = 0usize;
            let mut d = 0usize;
            if has3 && pos <= lim {
                let h = hash3(input[pos], input[pos + 1], input[pos + 2]);
                let start = head[h] as usize;
                prev[pos % 32768] = head[h];
                head[h] = (pos + 1) as u32;
                let mut cap = blen - i;
                if cap > 258 {
                    cap = 258;
                }
                let found = find_match(input, &prev, pos, cap, start);
                l = found.0;
                d = found.1;
            }
            mlen[i] = l as u32;
            mdist[i] = d as u32;
            i += 1;
        }
        // Backward: cheapest bits from each position to the block end.
        cost[blen] = 0;
        choice[blen] = 0;
        let mut j = blen;
        while j > 0 {
            j -= 1;
            let r = relax(&cost, j, mlen[j] as usize, mdist[j] as usize, blen);
            cost[j] = r.0;
            choice[j] = r.1 as u32;
        }
        // Forward: emit the chosen path; `verified` re-checks every match before it is written.
        let mut k = 0usize;
        while k < blen {
            let pos = pos0 + k;
            let ch = choice[k] as usize;
            let d = mdist[k] as usize;
            if verified(input, pos, d, ch, k, blen) {
                out[ntok] = 16777216u32 + ((d - 1) as u32) * 256 + ((ch - 3) as u32);
                ntok += 1;
                k += ch;
            } else {
                out[ntok] = input[pos] as u32;
                ntok += 1;
                k += 1;
            }
        }
        pos0 += blen;
    }
    ntok
}
