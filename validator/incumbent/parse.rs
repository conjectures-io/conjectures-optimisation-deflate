//! The incumbent: a frozen copy of a promoted `parse.rs`, kept apart from the file miners edit so the two can never be the same object.

#![allow(dead_code)]
pub const MIN_MATCH: usize = 3;
pub const MAX_MATCH: usize = 258;
pub const WINDOW: usize = 32768;
pub const HASH_SIZE: usize = 32768;

/// How far down a hash chain to look. The main speed/ratio dial.
pub const MAX_PROBES: usize = 32;
/// Stop the chain walk once a match at least this long is found.
pub const NICE_LEN: usize = 128;
/// Do not look ahead when the pending match is already at least this long.
pub const LAZY_LIMIT: usize = 32;

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

/// Lazy matching: `pend_len >= 3` is a match found at `pos - 1`, not yet emitted because `pos` might beat it.
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
            if pend_len < LAZY_LIMIT {
                let mut cap = n - pos;
                if cap > 258 {
                    cap = 258;
                }
                let found = find_match(input, &prev, pos, cap, start);
                cur_len = found.0;
                cur_dist = found.1;
            }
        }
        if pend_len >= 3 {
            if pend_len >= cur_len {
                // The pending match wins: emit it, insert the positions it covers, continue after it.
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
            } else {
                // The match at `pos` is longer: `pos - 1` becomes a literal and `pos` is pending.
                out[ntok] = input[pos - 1] as u32;
                ntok += 1;
                pend_len = cur_len;
                pend_dist = cur_dist;
                pos += 1;
            }
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
    // Provably unreachable (see Parse.lean); kept so no path leaves a token unemitted.
    if pend_len >= 3 {
        out[ntok] = 16777216u32 + ((pend_dist - 1) as u32) * 256 + ((pend_len - 3) as u32);
        ntok += 1;
    }
    ntok
}
