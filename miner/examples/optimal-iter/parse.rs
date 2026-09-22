//! The slot: optimal parse with one Huffman-aware cost iteration. A forward pass finds
//! the best match at every position; a backward dynamic program picks the cheapest path
//! under static bit costs; the symbols that path would emit are counted and turned into
//! per-symbol bit costs; the dynamic program runs once more under those costs; the
//! emission pass re-verifies each chosen match with `match_len` before writing it.
//! Tokens: `t < 256` literal, else `2^24 + (dist-1)*256 + (len-3)`.

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
/// Estimated bits of a literal, first pass. Costs are in quarter bits.
pub const LIT_BITS: u32 = 36;
/// A symbol the first pass never used still gets a cost: this many quarter bits (15 bits, the Huffman limit).
pub const COST_CAP: u32 = 60;

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
    (lb + 5 + extra) * 4
}

/// DEFLATE length code index (0..28) and its extra bits for `len` in 3..=258. `width` is
/// `4 << extra`, kept as a doubled counter so the model has no shifts; the index is clamped
/// so its bound is immediate. Search only: correctness never depends on it.
pub fn len_code(len: usize) -> (usize, u32) {
    if len <= 10 {
        return (if len >= 3 { len - 3 } else { 0 }, 0);
    }
    if len >= 258 {
        return (28, 0);
    }
    let mut extra = 1u32;
    let mut base = 11usize;
    let mut idx = 8usize;
    let mut width = 8usize;
    while base + width <= len && extra < 5 {
        base += width;
        width = width * 2;
        idx += 4;
        extra += 1;
    }
    // `off = (len - base) / (width / 4)`, counted rather than divided, so the model has no variable divisor.
    let step = width / 4;
    let mut off = 0usize;
    let mut t = base;
    while off < 3 && t + step <= len {
        t += step;
        off += 1;
    }
    let code = idx + off;
    (if code > 28 { 28 } else { code }, extra)
}

/// DEFLATE distance code index (0..29) and its extra bits for `dist` in 1..=32768. Same shape.
pub fn dist_code(dist: usize) -> (usize, u32) {
    let dist = if dist > 32768 { 32768 } else { dist };
    if dist <= 4 {
        return (if dist >= 1 { dist - 1 } else { 0 }, 0);
    }
    let mut extra = 1u32;
    let mut base = 5usize;
    let mut idx = 4usize;
    let mut width = 4usize;
    while base + width <= dist && extra < 13 && width <= 16384 {
        base += width;
        width = width * 2;
        idx += 2;
        extra += 1;
    }
    let step = width / 2;
    let mut off = 0usize;
    let mut t = base;
    while off < 1 && t + step <= dist {
        t += step;
        off += 1;
    }
    let code = idx + off;
    (if code > 29 { 29 } else { code }, extra)
}

/// `2^(r/4)` in 1/256ths for `r = c % 4`: the fractional part of a quarter-bit step.
pub fn quarter_mult(c: u32) -> u64 {
    let r = c % 4;
    if r == 0 {
        256
    } else if r == 1 {
        304
    } else if r == 2 {
        362
    } else {
        431
    }
}

/// Quarter-bit cost of a symbol seen `freq` times out of `total`: about `4 * log2(total / freq)`, capped.
pub fn sym_cost(freq: u32, total: u32) -> u32 {
    if freq == 0 {
        return COST_CAP;
    }
    let mut c = 0u32;
    let mut scaled = freq as u64 * 256;
    let target = total as u64 * 65536;
    while scaled < 1125899906842624 && scaled * quarter_mult(c) < target && c < COST_CAP {
        c += 1;
        if c % 4 == 0 {
            scaled = scaled * 2;
        }
    }
    if c < 4 { 4 } else { c }
}

/// Turn symbol counts into quarter-bit costs; the last entry of `freq` is the total.
pub fn costs_from(freq: &[u32], cost: &mut [u32], n: usize) {
    let total = freq[n];
    let mut s = 0usize;
    while s < n {
        cost[s] = sym_cost(freq[s], total);
        s += 1;
    }
}

/// Quarter-bit cost of a match under the learned costs: length code, its extra bits, distance code, its extra bits.
pub fn match_cost(ll_cost: &[u32], d_cost: &[u32], len: usize, dist: usize) -> u32 {
    let lc = len_code(len);
    let dc = dist_code(dist);
    let le = if lc.1 > 13 { 13 } else { lc.1 };
    let de = if dc.1 > 13 { 13 } else { dc.1 };
    ll_cost[257 + lc.0]
        .saturating_add(le * 4)
        .saturating_add(d_cost[dc.0])
        .saturating_add(de * 4)
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

/// `relax` under the learned costs: the literal costs what this byte costs, a match what its codes cost.
pub fn relax2(
    cost: &[u32],
    ll_cost: &[u32],
    d_cost: &[u32],
    byte: u8,
    i: usize,
    mlen: usize,
    dist: usize,
    blen: usize,
) -> (u32, usize) {
    let mut best = cost[i + 1].saturating_add(ll_cost[byte as usize]);
    let mut choice = 0usize;
    if mlen >= 3 && dist >= 1 && mlen <= blen - i {
        let c = cost[i + mlen].saturating_add(match_cost(ll_cost, d_cost, mlen, dist));
        choice = if c < best { mlen } else { choice };
        best = if c < best { c } else { best };
        let mut l = 3usize;
        let stop = if mlen < TRY_SHORT { mlen } else { TRY_SHORT };
        while l < stop {
            let c2 = cost[i + l].saturating_add(match_cost(ll_cost, d_cost, l, dist));
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

/// Optimal parse with one cost iteration; the emission re-verifies every match before writing it.
pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut head = [0u32; 32768];
    let mut prev = [0u32; 32768];
    let mut mlen = [0u32; 32768];
    let mut mdist = [0u32; 32768];
    let mut cost = [0u32; 32769];
    let mut choice = [0u32; 32769];
    let mut ll_freq = [0u32; 287];
    let mut d_freq = [0u32; 31];
    let mut ll_cost = [0u32; 286];
    let mut d_cost = [0u32; 30];
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
        // Count what that path would emit, per block, into the two DEFLATE alphabets.
        let mut s = 0usize;
        while s < 287 {
            ll_freq[s] = 0;
            s += 1;
        }
        s = 0;
        while s < 31 {
            d_freq[s] = 0;
            s += 1;
        }
        let mut k = 0usize;
        while k < blen {
            let ch = choice[k] as usize;
            let d = mdist[k] as usize;
            if ch >= 3 && ch <= 258 && d >= 1 && d <= 32768 && k + ch <= blen {
                let lc = len_code(ch);
                let dc = dist_code(d);
                ll_freq[257 + lc.0] = ll_freq[257 + lc.0].saturating_add(1);
                d_freq[dc.0] = d_freq[dc.0].saturating_add(1);
                ll_freq[286] = ll_freq[286].saturating_add(1);
                d_freq[30] = d_freq[30].saturating_add(1);
                k += ch;
            } else {
                let b = input[pos0 + k] as usize;
                ll_freq[b] = ll_freq[b].saturating_add(1);
                ll_freq[286] = ll_freq[286].saturating_add(1);
                k += 1;
            }
        }
        ll_freq[256] = ll_freq[256].saturating_add(1);
        ll_freq[286] = ll_freq[286].saturating_add(1);
        costs_from(&ll_freq, &mut ll_cost, 286);
        costs_from(&d_freq, &mut d_cost, 30);
        // Backward again, under the learned costs.
        cost[blen] = 0;
        choice[blen] = 0;
        j = blen;
        while j > 0 {
            j -= 1;
            let r = relax2(&cost, &ll_cost, &d_cost, input[pos0 + j], j, mlen[j] as usize, mdist[j] as usize, blen);
            cost[j] = r.0;
            choice[j] = r.1 as u32;
        }
        // Forward: emit the chosen path; `verified` re-checks every match before it is written.
        k = 0;
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
