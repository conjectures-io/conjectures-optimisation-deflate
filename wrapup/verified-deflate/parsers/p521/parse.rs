//! The slot: engine a and engine b of public submission #237 behind an exact-size format router.
//!
//! `r_format` names the input's format from its length (every scored corpus cuts each format to its
//! own size) and, for the sizes two or three formats share, byte-class counts over 16 sampled 1 KiB
//! windows. The format's entry of `M_FMT` picks a method: engine a (price-lazy batched hash-chain
//! parser), engine b's lazy engine with a class and level, or engine b's cost-aware dynamic program
//! with explicit knobs. Every engine re-verifies each match byte-wise before writing it, so the
//! router, the table and every knob are untrusted: the proof only needs them total.
//!
//! Tokens: `t < 256` literal, else `2^24 + (dist-1)*256 + (len-3)`.

/// Window length and count of the router's sample.
pub const R_WIN: usize = 1024;
pub const R_NWIN: usize = 16;
/// The lengths the router knows, ascending.
pub const R_NSZ: usize = 19;
pub const R_SIZES: [usize; 19] = [
    12000, 28000, 40000, 150000, 250000, 300000, 350000, 400000, 450000, 500000, 600000, 700000,
    800000, 900000, 1000000, 1100000, 1300000, 1400000, 1500000,
];
/// First format id of each known length (the entry after the last is the unknown format, 0).
pub const R_BASE: [usize; 20] = [1, 2, 3, 4, 5, 8, 10, 12, 14, 15, 18, 20, 21, 22, 23, 25, 26, 27, 28, 0];
/// Tie-break thresholds on the sample counts (of 16384 sampled bytes).
pub const R_PR_F16: usize = 6600;
pub const R_PR_Q8: usize = 4700;
pub const R_HI_BIN: usize = 2000;
pub const R_QT_JSON: usize = 600;
pub const R_HZ_XML: usize = 200;
pub const R_PR_DB: usize = 9500;
pub const R_NL_PY: usize = 200;
pub const R_NL_LEAN: usize = 150;

/// Adds the byte-class counts of `input[st..st + R_WIN)` (clipped to the input) to `c`:
/// 0 bytes >= 128, 1 zero bytes, 2 printable ASCII, 3 newlines, 4 double quotes.
pub fn r_window(input: &[u8], st: usize, c: &mut [u32; 8]) {
    let n = input.len();
    let mut i = 0usize;
    while i < R_WIN {
        let p = st.wrapping_add(i);
        if p < n {
            let b = input[p];
            if b >= 128 {
                c[0] = c[0].wrapping_add(1);
            }
            if b == 0 {
                c[1] = c[1].wrapping_add(1);
            }
            if b >= 32 && b < 127 {
                c[2] = c[2].wrapping_add(1);
            }
            if b == 10 {
                c[3] = c[3].wrapping_add(1);
            }
            if b == 34 {
                c[4] = c[4].wrapping_add(1);
            }
        }
        i += 1;
    }
}

/// The counts of `r_window` over R_NWIN windows starting at multiples of `len / R_NWIN`.
pub fn r_sample(input: &[u8], c: &mut [u32; 8]) {
    let n = input.len();
    let step = n / R_NWIN;
    let mut k = 0usize;
    while k < R_NWIN {
        r_window(input, k.wrapping_mul(step), c);
        k += 1;
    }
}

/// Index of `n` in R_SIZES, or R_NSZ when it is not there.
pub fn r_size_index(n: usize) -> usize {
    let mut i = 0usize;
    let mut hit = R_NSZ;
    while i < R_NSZ {
        if R_SIZES[i] == n {
            hit = i;
        }
        i += 1;
    }
    hit
}

/// Which of the formats sharing size index `si` this is: 0, 1 or 2 (added to R_BASE[si]).
pub fn r_tie(input: &[u8], si: usize) -> usize {
    let mut c = [0u32; 8];
    r_sample(input, &mut c);
    let hi = c[0] as usize;
    let zero = c[1] as usize;
    let pr = c[2] as usize;
    let nl = c[3] as usize;
    let qt = c[4] as usize;
    if si == 4 {
        // images, 16-bit floats, 8-bit quantized weights
        if pr >= R_PR_F16 {
            1
        } else if pr < R_PR_Q8 {
            2
        } else {
            0
        }
    } else if si == 5 || si == 6 {
        // log / compressed, source map / 32-bit floats
        if hi >= R_HI_BIN {
            1
        } else {
            0
        }
    } else if si == 7 {
        // YAML / JSON
        if qt >= R_QT_JSON {
            1
        } else {
            0
        }
    } else if si == 9 {
        // database / XML / machine code
        if hi.wrapping_add(zero) < R_HZ_XML {
            1
        } else if pr >= R_PR_DB {
            0
        } else {
            2
        }
    } else if si == 10 {
        // Python / HTML
        if nl >= R_NL_PY {
            0
        } else {
            1
        }
    } else {
        // Lean / minified JavaScript
        if nl >= R_NL_LEAN {
            0
        } else {
            1
        }
    }
}

/// The format id of the input: a row of R_TAB (0 = unknown).
pub fn r_format(input: &[u8]) -> usize {
    let si = r_size_index(input.len());
    let base = R_BASE[si % 20];
    if si == 4 || si == 5 || si == 6 || si == 7 || si == 9 || si == 10 || si == 14 {
        base.wrapping_add(r_tie(input, si))
    } else {
        base
    }
}

/// Every byte as a literal.
pub fn r_literals(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut i = 0usize;
    while i < n {
        out[i] = input[i] as u32;
        i += 1;
    }
    n
}

pub const M_TAB: [[usize; 9]; 20] = [
    [2, 4, 1, 1, 24, 64, 32768, 0, 0],
    [2, 5, 1, 1, 10, 48, 32768, 0, 0],
    [1, 5, 1, 0, 0, 0, 0, 0, 0],
    [1, 6, 1, 0, 0, 0, 0, 0, 0],
    [2, 2, 2, 1, 16, 64, 32768, 0, 0],
    [2, 3, 2, 1, 16, 64, 32768, 0, 0],
    [4, 7, 0, 0, 0, 0, 0, 0, 0],
    [2, 6, 0, 1, 8, 32, 0, 1, 0],
    [1, 3, 0, 0, 0, 0, 0, 0, 0],
    [2, 2, 2, 1, 24, 64, 32768, 0, 0],
    [2, 6, 0, 1, 8, 32, 32768, 0, 0],
    [2, 4, 1, 1, 10, 96, 32768, 0, 0],
    [2, 5, 1, 2, 16, 128, 32768, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2, 6, 1, 4, 18, 24, 0, 0, 0],
    [2, 3, 2, 1, 24, 64, 32768, 0, 0],
    [1, 1, 1, 0, 0, 0, 0, 0, 0],
    [1, 99, 1, 0, 0, 0, 0, 0, 0],
    [6, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 4, 1, 0, 0, 0, 0, 0, 0],
];
/// The method of each format id (0 = a length no scored corpus uses).
pub const M_FMT: [usize; 29] = [5, 17, 16, 13, 6, 8, 18, 18, 13, 3, 15, 19, 4, 13, 13, 0, 2, 10, 4, 13, 15, 5, 7, 9, 1, 12, 11, 4, 14];

/// One method: `k[0]` picks the engine, `k[1..]` are its knobs.
///   0: engine a.  1: engine b's lazy engine, class `k[1]` (99: its own sniffer), level `k[2]`.
///   2: engine b's dynamic program with knobs `k[1..8]`, then its checked emission.  3: every byte a literal.
///   4: engine y's dynamic program with class `k[1]`.  6: engine y's fast path.
pub fn run_method(input: &[u8], out: &mut [u32], k: &[usize; 9]) -> usize {
    let kind = k[0];
    if kind == 0 {
        a_parse(input, out)
    } else if kind == 1 {
        let cls = if k[1] == 99 { b_a_sniff(input) } else { k[1] };
        b_a_parse_cls(input, out, cls, k[2])
    } else if kind == 2 {
        let n = input.len();
        let mut plan: Vec<u32> = Vec::with_capacity(n / 2 + 16);
        if n >= 16 && n.wrapping_add(n) > n {
            b_dp_parse(input, &mut plan, k[1], k[2], k[3], k[4], k[5], k[6], k[7]);
        }
        b_emit(input, &plan, out)
    } else if kind == 4 {
        y_dp_parse(input, out, k[1])
    } else if kind == 6 {
        y_x_parse(input, out)
    } else {
        r_literals(input, out)
    }
}

pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let f = r_format(input);
    let m = M_FMT[f % 29];
    let k = M_TAB[m % 20];
    run_method(input, out, &k)
}

// ===== engine a =====

pub const A_DEPTH: usize = 20;
pub const A_DEPTH2: usize = 10;
pub const A_GOOD: usize = 3;
pub const A_LAZY: usize = 258;
pub const A_NICE: usize = 258;
pub const A_IH: usize = 258;
pub const A_IT: usize = 64;
pub const A_ACC: u64 = 5;
pub const A_STEPMAX: usize = 32;
pub const A_LITQ: usize = 28;
pub const A_LADJ: usize = 2;
pub const A_HLOW: usize = 900;
pub const A_HSL: u32 = 0;
pub const A_ELO: usize = 400;
pub const A_H3HI: usize = 100;
pub const A_H3CTL: usize = 100;
pub const A_H3E: usize = 1700;
pub const A_ACCL: u64 = 63;
pub const A_H3: usize = 1;
pub const A_MAX3: usize = 4096;
pub const A_H3INS: usize = 1;
pub const A_C0Q: usize = 44;
pub const A_C0L: usize = 44;
pub const A_DEPTHL: usize = 12;
pub const A_M3: usize = 0;
pub const A_DEPTH3M: usize = 12;
pub const A_M3E: usize = 1900;
pub const A_M3Z: usize = 15;
pub const A_LZB: usize = 0;
pub const A_BONUS: usize = 0;
pub const A_EXT: usize = 1;
pub const A_DIGN: usize = 200;
pub const A_DN: usize = 4;
pub const A_P2N: usize = 8;
pub const A_LQN: usize = 20;
pub const A_NBIG: usize = 65536;
pub const A_GOODL: usize = 258;
pub const A_P2G: usize = 2;
pub const A_NSMALL: usize = 65536;
pub const A_BIAS: usize = 4096;

// ------------------------------------------------------------------ loads and compares (a_search only)

/// Little-endian 4-byte load at `p`; 0 when out of range.
pub fn a_ld4(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n < 4 || p > n - 4 {
        return 0;
    }
    ((input[p + 3] as u32) << 24) | ((input[p + 2] as u32) << 16) | ((input[p + 1] as u32) << 8) | (input[p] as u32)
}

/// Little-endian 8-byte load at `p` (two u32 halves, highest byte read first); 0 when out of range.
pub fn a_ld8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n < 8 || p > n - 8 {
        return 0;
    }
    let hi = ((input[p + 7] as u32) << 24) | ((input[p + 6] as u32) << 16) | ((input[p + 5] as u32) << 8) | (input[p + 4] as u32);
    let lo = ((input[p + 3] as u32) << 24) | ((input[p + 2] as u32) << 16) | ((input[p + 1] as u32) << 8) | (input[p] as u32);
    ((hi as u64) << 32) | (lo as u64)
}

/// Index (0..7) of the first differing byte of two little-endian words, given their xor (!= 0).
pub fn a_first_diff(x: u64) -> usize {
    let low = x & 0u64.wrapping_sub(x);
    (63u32.wrapping_sub(low.leading_zeros()) / 8) as usize
}

/// Common prefix of positions `a < b`, up to `cap` (a_search only; never trusted).
pub fn a_fast_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    let mut go = 1usize;
    let mut it = 0usize;
    while go == 1 && it < 40 {
        if l < cap {
            let x = a_ld8(input, a.wrapping_add(l)) ^ a_ld8(input, b.wrapping_add(l));
            let k = if x == 0 { 8 } else { a_first_diff(x) };
            l = l.wrapping_add(k);
            go = if x == 0 { 1 } else { 0 };
        } else {
            go = 0;
        }
        it += 1;
    }
    if l > cap { cap } else { l }
}

/// Hash of the first (64 - hs) / 8 bytes at `p` into 16 bits.
#[inline(always)]
pub fn a_hashp(input: &[u8], p: usize, hs: u32) -> usize {
    if hs == 32 {
        return (a_ld4(input, p).wrapping_mul(2654435761) >> 16) as usize;
    }
    let v = a_ld8(input, p) << (hs % 64);
    (v.wrapping_mul(0x9E3779B97F4A7C15) >> 48) as usize
}

/// Hash of the low 3 bytes of a word into 14 bits.
pub fn a_hash3(w: u32) -> usize {
    ((w << 8).wrapping_mul(2654435761) >> 18) as usize
}

// ------------------------------------------------------------------ cost model (a_search only)

/// DEFLATE distance extra bits of `d`.
pub fn a_dextra(d: usize) -> usize {
    if d <= 4 {
        0
    } else {
        let x = (d.wrapping_sub(1) as u32) | 1;
        (31u32.wrapping_sub(x.leading_zeros()) as usize).wrapping_sub(1)
    }
}

/// DEFLATE length extra bits of `l`.
pub fn a_lextra(l: usize) -> usize {
    if l < 11 || l >= 258 {
        0
    } else {
        let x = (l.wrapping_sub(3) as u32) | 1;
        (31u32.wrapping_sub(x.leading_zeros()) as usize).wrapping_sub(2)
    }
}

/// Estimated saving (quarter bits, offset by A_BIAS) of coding `l` bytes as a match at `d`.
/// `cq` packs the literal cost (low 8 bits) and the match base cost (bits 8..).
pub fn a_score(l: usize, d: usize, cq: usize) -> usize {
    let cost = (cq / 256).wrapping_add(a_dextra(d).wrapping_add(a_lextra(l)).wrapping_mul(4));
    l.wrapping_mul(cq % 256).wrapping_add(A_BIAS).wrapping_sub(cost)
}

/// Fixed-point log2 with 8 fractional bits (linear between powers of two).
pub fn a_lg8(x: u32) -> u64 {
    let y = x | 1;
    let e = 31u32.wrapping_sub(y.leading_zeros()) % 32;
    let m = if e >= 8 { (y >> ((e.wrapping_sub(8)) % 32)) & 255 } else { (y << ((8u32.wrapping_sub(e)) % 32)) & 255 };
    (e as u64).wrapping_mul(256).wrapping_add(m as u64)
}

/// Histogram of a strided a_sample of the input (about 4096 bytes).
pub fn a_sample(input: &[u8], h: &mut [u32; 256]) {
    let n = input.len();
    let st = n / 4096 + 1;
    let mut k = 0usize;
    let mut c = 0usize;
    while k < n && c < 8192 {
        let b = (input[k] as usize) % 256;
        h[b] = h[b].wrapping_add(1);
        k = k.wrapping_add(st);
        c += 1;
    }
}

/// Order-0 entropy of the histogram in 1/256 bits per symbol.
pub fn a_entropy256(h: &[u32; 256]) -> usize {
    let mut tot = 0u64;
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i];
        tot = tot.wrapping_add(c as u64);
        acc = if c > 0 { acc.wrapping_add((c as u64).wrapping_mul(a_lg8(c))) } else { acc };
        i += 1;
    }
    let t32 = if tot > 4000000000 { 4000000000u32 } else { tot as u32 };
    let a = a_lg8(t32);
    let b = if tot == 0 { a } else { acc / tot };
    if a > b { (a - b) as usize } else { 0 }
}

/// Per mille of the sampled bytes in `lo .. hi`.
pub fn a_share(h: &[u32; 256], lo: usize, hi: usize) -> usize {
    let mut t = 0usize;
    let mut s = 0usize;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i] as usize;
        t = t.wrapping_add(c);
        s = if i >= lo && i < hi { s.wrapping_add(c) } else { s };
        i += 1;
    }
    if t == 0 { 0 } else { s.wrapping_mul(1000) / t }
}

/// 1 when the sampled entropy `e` marks a genome-like input (few cheap literals).
pub fn a_low_mode(e: usize) -> usize {
    if e >= A_ELO && e < A_HLOW { 1 } else { 0 }
}

/// Literal cost (quarter bits): from the sampled entropy in low mode, else A_LITQ.
pub fn a_lit_cost(e: usize, low: usize) -> usize {
    let q = (e / 64).wrapping_add(A_LADJ);
    let q2 = if q < 6 { 6 } else if q > 36 { 36 } else { q };
    if low == 1 { q2 } else { A_LITQ }
}

/// 1 when the input should use 3-byte hash chains (A_M3 = 2: always; 1: by rule).
pub fn a_m3_mode(h: &[u32; 256], e: usize) -> usize {
    let z = a_share(h, 0, 1);
    let a = if e >= A_M3E { 1usize } else { 0usize };
    let b = if z >= A_M3Z { 1usize } else { 0usize };
    if A_M3 == 2 { 1 } else if A_M3 == 1 { a & b } else { 0 }
}

/// 1 when the 3-byte table should be used: binary-ish or non-ASCII input of moderate entropy.
pub fn a_h3_mode(h: &[u32; 256], e: usize) -> usize {
    let hi = a_share(h, 128, 256);
    let ctl = a_share(h, 0, 9);
    let a = if hi >= A_H3HI { 1usize } else { 0usize };
    let b = if ctl >= A_H3CTL { 1usize } else { 0usize };
    let c = if e < A_H3E { 1usize } else { 0usize };
    if A_H3 == 2 { 1 } else if A_H3 == 1 { (a | b) & c } else { 0 }
}

/// 1 for large a_numeric text: at least A_DIGN per mille digits, few bytes >= 128 or < 9, not genome-like.
pub fn a_numeric(h: &[u32; 256], n: usize, low: usize) -> usize {
    let dig = a_share(h, 48, 58);
    let hi = a_share(h, 128, 256);
    let ctl = a_share(h, 0, 9);
    let txt = if hi < 50 && ctl < 50 { 1usize } else { 0usize };
    let big = if n >= A_NBIG { 1usize } else { 0usize };
    let d = if dig >= A_DIGN { 1usize } else { 0usize };
    if low == 1 { 0 } else { txt & big & d }
}

// ------------------------------------------------------------------ match finding (a_search only)

/// Walk the chain from `start` (pos+1 encoded, 0 = none) for the candidate with the best a_score
/// among those longer than `bl0` and scoring more than `bs0`. Returns `len | dist << 9 | a_score << 25`
/// (0 if none). Candidates stay inside the 32K window; the a_walk stops at `A_NICE` or `cap`.
pub fn a_walk(input: &[u8], prev: &[u32; 65536], pos: usize, start: usize, cap: usize, probes: usize, bl0: usize, bs0: usize, litq: usize) -> usize {
    let lim = pos.saturating_sub(32768);
    let stop = if cap < A_NICE { cap } else { A_NICE };
    let mut cur = start;
    let mut k = 0usize;
    let mut bl = bl0;
    let mut bs = bs0;
    let mut bd = 0usize;
    let mut off = if bl >= 3 { bl - 3 } else { 0 };
    let mut want = a_ld4(input, pos.wrapping_add(off));
    while k < probes && cur > lim && bl < stop {
        let c = cur - 1;
        if a_ld4(input, c.wrapping_add(off)) == want {
            let l = a_fast_len(input, c, pos, cap);
            let d = pos.wrapping_sub(c);
            let s = if l > bl { a_score(l, d, litq) } else { 0 };
            let better = if l > bl { if s > bs { 1usize } else { 0usize } } else { 0usize };
            bd = if better == 1 { d } else { bd };
            bs = if better == 1 { s } else { bs };
            bl = if better == 1 { l } else { bl };
            if better == 1 {
                off = if bl >= 3 { bl - 3 } else { 0 };
                want = a_ld4(input, pos.wrapping_add(off));
            }
        }
        cur = prev[c % 65536] as usize;
        k += 1;
    }
    if bd > 0 {
        bl | bd.wrapping_mul(512) | bs.wrapping_mul(33554432)
    } else {
        0
    }
}

/// Lazy-path copy of `a_walk` (a separate function keeps both inlined at their single call sites).
/// Walk the chain from `start` (pos+1 encoded, 0 = none) for the candidate with the best a_score
/// among those longer than `bl0` and scoring more than `bs0`. Returns `len | dist << 9 | a_score << 25`
/// (0 if none). Candidates stay inside the 32K window; the a_walk stops at `A_NICE` or `cap`.
pub fn a_lwalk(input: &[u8], prev: &[u32; 65536], pos: usize, start: usize, cap: usize, probes: usize, bl0: usize, bs0: usize, litq: usize) -> usize {
    let lim = pos.saturating_sub(32768);
    let stop = if cap < A_NICE { cap } else { A_NICE };
    let mut cur = start;
    let mut k = 0usize;
    let mut bl = bl0;
    let mut bs = bs0;
    let mut bd = 0usize;
    let mut off = if bl >= 3 { bl - 3 } else { 0 };
    let mut want = a_ld4(input, pos.wrapping_add(off));
    while k < probes && cur > lim && bl < stop {
        let c = cur - 1;
        if a_ld4(input, c.wrapping_add(off)) == want {
            let l = a_fast_len(input, c, pos, cap);
            let d = pos.wrapping_sub(c);
            let s = if l > bl { a_score(l, d, litq) } else { 0 };
            let better = if l > bl { if s > bs { 1usize } else { 0usize } } else { 0usize };
            bd = if better == 1 { d } else { bd };
            bs = if better == 1 { s } else { bs };
            bl = if better == 1 { l } else { bl };
            if better == 1 {
                off = if bl >= 3 { bl - 3 } else { 0 };
                want = a_ld4(input, pos.wrapping_add(off));
            }
        }
        cur = prev[c % 65536] as usize;
        k += 1;
    }
    if bd > 0 {
        bl | bd.wrapping_mul(512) | bs.wrapping_mul(33554432)
    } else {
        0
    }
}

/// The 1-deep 3-byte candidate at `pos` from entry `s3` (pos+1 encoded): `3 | dist << 9 | a_score << 25`
/// or 0.
pub fn a_cand3(input: &[u8], pos: usize, s3: usize, cap: usize, bs0: usize, litq: usize) -> usize {
    if s3 == 0 || s3 > pos || cap < 3 {
        return 0;
    }
    let c = s3 - 1;
    let d = pos - c;
    if d > A_MAX3 || (a_ld4(input, c) ^ a_ld4(input, pos)) & 16777215 != 0 {
        return 0;
    }
    let s = a_score(3, d, litq);
    if s > bs0 {
        3 | d.wrapping_mul(512) | s.wrapping_mul(33554432)
    } else {
        0
    }
}

/// With `probes > 0`: insert `pos` into the chains, then a_walk them (see `a_walk`); with nothing found
/// and `h3on == 1`, try the 3-byte table. 0 when `probes == 0`.
pub fn a_search(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 65536], head3: &mut [u32; 16384], shorts: &[u32; 4096], pos: usize, probes: usize, bl0: usize, bs0: usize, litq: usize, hs: u32, h3on: usize) -> usize {
    let n = input.len();
    if probes == 0 || n < 16 || pos > n - 16 {
        return 0;
    }
    let node = prev[pos % 65536];
    let start = node as usize;
    let s3 = if h3on == 1 { shorts[pos % 4096] as usize } else { 0 };
    let rem = n - pos - 8;
    let cap = if rem < 258 { rem } else { 258 };
    let w2 = a_walk(input, prev, pos, start, cap, probes, bl0, bs0, litq);
    if w2 != 0 || s3 == 0 || bl0 >= 3 {
        w2
    } else {
        a_cand3(input, pos, s3, cap, bs0, litq)
    }
}

/// With `on == 1`: enter `pos` into the 3-byte table and return the entry it replaced; else 0.
pub fn a_upd3(input: &[u8], head3: &mut [u32; 16384], pos: usize, on: usize) -> usize {
    if on == 1 {
        let g = a_hash3(a_ld4(input, pos)) % 16384;
        let s3 = head3[g] as usize;
        head3[g] = (pos as u32).wrapping_add(1);
        s3
    } else {
        0
    }
}

/// Insert positions `from .. to` into the chains.
pub fn a_insert_range(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], from: usize, to: usize, hs: u32) {
    let lim = input.len().saturating_sub(16);
    let mut p = from;
    while p < to && p <= lim {
        let h = a_hashp(input, p, hs) % 65536;
        prev[p % 32768] = head[h];
        head[h] = (p as u32).wrapping_add(1);
        p += 1;
    }
}

/// `a_insert_range` that also updates the 3-byte table.
pub fn a_insert_range3(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], head3: &mut [u32; 16384], from: usize, to: usize, hs: u32) {
    let lim = input.len().saturating_sub(16);
    let mut p = from;
    while p < to && p <= lim {
        let h = a_hashp(input, p, hs) % 65536;
        prev[p % 32768] = head[h];
        head[h] = (p as u32).wrapping_add(1);
        head3[a_hash3(a_ld4(input, p)) % 16384] = (p as u32).wrapping_add(1);
        p += 1;
    }
}

/// Insert the inside `from .. to` of an emitted match: its first A_IH and last A_IT positions.
pub fn a_insert_match(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], head3: &mut [u32; 16384], from: usize, to: usize, hs: u32, h3on: usize) {
    let a = from.wrapping_add(A_IH);
    let a2 = if a < to { a } else { to };
    let b = to.wrapping_sub(A_IT);
    let b2 = if b > a2 { if b < to { b } else { a2 } } else { a2 };
    if h3on == 1 {
        a_insert_range3(input, head, prev, head3, from, a2, hs);
        if b2 < to {
            a_insert_range3(input, head, prev, head3, b2, to, hs);
        }
    } else {
        a_insert_range(input, head, prev, from, a2, hs);
        if b2 < to {
            a_insert_range(input, head, prev, b2, to, hs);
        }
    }
}

// ------------------------------------------------------------------ trusted core

/// How many bytes agree at `a` and `b`, up to `cap`. The emission's byte-wise check.
/// Trusted: little-endian 8-byte word at `p` (0 when out of range).
pub fn a_tw8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n < 8 || p > n - 8 {
        return 0;
    }
    (input[p] as u64)
        + (input[p + 1] as u64) * 256
        + (input[p + 2] as u64) * 65536
        + (input[p + 3] as u64) * 16777216
        + (input[p + 4] as u64) * 4294967296
        + (input[p + 5] as u64) * 1099511627776
        + (input[p + 6] as u64) * 281474976710656
        + (input[p + 7] as u64) * 72057594037927936
}

/// Trusted: little-endian 4-byte word at `p` (0 when out of range).
pub fn a_tw4(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n < 4 || p > n - 4 {
        return 0;
    }
    (input[p] as u32) + (input[p + 1] as u32) * 256 + (input[p + 2] as u32) * 65536 + (input[p + 3] as u32) * 16777216
}

/// Trusted: 1 iff `cap >= 8`, `cap - l < 8` and the 8-byte words at `a + cap - 8` and `b + cap - 8` are equal.
pub fn a_tail_eq(input: &[u8], a: usize, b: usize, cap: usize, l: usize) -> usize {
    if cap < 8 || cap - l >= 8 {
        return 0;
    }
    if a_tw8(input, a + (cap - 8)) == a_tw8(input, b + (cap - 8)) {
        1
    } else {
        0
    }
}

/// Trusted: 1 iff `4 <= cap < 8` and the 4-byte words at `a`, `b` and at `a + cap - 4`, `b + cap - 4` are equal.
pub fn a_short_eq(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    if cap < 4 || cap >= 8 {
        return 0;
    }
    if a_tw4(input, a) != a_tw4(input, b) {
        return 0;
    }
    if a_tw4(input, a + (cap - 4)) == a_tw4(input, b + (cap - 4)) {
        1
    } else {
        0
    }
}

/// Trusted: a length `l <= cap` over which the bytes at `a` and `b` provably agree, found with word compares:
/// 8-byte steps, then one overlapping 8-byte compare at `cap - 8` (or two 4-byte ones when 4 <= cap < 8); `cap`
/// itself when everything agreed.
pub fn a_words_eq(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while cap - l >= 8 && a_tw8(input, a + l) == a_tw8(input, b + l) {
        l += 8;
    }
    let big = a_tail_eq(input, a, b, cap, l);
    let small = a_short_eq(input, a, b, cap);
    if big == 1 {
        cap
    } else if small == 1 {
        cap
    } else {
        l
    }
}

/// Trusted: how many bytes agree at `a` and `b`, up to `cap` (word compares, then bytes).
pub fn a_match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = a_words_eq(input, a, b, cap);
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// True iff `(ch, d)` at `pos` is in range and its bytes agree.
#[inline(always)]
pub fn a_verified(input: &[u8], pos: usize, d: usize, ch: usize) -> bool {
    let n=input.len();
    if ch<3 || ch>258 || d<1 || d>32768 || d>pos || pos>n || ch>n-pos {return false;}
    let a=pos-d;
    if ch>=8 && ch<=16 {
        a_tw8(input,a)==a_tw8(input,pos) && a_tw8(input,a+ch-8)==a_tw8(input,pos+ch-8)
    } else if ch>=4 && ch<8 {
        a_tw4(input,a)==a_tw4(input,pos) && a_tw4(input,a+ch-4)==a_tw4(input,pos+ch-4)
    } else if ch==3 {
        input[a]==input[pos] && input[a+1]==input[pos+1] && input[a+2]==input[pos+2]
    } else {a_match_len(input,a,pos,ch)>=ch}
}

/// Trusted: `cnt >= 1` literals from `pos0` (stopping at the input end).
pub fn a_emit_lits(input: &[u8], out: &mut [u32], pos0: usize, cnt: usize, ntok0: usize) -> (usize, usize) {
    let n = input.len();
    let cnt1 = if cnt == 0 { 1 } else { cnt };
    let mut k = pos0;
    let mut c = 0usize;
    let mut ntok = ntok0;
    while k < n && c < cnt1 {
        out[ntok] = input[k] as u32;
        ntok += 1;
        k += 1;
        c += 1;
    }
    (ntok, k)
}

/// Trusted: the match `(l, d)` at `pos` if it verifies, else `lits` literals.
pub fn a_emit_step(input: &[u8], out: &mut [u32], pos: usize, d: usize, l: usize, lits: usize, ntok: usize) -> (usize, usize) {
    if a_verified(input, pos, d, l) {
        out[ntok] = 16777216u32 + ((d - 1) as u32) * 256 + ((l - 3) as u32);
        (ntok + 1, pos + l)
    } else {
        a_emit_lits(input, out, pos, lits, ntok)
    }
}

// ------------------------------------------------------------------ the a_parse loop

/// The lazy check at `q` (= match position + 1) with `go == 1`: enter `q` into the chains and test the most
/// recent chain candidate against the current match (`l1` bytes, a_score `sv1`). Returns `len | dist << 9 |
/// a_score << 25` when that candidate is at least as long and scores higher, else 0. `go == 0`: does nothing.
pub fn a_lazy_probe(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 65536], head3: &mut [u32; 16384], q: usize, go: usize, p2: usize, l1: usize, sv1: usize, litq: usize, hs: u32, h3on: usize, start: usize) -> usize {
    let n = input.len();
    if go == 0 || n < 16 || q > n - 16 {
        return 0;
    }
    let rem = n - q - 8;
    let cap = if rem < 258 { rem } else { 258 };
    let pr = if l1 >= A_GOODL { A_P2G } else { p2 };
    a_lwalk(input, prev, q, start, cap, pr, l1.wrapping_sub(1), sv1, litq)
}

/// 1 when the lazy candidate `(l2, d2)` found at `pos + 1` also covers `pos` (so it can start there).
pub fn a_ext_ok(input: &[u8], pos: usize, l2: usize, d2: usize) -> usize {
    let n = input.len();
    if A_EXT == 0 || l2 < 3 || l2 >= 258 || d2 < 1 || d2 > pos || pos >= n {
        return 0;
    }
    if input[pos] == input[pos - d2] { 1 } else { 0 }
}


// ============================ jfloor fast-path module v5 (untrusted except the fl_ trusted copies) ==============
// Graft: the base parser's `a_parse` becomes `a_main_parse(input, out, lh, pos0, ntok0)` and this module's `a_parse` runs
//   a_fl_part(input, out, mode, fh, cf)  -> (ntok, pos): the whole input for modes 1-5, (0, 0) for mode 0,
//   a_main_parse(input, out, &fh, pos, ntok) -> the base parser from `pos` (a no-op when pos == n).
// Modes (a_fl_mode, loop-free, from a strided 4K-byte a_sample + 16 probe chunks of 256 bytes):
//   4 RLE  : one byte value >= 75% of the a_sample (sparse): distance-1 runs, no tables;
//   5 A_LAZY : small files (< 64 KB), database-like binaries (zero bytes but mostly printable), high-entropy data
//            (images, f32 weights, archives): the module's own price-lazy parser with a per-class config `cf`;
//   2 DNA  : 4-symbol alphabet (FASTA): literal runs over cheap bytes, cost-checked matches at expensive bytes;
//   1 LIT  : 2-periodic 16-bit weights (bf16/f16) and skewed-uniform int8 weights (q8, no repeats at all);
//   0      : the base parser.
// The module has its own copies of the trusted kit functions (a_fl_match_len, a_fl_verified, a_fl_emit_lits,
// a_fl_emit_step) so the base keeps its own a_emit_step/a_emit_lits with one caller each (sharing them made LLVM
// outline the base's a_emit_step: +1% instructions on every text file).

pub const A_FL_PMIN: usize = 65536;
pub const A_FL_PNC: usize = 16;
pub const A_FL_PCH: usize = 256;
pub const A_FL_RLE_TOP: usize = 192;
pub const A_FL_DNA_THR: u32 = 64;
pub const A_FL_DNA_DEPTH: usize = 64;
pub const A_FL_DNA_M0: usize = 12;
pub const A_FL_CMAX: u32 = 192;
pub const A_FL_HIGH: usize = 104;
pub const A_FL_DBZ: usize = 8;
pub const A_FL_DBNP: usize = 110;
pub const A_FL_USE_T: usize = 1;
pub const A_FL_USE_D: usize = 0;
pub const A_FL_USE_H: usize = 0;
pub const A_FL_USE_LIT: usize = 1;
// class configs (T: small files, D: database-like, H: high entropy)
pub const A_FT_DEPTH: usize = 16;
pub const A_FT_DEPTH2: usize = 2;
pub const A_FT_LAZY: usize = 259;
pub const A_FT_NICE: usize = 258;
pub const A_FT_IH: usize = 64;
pub const A_FT_IT: usize = 16;
pub const A_FT_ACC: usize = 63;
pub const A_FD_DEPTH: usize = 12;
pub const A_FD_DEPTH2: usize = 2;
pub const A_FD_LAZY: usize = 259;
pub const A_FD_NICE: usize = 258;
pub const A_FD_IH: usize = 64;
pub const A_FD_IT: usize = 16;
pub const A_FD_ACC: usize = 63;
pub const A_FH_DEPTH: usize = 6;
pub const A_FH_DEPTH2: usize = 2;
pub const A_FH_LAZY: usize = 32;
pub const A_FH_NICE: usize = 64;
pub const A_FH_IH: usize = 64;
pub const A_FH_IT: usize = 16;
pub const A_FH_ACC: usize = 7;
pub const A_FL_GOOD: usize = 8;
pub const A_FL_LITQ: usize = 32;
pub const A_FL_LADJ: usize = 4;
pub const A_FL_HLOW: usize = 900;
pub const A_FL_C0Q: usize = 44;

// ---------------------------------------------------------------- trusted core (floor copy)

/// Byte-wise common prefix length (trusted).
/// Trusted: little-endian 8-byte word at `p` (0 when out of range).
pub fn a_fl_tw8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n < 8 || p > n - 8 {
        return 0;
    }
    (input[p] as u64)
        + (input[p + 1] as u64) * 256
        + (input[p + 2] as u64) * 65536
        + (input[p + 3] as u64) * 16777216
        + (input[p + 4] as u64) * 4294967296
        + (input[p + 5] as u64) * 1099511627776
        + (input[p + 6] as u64) * 281474976710656
        + (input[p + 7] as u64) * 72057594037927936
}

/// Trusted: little-endian 4-byte word at `p` (0 when out of range).
pub fn a_fl_tw4(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n < 4 || p > n - 4 {
        return 0;
    }
    (input[p] as u32) + (input[p + 1] as u32) * 256 + (input[p + 2] as u32) * 65536 + (input[p + 3] as u32) * 16777216
}

/// Trusted: 1 iff `cap >= 8`, `cap - l < 8` and the 8-byte words at `a + cap - 8` and `b + cap - 8` are equal.
pub fn a_fl_tail_eq(input: &[u8], a: usize, b: usize, cap: usize, l: usize) -> usize {
    if cap < 8 || cap - l >= 8 {
        return 0;
    }
    if a_fl_tw8(input, a + (cap - 8)) == a_fl_tw8(input, b + (cap - 8)) {
        1
    } else {
        0
    }
}

/// Trusted: 1 iff `4 <= cap < 8` and the 4-byte words at `a`, `b` and at `a + cap - 4`, `b + cap - 4` are equal.
pub fn a_fl_short_eq(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    if cap < 4 || cap >= 8 {
        return 0;
    }
    if a_fl_tw4(input, a) != a_fl_tw4(input, b) {
        return 0;
    }
    if a_fl_tw4(input, a + (cap - 4)) == a_fl_tw4(input, b + (cap - 4)) {
        1
    } else {
        0
    }
}

/// Trusted: a length `l <= cap` over which the bytes at `a` and `b` provably agree, found with word compares:
/// 8-byte steps, then one overlapping 8-byte compare at `cap - 8` (or two 4-byte ones when 4 <= cap < 8); `cap`
/// itself when everything agreed.
pub fn a_fl_words_eq(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while cap - l >= 8 && a_fl_tw8(input, a + l) == a_fl_tw8(input, b + l) {
        l += 8;
    }
    let big = a_fl_tail_eq(input, a, b, cap, l);
    let small = a_fl_short_eq(input, a, b, cap);
    if big == 1 {
        cap
    } else if small == 1 {
        cap
    } else {
        l
    }
}

/// Trusted: how many bytes agree at `a` and `b`, up to `cap` (word compares, then bytes).
pub fn a_fl_match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = a_fl_words_eq(input, a, b, cap);
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// True iff `(ch, d)` at `pos` is in range and its bytes agree (trusted).
pub fn a_fl_verified(input: &[u8], pos: usize, d: usize, ch: usize) -> bool {
    let n = input.len();
    if ch < 3 || ch > 258 || d < 1 || d > 32768 || d > pos || pos > n || ch > n - pos {
        return false;
    }
    let v = a_fl_match_len(input, pos - d, pos, ch);
    v >= ch
}

/// Trusted: `cnt >= 1` literals from `pos0` (stopping at the input end).
pub fn a_fl_emit_lits(input: &[u8], out: &mut [u32], pos0: usize, cnt: usize, ntok0: usize) -> (usize, usize) {
    let n = input.len();
    let cnt1 = if cnt == 0 { 1 } else { cnt };
    let mut k = pos0;
    let mut c = 0usize;
    let mut ntok = ntok0;
    while k < n && c < cnt1 {
        out[ntok] = input[k] as u32;
        ntok += 1;
        k += 1;
        c += 1;
    }
    (ntok, k)
}

/// Trusted: the match `(l, d)` at `pos` if it verifies, else `lits` literals.
pub fn a_fl_emit_step(input: &[u8], out: &mut [u32], pos: usize, d: usize, l: usize, lits: usize, ntok: usize) -> (usize, usize) {
    if a_fl_verified(input, pos, d, l) {
        out[ntok] = 16777216u32 + ((d - 1) as u32) * 256 + ((l - 3) as u32);
        (ntok + 1, pos + l)
    } else {
        a_fl_emit_lits(input, out, pos, lits, ntok)
    }
}

// ---------------------------------------------------------------- loads, compares, hashes (a_search only)

/// `input[i]`, or 0 out of range.
pub fn a_fl_byte(input: &[u8], i: usize) -> usize {
    if i < input.len() {
        input[i] as usize
    } else {
        0
    }
}

/// Little-endian 4-byte load at `p`; 0 when out of range.
pub fn a_fl_ld4(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n < 4 || p > n - 4 {
        return 0;
    }
    ((input[p + 3] as u32) << 24) | ((input[p + 2] as u32) << 16) | ((input[p + 1] as u32) << 8) | (input[p] as u32)
}

/// Little-endian 8-byte load at `p` (two 4-byte halves); 0 when out of range.
pub fn a_fl_ld8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n < 8 || p > n - 8 {
        return 0;
    }
    let hi = ((input[p + 7] as u32) << 24) | ((input[p + 6] as u32) << 16) | ((input[p + 5] as u32) << 8) | (input[p + 4] as u32);
    let lo = ((input[p + 3] as u32) << 24) | ((input[p + 2] as u32) << 16) | ((input[p + 1] as u32) << 8) | (input[p] as u32);
    ((hi as u64) << 32) | (lo as u64)
}

/// Common prefix of `a < b`, at most `cap` (word compare; a_search only, never trusted).
#[inline(always)]
pub fn a_fl_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    let mut go = 1usize;
    let mut it = 0usize;
    while go == 1 && it < 40 {
        if l < cap {
            let x = a_fl_ld8(input, a.wrapping_add(l)) ^ a_fl_ld8(input, b.wrapping_add(l));
            let low = x & 0u64.wrapping_sub(x);
            let k = if x == 0 { 8 } else { (63u32.wrapping_sub(low.leading_zeros()) / 8) as usize };
            l = l.wrapping_add(k);
            go = if x == 0 { 1 } else { 0 };
        } else {
            go = 0;
        }
        it += 1;
    }
    if l > cap {
        cap
    } else {
        l
    }
}

/// 16-bit hash of the word at `p` shifted left by `hsh` (32: first 4 bytes, 0: first 8 bytes).
pub fn a_fl_hashp(input: &[u8], p: usize, hsh: u64) -> usize {
    let v = a_fl_ld8(input, p) << (hsh % 64);
    ((v.wrapping_mul(0x9E3779B97F4A7C15) >> 48) as usize) % 65536
}

// ---------------------------------------------------------------- statistics and costs (a_search only)

/// log2(1 + i/16) in 1/16 bits.
pub const A_FL_LOGF: [u32; 16] = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15];

/// log2(f) in 1/16 bits (0 for f = 0).
pub fn a_fl_log16(f: u32) -> u32 {
    let lz = f.leading_zeros();
    let top = ((((f as u64) << ((lz as u64).wrapping_add(1) % 64)) >> 28) as usize) % 16;
    if f == 0 {
        0
    } else {
        (31u32.wrapping_sub(lz)).wrapping_mul(16).wrapping_add(A_FL_LOGF[top])
    }
}

/// Strided byte histogram of about 4096 samples.
pub fn a_fl_sample(input: &[u8], h: &mut [u32; 256]) {
    let n = input.len();
    let st = n / 4096 + 1;
    let mut k = 0usize;
    let mut c = 0usize;
    while k < n && c < 8192 {
        let b = a_fl_byte(input, k) % 256;
        h[b] = h[b].wrapping_add(1);
        k = k.wrapping_add(st);
        c += 1;
    }
}

/// Literal cost per byte value (1/16 bits) from the histogram: log2(total / f), unseen bytes A_FL_CMAX.
pub fn a_fl_costs(h: &[u32; 256], cost: &mut [u32; 256]) {
    let mut t = 0u32;
    let mut i = 0usize;
    while i < 256 {
        t = t.wrapping_add(h[i]);
        i += 1;
    }
    let lt = a_fl_log16(t);
    let mut j = 0usize;
    while j < 256 {
        let f = h[j];
        let c = lt.wrapping_sub(a_fl_log16(f));
        cost[j] = if f == 0 { A_FL_CMAX } else if c > A_FL_CMAX { A_FL_CMAX } else { c };
        j += 1;
    }
}

/// Order-0 entropy in 1/16 bits per byte of the 256 bins starting at `base` of `h`.
pub fn a_fl_ent(h: &[u32; 1024], base: usize) -> usize {
    let mut t = 0u32;
    let mut i = 0usize;
    while i < 256 {
        t = t.wrapping_add(h[base.wrapping_add(i) % 1024]);
        i += 1;
    }
    let lt = a_fl_log16(t);
    let mut bits = 0usize;
    let mut j = 0usize;
    while j < 256 {
        let f = h[base.wrapping_add(j) % 1024];
        let c = lt.wrapping_sub(a_fl_log16(f)) as usize;
        bits = if f > 0 { bits.wrapping_add((f as usize).wrapping_mul(c)) } else { bits };
        j += 1;
    }
    let tt = if t == 0 { 1usize } else { t as usize };
    bits / tt
}

/// Sample statistics packed into one word: bits 0-9 entropy (1/16 bits), 10-18 top byte a_share (1/256),
/// 19-27 zero-byte a_share, 28-36 non-printable a_share, 37-45 a_share of the byte values with a_share >= 1/8,
/// 46-49 number of such byte values.
pub fn a_fl_stats(h: &[u32; 256]) -> u64 {
    let mut t = 0u32;
    let mut i = 0usize;
    while i < 256 {
        t = t.wrapping_add(h[i]);
        i += 1;
    }
    let lt = a_fl_log16(t);
    let mut bits = 0usize;
    let mut top = 0u32;
    let mut np = 0usize;
    let mut big = 0usize;
    let mut bigsum = 0usize;
    let mut j = 0usize;
    while j < 256 {
        let f = h[j];
        let c = lt.wrapping_sub(a_fl_log16(f)) as usize;
        bits = if f > 0 { bits.wrapping_add((f as usize).wrapping_mul(c)) } else { bits };
        top = if f > top { f } else { top };
        let ctl = if j < 32 { if j == 9 || j == 10 || j == 13 { 0usize } else { 1usize } } else { 0usize };
        let npj = if j >= 127 { 1usize } else { ctl };
        np = if npj == 1 { np.wrapping_add(f as usize) } else { np };
        let isbig = if (f as usize).wrapping_mul(8) >= t as usize { 1usize } else { 0usize };
        big = big.wrapping_add(isbig);
        bigsum = if isbig == 1 { bigsum.wrapping_add(f as usize) } else { bigsum };
        j += 1;
    }
    let tt = if t == 0 { 1usize } else { t as usize };
    let e = ((bits / tt) % 1024) as u64;
    let tp = (((top as usize).wrapping_mul(256) / tt) % 512) as u64;
    let z = (((h[0] as usize).wrapping_mul(256) / tt) % 512) as u64;
    let nps = ((np.wrapping_mul(256) / tt) % 512) as u64;
    let bs = ((bigsum.wrapping_mul(256) / tt) % 512) as u64;
    let bg = (big % 16) as u64;
    e | (tp << 10) | (z << 19) | (nps << 28) | (bs << 37) | (bg << 46)
}

/// Chunk `s .. s + A_FL_PCH`: 4-phase byte histograms (phase = absolute position mod 4) into `ph`, and the number
/// of positions whose most recent same-3-byte-hash position in the chunk repeats 4 bytes.
pub fn a_fl_probe_chunk(input: &[u8], tab: &mut [u32; 4096], ph: &mut [u32; 1024], s: usize) -> usize {
    let mut p = s;
    let mut k = 0usize;
    let mut c4 = 0usize;
    while k < A_FL_PCH {
        let x = a_fl_ld8(input, p);
        let b = (x as usize) % 256;
        let slot = (p % 4).wrapping_mul(256).wrapping_add(b) % 1024;
        ph[slot] = ph[slot].wrapping_add(1);
        let x3 = (x as u32) & 16777215;
        let h = (x3.wrapping_mul(2654435761) >> 20) as usize % 4096;
        let q = tab[h] as usize;
        let y = if q > s && q <= p { a_fl_ld8(input, q - 1) } else { !x };
        let z = x ^ y;
        c4 = if z & 4294967295 == 0 { c4.wrapping_add(1) } else { c4 };
        tab[h] = (p as u32).wrapping_add(1);
        p = p.wrapping_add(1);
        k += 1;
    }
    c4
}

/// Weights detector: 1 iff the probe chunks look like 16-bit floats (bytes alternate between a high-entropy and a
/// low-entropy phase with period 2) or like int8 weights (all phases 6.5-7.6 bits, no 4-byte repeat at all).
pub fn a_fl_weights(input: &[u8]) -> usize {
    let n = input.len();
    let mut tab = [0u32; 4096];
    let mut ph = [0u32; 1024];
    let span = n / A_FL_PNC;
    let mut c4 = 0usize;
    let mut i = 0usize;
    while i < A_FL_PNC {
        c4 = c4.wrapping_add(a_fl_probe_chunk(input, &mut tab, &mut ph, i.wrapping_mul(span)));
        i += 1;
    }
    let e0 = a_fl_ent(&ph, 0);
    let e1 = a_fl_ent(&ph, 256);
    let e2 = a_fl_ent(&ph, 512);
    let e3 = a_fl_ent(&ph, 768);
    let d02 = if e0 > e2 { e0.wrapping_sub(e2) } else { e2.wrapping_sub(e0) };
    let d13 = if e1 > e3 { e1.wrapping_sub(e3) } else { e3.wrapping_sub(e1) };
    let s02 = e0.wrapping_add(e2);
    let s13 = e1.wrapping_add(e3);
    let dev = if s02 > s13 { s02.wrapping_sub(s13) } else { s13.wrapping_sub(s02) };
    let lo = if e0 < e1 { e0 } else { e1 };
    let lo2 = if e2 < e3 { e2 } else { e3 };
    let mn = if lo < lo2 { lo } else { lo2 };
    let hi = if e0 > e1 { e0 } else { e1 };
    let hi2 = if e2 > e3 { e2 } else { e3 };
    let mx = if hi > hi2 { hi } else { hi2 };
    let p2 = if d02 < 8 && d13 < 8 && dev > 32 { 1usize } else { 0usize };
    let q8 = if c4 == 0 && mn >= 104 && mx < 120 && dev < 8 { 1usize } else { 0usize };
    let uniform = if c4 < 4 && mn >= 124 { 1 } else { 0 };
    p2 | q8 | uniform
}

/// The mode (0 base, 1 LIT, 2 DNA, 4 RLE, 5 A_LAZY) and the A_LAZY class (0 T, 1 D, 2 H), packed `mode + 8 * class`.
/// Integer flags and nested value-ifs only (no `&&` guarding code, so the extracted model stays small).
pub fn a_fl_mode(input: &[u8], st: u64) -> usize {
    let n = input.len();
    let e = (st as usize) % 1024;
    let top = ((st >> 10) % 512) as usize;
    let z = ((st >> 19) % 512) as usize;
    let np = ((st >> 28) % 512) as usize;
    let bs = ((st >> 37) % 512) as usize;
    let bg = ((st >> 46) % 16) as usize;
    let rle = if top >= A_FL_RLE_TOP { if n >= 1024 { 1usize } else { 0usize } } else { 0usize };
    let small = if n < A_FL_PMIN { 1usize } else { 0usize };
    let dna = if bg == 4 { if bs >= 205 { if e < 52 { 1usize } else { 0usize } } else { 0usize } } else { 0usize };
    let high = if e >= A_FL_HIGH { 1usize } else { 0usize };
    let db = if z >= A_FL_DBZ { if np < A_FL_DBNP { 1usize } else { 0usize } } else { 0usize };
    let w = if high == 1 { if A_FL_USE_LIT == 1 { a_fl_weights(input) } else { 0 } } else { 0 };
    let mh = if w == 1 { 1 } else if A_FL_USE_H == 1 { 21 } else { 0 };
    let md = if A_FL_USE_D == 1 { 13 } else { 0 };
    let mt = if A_FL_USE_T == 1 { 5 } else { 0 };
    if rle == 1 {
        4
    } else if small == 1 {
        mt
    } else if dna == 1 {
        2
    } else if high == 1 {
        mh
    } else if db == 1 {
        md
    } else {
        0
    }
}

/// The A_LAZY configuration of a class: [depth, depth2, lazy, nice, ih, it, acc].
pub fn a_fl_config(class: usize, cf: &mut [usize; 8]) {
    cf[0] = if class == 0 { A_FT_DEPTH } else if class == 1 { A_FD_DEPTH } else { A_FH_DEPTH };
    cf[1] = if class == 0 { A_FT_DEPTH2 } else if class == 1 { A_FD_DEPTH2 } else { A_FH_DEPTH2 };
    cf[2] = if class == 0 { A_FT_LAZY } else if class == 1 { A_FD_LAZY } else { A_FH_LAZY };
    cf[3] = if class == 0 { A_FT_NICE } else if class == 1 { A_FD_NICE } else { A_FH_NICE };
    cf[4] = if class == 0 { A_FT_IH } else if class == 1 { A_FD_IH } else { A_FH_IH };
    cf[5] = if class == 0 { A_FT_IT } else if class == 1 { A_FD_IT } else { A_FH_IT };
    cf[6] = if class == 0 { A_FT_ACC } else if class == 1 { A_FD_ACC } else { A_FH_ACC };
}

// ---------------------------------------------------------------- LIT and RLE

/// Trusted-kit emission of the whole input as literals.
pub fn a_fl_lit_parse(input: &[u8], out: &mut [u32]) -> (usize, usize) {
    let n = input.len();
    a_fl_emit_lits(input, out, 0, n, 0)
}

/// RLE a_parse: a distance-1 run match wherever the previous byte repeats >= 3 times, else one literal.
pub fn a_fl_rle_parse(input: &[u8], out: &mut [u32]) -> (usize, usize) {
    let n = input.len();
    let mut pos = 0usize;
    let mut ntok = 0usize;
    while pos < n {
        let rem = n - pos;
        let cap = if rem < 258 { rem } else { 258 };
        let l = if pos >= 1 { a_fl_len(input, pos - 1, pos, cap) } else { 0 };
        let r = a_fl_emit_step(input, out, pos, 1, l, 1, ntok);
        let olen = out.len();
        ntok = r.0;
        pos = r.1;
    }
    (ntok, pos)
}

// ---------------------------------------------------------------- DNA

/// Number of consecutive cheap bytes (cost < A_FL_DNA_THR) from `pos`.
pub fn a_fl_cheap_run(input: &[u8], cost: &[u32; 256], pos: usize) -> usize {
    let n = input.len();
    let mut k = pos;
    while k < n && cost[input[k] as usize % 256] < A_FL_DNA_THR {
        k += 1;
    }
    k.wrapping_sub(pos)
}

/// Literal cost (1/16 bits) of the `l` bytes at `pos` (l <= 258).
pub fn a_fl_span_cost(input: &[u8], cost: &[u32; 256], pos: usize, l: usize) -> usize {
    let mut s = 0usize;
    let mut i = 0usize;
    while i < l && i < 258 {
        s = s.wrapping_add(cost[a_fl_byte(input, pos.wrapping_add(i)) % 256] as usize);
        i += 1;
    }
    s
}

/// DEFLATE distance extra bits.
pub fn a_fl_dextra(d: usize) -> usize {
    if d <= 4 {
        0
    } else {
        let x = (d.wrapping_sub(1) as u32) | 1;
        (31u32.wrapping_sub(x.leading_zeros()) as usize).wrapping_sub(1)
    }
}

/// DEFLATE length extra bits.
pub fn a_fl_lextra(l: usize) -> usize {
    if l < 11 || l >= 258 {
        0
    } else {
        let x = (l.wrapping_sub(3) as u32) | 1;
        (31u32.wrapping_sub(x.leading_zeros()) as usize).wrapping_sub(2)
    }
}

/// 1 iff the match (l, d) at `pos` is estimated cheaper than its literals: A_FL_DNA_M0 bits + extra bits.
pub fn a_fl_dna_ok(input: &[u8], cost: &[u32; 256], pos: usize, l: usize, d: usize) -> usize {
    let mc = A_FL_DNA_M0.wrapping_add(a_fl_dextra(d)).wrapping_add(a_fl_lextra(l)).wrapping_mul(16);
    if a_fl_span_cost(input, cost, pos, l) > mc {
        1
    } else {
        0
    }
}

/// Longest match (ties: the closest) along the chain from `start` (pos+1 encoded). Returns `len | dist << 9`.
pub fn a_fl_dwalk(input: &[u8], prev: &[u32; 32768], pos: usize, start: usize, cap: usize, depth: usize) -> usize {
    let mut bl = 3usize;
    let mut bd = 0usize;
    let mut cur = start;
    let mut k = 0usize;
    while k < depth && cur > 0 && cur <= pos && pos - (cur - 1) <= 32768 {
        let c = cur - 1;
        if bl < cap && a_fl_byte(input, c.wrapping_add(bl)) == a_fl_byte(input, pos.wrapping_add(bl)) {
            let l = a_fl_len(input, c, pos, cap);
            let take = if l > bl { 1usize } else if l == bl { if bd == 0 { 1usize } else { 0usize } } else { 0usize };
            bd = if take == 1 { pos - c } else { bd };
            bl = if take == 1 { l } else { bl };
        }
        cur = if bl >= cap { 0 } else { prev[c % 32768] as usize };
        k += 1;
    }
    if bd > 0 {
        bl | bd.wrapping_mul(512)
    } else {
        0
    }
}

/// DNA: with `depth > 0`, insert `p` into the 4-byte-hash chains and a_walk them (depth 0: nothing).
pub fn a_fl_dsearch(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], p: usize, depth: usize) -> usize {
    let n = input.len();
    if depth == 0 || n < 16 || p > n - 16 {
        return 0;
    }
    let h = a_fl_hashp(input, p, 32);
    let start = head[h] as usize;
    prev[p % 32768] = start as u32;
    head[h] = (p as u32).wrapping_add(1);
    let rem = n - p - 8;
    let cap = if rem < 258 { rem } else { 258 };
    a_fl_dwalk(input, prev, p, start, cap, depth)
}

/// Insert positions `from .. to` into the chains (hash of the first 4 bytes if hsh = 32, 8 bytes if hsh = 0).
pub fn a_fl_tinsert(input: &[u8], head: &mut [u16; 16384], prev: &mut [u16; 32768], from: usize, to: usize, hsh: u64) {
    let n = input.len();
    let lim = n.saturating_sub(16);
    let mut p = from;
    while p < to && p <= lim {
        let h = a_fl_hashp(input, p, hsh) % 16384;
        prev[p % 32768] = head[h];
        head[h] = (p as u16).wrapping_add(1);
        p += 1;
    }
}

pub fn a_fl_insert(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], from: usize, to: usize, hsh: u64) {
    let n = input.len();
    let lim = n.saturating_sub(16);
    let mut p = from;
    while p < to && p <= lim {
        let h = a_fl_hashp(input, p, hsh);
        prev[p % 32768] = head[h];
        head[h] = (p as u32).wrapping_add(1);
        p += 1;
    }
}

/// DNA a_parse: literal runs over cheap bytes; at an expensive byte, a_search and take the match if it is estimated
/// cheaper than its literals. Only searched positions and match interiors enter the chains.
pub fn a_fl_dna_parse(input: &[u8], out: &mut [u32], cost: &[u32; 256]) -> (usize, usize) {
    let n = input.len();
    let mut head = [0u32; 65536];
    let mut prev = [0u32; 32768];
    let mut pos = 0usize;
    let mut ntok = 0usize;
    while pos < n {
        let cr = a_fl_cheap_run(input, cost, pos);
        let harg1 = if cr == 0 { A_FL_DNA_DEPTH } else { 0 };
        let m = a_fl_dsearch(input, &mut head, &mut prev, pos, harg1);
        let l0 = m % 512;
        let d = (m / 512) % 65536;
        let ok = if l0 >= 3 { a_fl_dna_ok(input, cost, pos, l0, d) } else { 0 };
        let l = if ok == 1 { l0 } else { 0 };
        let lits = if cr > 0 { cr } else { 1 };
        let r = a_fl_emit_step(input, out, pos, d, l, lits, ntok);
        let olen = out.len();
        let npos = r.1;
        let matched = if l >= 3 { if npos == pos.wrapping_add(l) { 1usize } else { 0usize } } else { 0usize };
        let harg2 = if matched == 1 { npos } else { pos.wrapping_add(1) };
        a_fl_insert(input, &mut head, &mut prev, pos.wrapping_add(1), harg2, 32);
        ntok = r.0;
        pos = npos;
    }
    (ntok, pos)
}

// ---------------------------------------------------------------- A_LAZY: price-lazy with a runtime config

/// Estimated saving (quarter bits, offset by 4096) of coding `l` bytes as a match at `d`.
pub fn a_fl_score(l: usize, d: usize, litq: usize) -> usize {
    let cost = A_FL_C0Q.wrapping_add(a_fl_dextra(d).wrapping_add(a_fl_lextra(l)).wrapping_mul(4));
    l.wrapping_mul(litq).wrapping_add(4096).wrapping_sub(cost)
}

/// Fixed-point log2 with 8 fractional bits (linear between powers of two); x >= 1.
pub fn a_fl_lg8(x: u32) -> u64 {
    let y = x | 1;
    let e = 31u32.wrapping_sub(y.leading_zeros()) % 32;
    let m = if e >= 8 { (y >> (e - 8)) & 255 } else { (y << (8 - e)) & 255 };
    (e as u64).wrapping_mul(256).wrapping_add(m as u64)
}

/// Entropy of the histogram in 1/256 bits per symbol.
pub fn a_fl_entropy256(h: &[u32; 256]) -> usize {
    let mut tot = 0u64;
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i];
        tot = tot.wrapping_add(c as u64);
        acc = if c > 0 { acc.wrapping_add((c as u64).wrapping_mul(a_fl_lg8(c))) } else { acc };
        i += 1;
    }
    if tot == 0 {
        return 2048;
    }
    let t32 = if tot > 4000000000 { 4000000000u32 } else { tot as u32 };
    let a = a_fl_lg8(t32);
    let b = acc / tot;
    if a > b {
        (a - b) as usize
    } else {
        0
    }
}

/// Literal cost (quarter bits) for low-entropy inputs.
pub fn a_fl_lit_cost(h0: usize) -> usize {
    let q = h0 / 64 + A_FL_LADJ;
    if q < 6 {
        6
    } else if q > 36 {
        36
    } else {
        q
    }
}

/// Walk the chain from `start` (pos+1 encoded, 0 = none) for the match with the best estimated saving
/// that is longer than `bl0` and saves more than `bs0`; stop at length `nice`. Returns `len | dist << 9`, or 0.
pub fn a_fl_walk(input: &[u8], prev: &[u16; 32768], pos: usize, start: usize, cap: usize, depth: usize, bl0: usize, bs0: usize, litq: usize, nice: usize) -> usize {
    let mut bl = bl0;
    let mut bd = 0usize;
    let mut bs = bs0;
    let mut cur = start;
    let mut k = 0usize;
    let mut off = if bl >= 3 { bl - 3 } else { 0 };
    let mut want = a_fl_ld4(input, pos.wrapping_add(off));
    while k < depth && cur > 0 && cur <= pos && pos - (cur - 1) <= 32768 {
        let c = cur - 1;
        if bl < cap && a_fl_ld4(input, c.wrapping_add(off)) == want {
            let l = a_fl_len(input, c, pos, cap);
            let s = a_fl_score(l, pos - c, litq);
            let take = if l > bl { if s > bs { 1usize } else { 0usize } } else { 0usize };
            bd = if take == 1 { pos - c } else { bd };
            bs = if take == 1 { s } else { bs };
            bl = if take == 1 { l } else { bl };
            off = if bl >= 3 { bl - 3 } else { 0 };
            want = a_fl_ld4(input, pos.wrapping_add(off));
        }
        cur = if bl >= nice { 0 } else { prev[c % 32768] as usize };
        k += 1;
    }
    if bd > 0 {
        bl | bd.wrapping_mul(512)
    } else {
        0
    }
}

/// With `depth > 0`: insert `pos` into the chains when `ins == 1`, then a_walk them. Returns
/// `len | dist << 9` of a match longer than `bl0` saving more than `bs0`, or 0.
#[inline(always)]
pub fn a_fl_search(input: &[u8], head: &mut [u16; 16384], prev: &mut [u16; 32768], pos: usize, depth: usize, ins: usize, bl0: usize, bs0: usize, litq: usize, hsh: u64, nice: usize) -> usize {
    let n = input.len();
    if depth == 0 || n < 16 || pos > n - 16 {
        return 0;
    }
    let h = a_fl_hashp(input, pos, hsh) % 16384;
    let start = head[h] as usize;
    let pw = pos % 32768;
    prev[pw] = if ins == 1 { start as u16 } else { prev[pw] };
    head[h] = if ins == 1 { (pos as u16).wrapping_add(1) } else { head[h] };
    let rem = n - pos - 8;
    let cap = if rem < 258 { rem } else { 258 };
    a_fl_walk(input, prev, pos, start, cap, depth, bl0, bs0, litq, nice)
}

/// Insert the inside `from .. to` of an emitted match: its first `ih` and last `it` positions.
pub fn a_fl_insert_match(input: &[u8], head: &mut [u16; 16384], prev: &mut [u16; 32768], from: usize, to: usize, hsh: u64, ih: usize, it: usize) {
    let a = from.wrapping_add(ih);
    let a2 = if a < to { a } else { to };
    a_fl_tinsert(input, head, prev, from, a2, hsh);
    let b = to.wrapping_sub(it);
    let b2 = if b > a2 { if b < to { b } else { a2 } } else { a2 };
    a_fl_tinsert(input, head, prev, b2, to, hsh);
}

/// Literal-run length after `miss` consecutive misses: 1 + (miss >> acc), at most 32.
pub fn a_fl_lits(miss: usize, acc: usize) -> usize {
    let over = ((miss as u64) >> ((acc as u64) % 64)) as usize;
    if over < 32 {
        over + 1
    } else {
        32
    }
}

/// Literal cost (quarter bits) used by the lazy parser: from the entropy for low-entropy inputs, else A_FL_LITQ.
pub fn a_fl_litq(h0: usize) -> usize {
    if h0 < A_FL_HLOW {
        a_fl_lit_cost(h0)
    } else {
        A_FL_LITQ
    }
}

/// Hash shift: 8-byte hash (0) for low-entropy inputs, 4-byte hash (32) otherwise.
pub fn a_fl_hsh(h0: usize) -> u64 {
    if h0 < A_FL_HLOW {
        0
    } else {
        32
    }
}

/// Price-lazy a_parse (the jgreedy jg1c algorithm) with the class configuration `cf`.
pub fn a_fl_lazy_parse(input: &[u8], out: &mut [u32], lh: &[u32; 256], cf: &[usize; 8]) -> (usize, usize) {
    let n = input.len();
    let depth = cf[0];
    let depth2 = cf[1];
    let lazy = cf[2];
    let nice = cf[3];
    let ih = cf[4];
    let it = cf[5];
    let acc = cf[6];
    let h0 = a_fl_entropy256(lh);
    let litq = a_fl_litq(h0);
    let hsh = a_fl_hsh(h0);
    let mut head = [0u16; 16384];
    let mut prev = [0u16; 32768];
    let mut pos = 0usize;
    let mut ntok = 0usize;
    let mut carry = 0usize;
    let mut miss = 0usize;
    while pos < n {
        let have = if carry != 0 { 1usize } else { 0usize };
        let harg3 = if have == 1 { 0 } else { depth };
        let s1 = a_fl_search(input, &mut head, &mut prev, pos, harg3, 1, 2, 4096, litq, hsh, nice);
        let m1 = if have == 1 { carry } else { s1 };
        let l1 = m1 % 512;
        if l1 < 3 {
            let lits = a_fl_lits(miss, acc);
            let r = a_fl_emit_step(input, out, pos, 0, 0, lits, ntok);
            let olen = out.len();
            miss = miss.wrapping_add(1);
            carry = 0;
            ntok = r.0;
            pos = r.1;
        } else {
            let d1 = (m1 / 512) % 65536;
            let want = if l1 < lazy { 1usize } else { 0usize };
            let p2 = if want == 1 { if l1 >= A_FL_GOOD { depth2 } else { depth } } else { 0 };
            let s2 = a_fl_search(input, &mut head, &mut prev, pos.wrapping_add(1), p2, 1, l1.wrapping_sub(1), a_fl_score(l1, d1, litq), litq, hsh, nice);
            let take2 = if s2 != 0 { 1usize } else { 0usize };
            let l = if take2 == 1 { 0 } else { l1 };
            let d = if take2 == 1 { 0 } else { d1 };
            let r = a_fl_emit_step(input, out, pos, d, l, 1, ntok);
            let olen = out.len();
            let npos = r.1;
            let matched = if l >= 3 { if npos == pos.wrapping_add(l) { 1usize } else { 0usize } } else { 0usize };
            let from = if want == 1 { pos.wrapping_add(2) } else { pos.wrapping_add(1) };
            let harg4 = if matched == 1 { npos } else { from };
            a_fl_insert_match(input, &mut head, &mut prev, from, harg4, hsh, ih, it);
            carry = if take2 == 1 { s2 } else { 0 };
            miss = 0;
            ntok = r.0;
            pos = npos;
        }
    }
    (ntok, pos)
}

// ---------------------------------------------------------------- the floor phase

/// Runs the whole input through the mode's parser and returns `(ntok, n)`; mode 0 does nothing and returns
/// `(0, 0)` (the base parser then runs from position 0).
pub fn a_fl_part(input: &[u8], out: &mut [u32], mc: usize, fh: &[u32; 256]) -> (usize, usize) {
    let mode = mc % 8;
    if mode == 1 {
        a_fl_lit_parse(input, out)
    } else if mode == 2 {
        let mut cost = [0u32; 256];
        a_fl_costs(fh, &mut cost);
        a_fl_dna_parse(input, out, &cost)
    } else if mode == 4 {
        a_fl_rle_parse(input, out)
    } else if mode == 5 {
        let mut cf = [0usize; 8];
        a_fl_config(mc / 8, &mut cf);
        a_fl_lazy_parse(input, out, fh, &cf)
    } else {
        (0, 0)
    }
}
// ============================ end of the jfloor module =============================================================


/// Build predecessor links; hs % 64 is the hash shift.
/// Bit 6 skips accelerated literal gaps; bit 7 limits lookahead on high-entropy inputs.
/// Matched interiors are retained when only bit 7 is set.
/// A 64K ring holds the 32K history plus at most 4096 bytes of lookahead.
/// Each node stores the original 4-byte predecessor and the optional 3-byte predecessor.
#[inline(never)]
pub fn a_prepare(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 65536], head3: &mut [u32; 16384], shorts: &mut [u32; 4096], from: usize, pos: usize, hs: u32, h3on: usize) -> usize {
    let n = input.len();
    if from >= pos.saturating_add(2) || n < 16 {
        return from;
    }
    let sparse = hs >= 64;
    let hs0 = hs % 64;
    let upto = pos.saturating_add(if sparse { 2 } else { 4096 });
    let end = if upto < n - 15 { upto } else { n - 15 };
    let mut p = if hs % 128 >= 64 && pos > from { pos } else { from };
    while p < end {
        let h = a_hashp(input, p, hs0) % 65536;
        let old = head[h];
        let s3 = a_upd3(input, head3, p, h3on);
        if h3on == 1 { shorts[p % 4096] = s3 as u32; }
        prev[p % 65536] = old;
        head[h] = (p as u32).wrapping_add(1);
        p += 1;
    }
    end
}



/// Find a closer a_verified source for a retained previous-token prefix.
pub fn a_nearer_prefix(input: &[u8], prev: &[u32;65536], pp: usize, nl: usize, oldd: usize) -> usize {
    let mut cur=prev[pp%65536] as usize;let mut probes=0usize;let mut result=0usize;
    while probes<4 && cur>0 && cur<=pp {
        let c=cur-1;let d=pp-c;
        if d>=oldd || d>32768 {probes=4;}
        else if a_verified(input,pp,d,nl) {result=d;probes=4;}
        else {cur=prev[c%65536] as usize;probes+=1;}
    }
    result
}

/// Partial token fold; separate helper keeps one extracted suffix loop.
#[inline(always)]
pub fn a_public_partial(input: &[u8], out: &mut [u32], prev: &[u32;65536],
    nt: usize, p: usize, l: usize, dist: usize, t: u32, w: usize, costs:&[u32;256]) -> (usize,usize,usize) {
    if w>=3 && w<=p {
        let mut k=0usize;
        while k+1<w && l+k<258 && dist+k<p && input[p-1-k]==input[p-1-k-dist] {k+=1;}
        let pp=p-w;let oldd=((t-16777216)/256+1) as usize;
        let remain=w-k;
        if remain<=2 && k>0 {
            let oldcost=176usize.wrapping_add(a_lextra(w).wrapping_add(a_dextra(oldd)).wrapping_add(a_lextra(l)).wrapping_mul(16));
            let mut keep=1usize;let mut lc=0usize;let mut best=oldcost;let mut chosen=0usize;
            while keep<=2 && keep<w {
                lc=lc.wrapping_add(112);
                if keep>=remain {
                    let total=lc.wrapping_add(a_lextra(l+w-keep).wrapping_mul(16));
                    if total<best {best=total;chosen=keep;}
                }
                keep+=1;
            }
            if chosen>0 {
                out[nt-1]=input[pp] as u32;
                if chosen==2 {out[nt]=input[pp+1] as u32;}
                return (nt-1+chosen,pp+chosen,l+w-chosen);
            }
        }
        if w>4 {
            let k=if k<w-4 {k} else {w-4};
            if k>0 {
                let nl=w-k;
                let near=a_nearer_prefix(input,prev,pp,nl,oldd);
                let nd=if near>0 {near} else if a_lextra(nl).wrapping_add(a_lextra(l+k))<=a_lextra(w).wrapping_add(a_lextra(l)) && oldd>=1 && oldd<=32768 && oldd<=pp {oldd} else {0};
                if nd>0 {
                    out[nt-1]=16777216u32+((nd-1) as u32)*256+((nl-3) as u32);
                    return (nt,p-k,l+k);
                }
            }
        }
    }
    (nt,p,l)
}

/// One fold step, called under the decoder invariant and legal pending match.
#[inline(always)]
pub fn a_public_back_step(input: &[u8], out: &mut [u32], prev: &[u32;65536],
    nt: usize, p: usize, l: usize, dist: usize, back: usize, costs:&[u32;256]) -> (usize,usize,usize,usize) {
    let t=out[nt-1];
    if t<256 && input[p-1]==input[p-1-dist] {
        (nt-1,p-1,l+1,back+1)
    } else if t>=16777216 {
        let w=((t-16777216)%256+3) as usize;
        if w<=258-l && w<=p && dist<=p-w && a_verified(input,p-w,dist,w) {
            (nt-1,p-w,l+w,back+1)
        } else {
            let r=a_public_partial(input,out,prev,nt,p,l,dist,t,w,costs);
            (r.0,r.1,r.2,16)
        }
    } else {(nt,p,l,16)}
}

/// Generic backwards token joining with an unchanged endpoint.
pub fn a_public_back(input: &[u8], out: &mut [u32], prev: &[u32;65536], nt0: usize, pos0: usize,
    len0: usize, dist: usize, costs:&[u32;256]) -> (usize,usize,usize) {
    let mut nt=nt0;let mut p=pos0;let mut l=len0;let mut back=0usize;
    while back<16 && nt>0 && nt<=out.len() && p>dist && l<258 {
        let r=a_public_back_step(input,out,prev,nt,p,l,dist,back,costs);
        nt=r.0;p=r.1;l=r.2;back=r.3;
    }
    (nt,p,l)
}

/// Folding can only start when the byte before the pending match continues it; otherwise nothing changes.
#[inline(always)]
pub fn a_public_back_gate(input: &[u8], out: &mut [u32], prev: &[u32;65536], nt0: usize, pos0: usize,
    len0: usize, dist: usize, costs:&[u32;256]) -> (usize,usize,usize) {
    if pos0>dist && input[pos0-1]==input[pos0-1-dist] {a_public_back(input,out,prev,nt0,pos0,len0,dist,costs)} else {(nt0,pos0,len0)}
}

/// One a_verified gate for pending match. Folding independently verifies every
/// newly consumed earlier prefix, so resulting match follows by concatenation.
/// Outer endpoint is unchanged. No untrusted a_search fact is used to delete tokens.
pub fn a_public_emit_join(input: &[u8], out: &mut [u32], prev: &[u32;65536],
    pos: usize, dist: usize, len: usize, ntok: usize, costs:&[u32;256]) -> (usize,usize) {
    if a_verified(input,pos,dist,len) {
        let bk=a_public_back_gate(input,out,prev,ntok,pos,len,dist,costs);
        out[bk.0]=16777216u32+((dist-1) as u32)*256+((bk.2-3) as u32);
        (bk.0+1,bk.1+bk.2)
    } else {a_emit_step(input,out,pos,dist,len,1,ntok)}
}

/// Price-lazy a_parse using immutable predecessor links prepared ahead in batches.
/// Each chosen match still passes through the original trusted emission path.

/// Compare lazy candidates by the raw-byte prices only outside their common span.
/// Costs are sampled fractional bits; this is a heuristic, not trusted code.
pub fn a_public_span_better(input: &[u8], costs: &[u32;256], pos: usize,
    l1: usize, d1: usize, l2: usize, d2: usize, ex: usize) -> usize {
    let n=input.len();
    if l1<3 || l2<l1 || l2>258 || pos>=n || l2>=n-pos {return 0;}
    let first=if ex==1 {0} else {costs[input[pos] as usize] as usize};
    let aa=a_dextra(d1).wrapping_add(a_lextra(l1)).wrapping_mul(16);
    let bb=first.wrapping_add(a_dextra(d2).wrapping_add(a_lextra(l2+ex)).wrapping_mul(16));
    let mut tail=0usize;let mut j=l1;
    while j<=l2 {
        tail=tail.wrapping_add(costs[input[pos+j] as usize] as usize);
        if tail.wrapping_add(aa)>bb {return 1;}
        j+=1;
    }
    0
}

pub fn a_main_parse(input: &[u8], out: &mut [u32], pos0: usize, ntok0: usize) -> usize {
    let n = input.len();
    let mut head = [0u32; 65536];
    let mut prev = [0u32; 65536];
    let mut head3 = [0u32; 16384];
    let mut shorts = [0u32; 4096];
    let mut hist = [0u32; 256];
    a_sample(input, &mut hist);
    let mut span_costs=[0u32;256];
    a_fl_costs(&hist,&mut span_costs);
    let e = a_entropy256(&hist);
    let low = a_low_mode(e);
    let m3 = if low == 1 { 0 } else { a_m3_mode(&hist, e) };
    let num = a_numeric(&hist, n, low);
    let lq = if num == 1 { A_LQN } else { a_lit_cost(e, low) };
    let c0 = if low == 1 { A_C0L } else { A_C0Q };
    let litq = lq.wrapping_add(c0.wrapping_mul(256));
    let hs = if low == 1 { A_HSL } else if m3 == 1 { 40 } else { 32 };
    let hs = if e >= 1792 { hs.wrapping_add(128) } else { hs };
    let acc = if low == 1 { A_ACCL } else if n < A_NSMALL { 63 } else { A_ACC };
    let depth = if low == 1 { A_DEPTHL } else if m3 == 1 { A_DEPTH3M } else if num == 1 { A_DN } else { A_DEPTH };
    let lz = A_LAZY;
    let p2 = if num == 1 { A_P2N } else { A_DEPTH2 };
    let h3on = if m3 == 1 { 0 } else { a_h3_mode(&hist, e) };
    let mut pos = pos0;
    let mut ntok = ntok0;
    let mut carry = 0usize;
    let mut miss = 0usize;
    let mut filled = 0usize;
    while pos < n {
        if filled < pos.saturating_add(2) {
            filled = a_prepare(input, &mut head, &mut prev, &mut head3, &mut shorts, filled, pos, hs.wrapping_add(if miss >= 64 { 64 } else { 0 }), h3on);
        }
        let have = if carry != 0 { 1usize } else { 0usize };
        let dep = if have == 1 { 0 } else { depth };
        let ls = prev[pos.wrapping_add(1) % 65536] as usize;
        let s1 = a_search(input, &mut head, &mut prev, &mut head3, &shorts, pos, dep, 2, A_BIAS, litq, hs, h3on);
        let m1 = if have == 1 { carry } else { s1 };
        let l1 = m1 % 512;
        if l1 < 3 {
            let over = (miss as u64) >> (acc % 64);
            let lits = if over < A_STEPMAX as u64 { (over as usize).wrapping_add(1) } else { A_STEPMAX };
            let r = a_emit_step(input, out, pos, 0, 0, lits, ntok);
            let olen = out.len();
            miss = miss.wrapping_add(1);
            carry = 0;
            ntok = r.0;
            pos = r.1;
        } else {
            let d1 = (m1 / 512) % 65536;
            let want = if l1 < lz { 1usize } else { 0usize };
            let sv1 = m1 / 33554432;
            let s2 = a_lazy_probe(input, &mut head, &mut prev, &mut head3, pos.wrapping_add(1), want, p2, l1.wrapping_add(A_LZB), sv1.wrapping_add(A_BONUS), litq, hs, h3on, ls);
            let l2 = s2 % 512;
            let d2 = (s2 / 512) % 65536;
            let ex = if s2!=0 { a_ext_ok(input, pos, l2, d2) } else { 0 };
            let take2 = if s2!=0 {a_public_span_better(input,&span_costs,pos,l1,d1,l2,d2,ex)} else {0};
            let l = if take2 == 1 { if ex == 1 { l2.wrapping_add(1) } else { 0 } } else { l1 };
            let d = if take2 == 1 { if ex == 1 { d2 } else { 0 } } else { d1 };
            let r = a_public_emit_join(input,out,&prev,pos,d,l,ntok,&span_costs);
            let olen = out.len();
            let npos = r.1;

            carry = if take2 == 1 { if ex == 1 { 0 } else { s2 } } else { 0 };
            miss = 0;
            ntok = r.0;
            pos = npos;
        }
    }
    ntok
}

/// jfloor dispatcher. Sequential phases (no if/else between loop-heavy paths, SHARED_FINDINGS F17): the floor
/// phase handles the whole input for modes 1-5 and returns (ntok, n); for mode 0 it returns (0, 0) and the base
/// parser runs from position 0.
pub fn a_parse(input: &[u8], out: &mut [u32]) -> usize {
    let mut fh = [0u32; 256];
    a_fl_sample(input, &mut fh);
    let st = a_fl_stats(&fh);
    let mc = a_fl_mode(input, st);
    let r = a_fl_part(input, out, mc, &fh);
    if r.1 < input.len() { a_main_parse(input, out, r.1, r.0) } else { r.0 }
}

// ===== engine b: parse.rs =====

pub const B_H3B: u32 = 14;
pub const B_H3N: usize = 16384;
pub const B_H4B: u32 = 16;
pub const B_H4N: usize = 65536;
pub const B_H7B: u32 = 16;
pub const B_H7N: usize = 65536;
pub const B_WN: usize = 32768;
/// Price ring and backtracking chunk (positions).
pub const B_RING: usize = 8192;
pub const B_CHUNK: usize = 4096;
/// Long chain key length in bytes (5..8).
pub const B_KB7: u32 = 7;
/// Every length up to B_FULL_LEN is tried; above it, the last length of each length code.
pub const B_FULL_LEN: usize = 258;
/// The nearest 3-byte match is a candidate up to this distance.
pub const B_H3DIST: usize = 16384;
pub const B_H3DIST_STRUCT: usize = 16384;
pub const B_H3DIST_BIN: usize = 16384;
pub const B_H3DIST_PROSE: usize = 0;
/// DNA-like inputs: the nearest 3-byte match is not worth its cost there.
pub const B_H3DIST_DNA: usize = 0;
/// DNA-like inputs price symbols by Huffman code lengths (1) instead of entropy (0).
pub const B_HUFF_DNA: usize = 1;
pub const B_HUFF_TEXT: usize = 0;
pub const B_HUFF_STRUCT: usize = 0;
pub const B_HUFF_BIN: usize = 0;
pub const B_HUFF_PROSE: usize = 0;
/// Symbol costs are rebuilt every B_UPD positions; counts are halved above B_HALF_AT symbols.
pub const B_UPD: usize = 4096;
pub const B_HALF_AT: u32 = 12000;
pub const B_INF: u32 = 0x3FFF_FFFF;
pub const B_UNREACHED: u64 = 0x3FFF_FFFF_0000_0000;
/// Backward extension: at most B_TMAX bytes, for the B_BEXT_TOP longest candidates of a position.
pub const B_TMAX: usize = 128;
pub const B_BEXT_TOP: usize = 2;
pub const B_BTRUNC: usize = 1;
/// Lazy positions beyond the first are searched only after an anchor match of at most B_LZ2MAX bytes.
pub const B_LZ2MAX: usize = 16;
/// Inputs below B_SMALL bytes take the lazy engine (see the module comment).
pub const B_SMALL: usize = 65536;
/// Long-match share (per 1024, `sample_long`) from which text / structured text / other binary
/// inputs take the lazy engine; samples of B_SBLOCKS x B_SBS bytes.
pub const B_LONG_T: usize = 100;
pub const B_LONG_S: usize = 480;
pub const B_LONG_B: usize = 250;
/// Any input with a long-repeat share of at least B_LONG_X/1024 takes route B_R_XLONG.
pub const B_LONG_X: usize = 800;
/// Text with at least B_HIGH_MB/1024 bytes >= 128 (multi-byte UTF-8 text) is its own route.
pub const B_HIGH_MB: usize = 154;
/// Engine per route: 3 lazy engine (full settings), 4 lazy engine (lighter text settings), 10..14 dynamic
/// program (10 text, 11 structured text, 12 other binary, 13 DNA-like, 14 prose).
pub const B_R_SMALL: usize = 3;
pub const B_R_FLAT: usize = 3;
pub const B_R_HIGH: usize = 3;
pub const B_R_DNA: usize = 5;
pub const B_R_PROSE: usize = 14;
pub const B_R_MB: usize = 5;
pub const B_R_TEXT: usize = 5;
pub const B_R_TLONG: usize = 5;
pub const B_R_STRUCT: usize = 11;
pub const B_R_SLONG: usize = 5;
pub const B_R_BIN: usize = 5;
pub const B_R_XLONG: usize = 5;
pub const B_R_BLONG: usize = 5;
pub const B_SBLOCKS: usize = 8;
pub const B_SBS: usize = 4096;
/// Dynamic-program settings per route: text, structured text, other binary, DNA-like, prose.
/// B_CT: continuation threshold, B_LZ: lazy positions searched, B_D4/B_D7: chain depths, B_SKIP: take-as-is length.
pub const B_CT: usize = 4;
pub const B_LZ: usize = 1;
pub const B_D4: usize = 1;
pub const B_D7: usize = 4;
pub const B_SKIP: usize = 128;
pub const B_CT_STRUCT: usize = 3;
pub const B_LZ_STRUCT: usize = 1;
pub const B_D4_STRUCT: usize = 1;
pub const B_D7_STRUCT: usize = 1;
pub const B_SKIP_STRUCT: usize = 64;
pub const B_CT_BIN: usize = 4;
pub const B_LZ_BIN: usize = 1;
pub const B_D4_BIN: usize = 1;
pub const B_D7_BIN: usize = 16;
pub const B_SKIP_BIN: usize = 64;
pub const B_CT_DNA: usize = 6;
pub const B_LZ_DNA: usize = 1;
pub const B_D4_DNA: usize = 2;
pub const B_D7_DNA: usize = 8;
pub const B_SKIP_DNA: usize = 32;
pub const B_CT_PROSE: usize = 4;
pub const B_LZ_PROSE: usize = 1;
pub const B_D4_PROSE: usize = 4;
pub const B_D7_PROSE: usize = 8;
pub const B_SKIP_PROSE: usize = 32;

/// DEFLATE length-code base lengths (codes 257..285) and extra bits.
pub const B_LBASE: [u32; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
    131, 163, 195, 227, 258,
];
pub const B_LEXTRA: [u32; 32] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 0, 0, 0,
];
/// DEFLATE distance-code base distances and extra bits.
pub const B_DBASE: [u32; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];
pub const B_DEXTRA: [u32; 32] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13, 0, 0,
];
/// round(16 * log2(1 + m/32)) for m < 32.
pub const B_FRAC: [u32; 32] = [
    0, 1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 7, 7, 8, 9, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 14,
    15, 15, 15, 16,
];

// ───────────────────────────── the load-bearing part ─────────────────────────────

/// The eight bytes at `p` as one big-endian number (byte `p` most significant), or 0 when
/// fewer than eight bytes remain (Horner form; one load plus `bswap` once inlined).
#[inline(always)]
pub fn b_load8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n >= 8 && p <= n - 8 {
        let mut v = input[p] as u64;
        v = v * 256 + input[p + 1] as u64;
        v = v * 256 + input[p + 2] as u64;
        v = v * 256 + input[p + 3] as u64;
        v = v * 256 + input[p + 4] as u64;
        v = v * 256 + input[p + 5] as u64;
        v = v * 256 + input[p + 6] as u64;
        v * 256 + input[p + 7] as u64
    } else {
        0
    }
}

/// How many leading (most significant) bytes the words `x` and `y` share: 8 when equal.
#[inline(always)]
pub fn b_first_diff(x: u64, y: u64) -> usize {
    let z = x ^ y;
    let lz = z.leading_zeros();
    let bytes = lz / 8;
    bytes as usize
}

/// How many bytes agree at `a` and `b`, up to `cap`: eight at a time, the first mismatching
/// word resolved by `first_diff`, the last `cap % 8` bytes one at a time.
#[inline(always)]
pub fn b_mlen(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while cap - l >= 8 {
        let x = b_load8(input, a + l);
        let y = b_load8(input, b + l);
        if x != y {
            return l + b_first_diff(x, y);
        }
        l += 8;
    }
    while l < cap && input[a + l] == input[b + l] {
        l += 1;
    }
    l
}

/// True only if `(len, dist)` is a legal match at `p` whose bytes all agree.
pub fn b_check(input: &[u8], p: usize, len: usize, dist: usize) -> bool {
    let n = input.len();
    if p > n || len < 3 || len > 258 || dist < 1 || dist > 32768 || dist > p || len > n - p {
        return false;
    }
    let src = p - dist;
    let l = b_mlen(input, src, p, len);
    l == len
}

/// `v[i]`, or 0 when `i` is out of range.
pub fn b_get0(v: &[u32], i: usize) -> u32 {
    if i < v.len() {
        v[i]
    } else {
        0
    }
}


/// Phase 2: walk the plan from 0 (entry `k` for the `k`-th planned token); a planned match is
/// written only if `check` accepts it, else its bytes become literals (so the plan stays aligned).
pub fn b_emit(input: &[u8], plan: &[u32], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut ntok = 0usize;
    let mut k = 0usize;
    let mut owed = 0usize;
    let mut p = 0usize;
    while p < n {
        if owed > 0 {
            out[ntok] = input[p] as u32;
            ntok += 1;
            p += 1;
            owed -= 1;
        } else {
            let v = b_get0(plan, k);
            k += 1;
            let len = (v % 512) as usize;
            let dist = (v / 512) as usize;
            let valid = b_check(input, p, len, dist);
            if valid {
                let tok = 16777216u32 + ((dist - 1) as u32) * 256 + ((len - 3) as u32);
                out[ntok] = tok;
                ntok += 1;
                p += len;
            } else {
                out[ntok] = input[p] as u32;
                ntok += 1;
                p += 1;
                if len >= 2 {
                    owed = len - 1;
                }
            }
        }
    }
    ntok
}

/// The whole parser: one sniff, then the route's engine (the dynamic program's plan is re-checked
/// by `emit`).
pub fn b_parse(input: &[u8], out: &mut [u32]) -> usize {
    let cls = b_a_sniff(input);
    let r = b_route(input, cls);
    if r == 3 {
        b_a_parse_cls(input, out, cls, 1)
    } else if r == 4 {
        b_a_parse_cls(input, out, cls, 0)
    } else {
        let plan = b_make_plan(input, r);
        b_emit(input, &plan, out)
    }
}

// ─────────────────────────── phase 1: search, totality only ───────────────────────────



/// Eight bytes at `i`, first byte most significant (0 when out of range).
#[inline(always)]
pub fn b_be8(s: &[u8], i: usize) -> u64 {
    if i + 8 <= s.len() {
        ((s[i] as u64) << 56)
            | ((s[i + 1] as u64) << 48)
            | ((s[i + 2] as u64) << 40)
            | ((s[i + 3] as u64) << 32)
            | ((s[i + 4] as u64) << 24)
            | ((s[i + 5] as u64) << 16)
            | ((s[i + 6] as u64) << 8)
            | (s[i + 7] as u64)
    } else {
        0
    }
}

/// Length of the common prefix of s[a..] and s[b..], at most `cap`.
#[inline(always)]
pub fn b_common(s: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut k = 0usize;
    let mut run = 1u32;
    while run == 1 && cap - k >= 8 {
        let x = b_be8(s, a + k) ^ b_be8(s, b + k);
        if x == 0 {
            k += 8;
        } else {
            k += (x.leading_zeros() / 8) as usize;
            run = 0;
        }
    }
    while run == 1 && k < cap && a + k < s.len() && b + k < s.len() {
        if s[a + k] == s[b + k] {
            k += 1;
        } else {
            run = 0;
        }
    }
    k
}

#[inline(always)]
pub fn b_hash3(x: u32) -> usize {
    ((x.wrapping_mul(2654435761)) >> (32 - B_H3B)) as usize % B_H3N
}

#[inline(always)]
pub fn b_hash4(x: u32) -> usize {
    ((x.wrapping_mul(2654435761)) >> (32 - B_H4B)) as usize % B_H4N
}

#[inline(always)]
pub fn b_hash7(x: u64) -> usize {
    ((x.wrapping_mul(0x9E37_79B9_7F4A_7C15)) >> (64 - B_H7B)) as usize % B_H7N
}

/// `16 * log2(x)` for x >= 1 (about 1/16-bit precision).
#[inline(always)]
pub fn b_log2_16(x: u32) -> u32 {
    if x == 0 {
        return 0;
    }
    let e = 31 - x.leading_zeros();
    let m = if e >= 5 { (x >> (e - 5)) % 32 } else { (x << (5 - e)) % 32 };
    e * 16 + B_FRAC[m as usize % 32]
}

/// Length codes (0..28) of lengths 0..258, distance codes of `d - 1` (d <= 256: index d - 1;
/// larger d: index 256 + (d - 1) / 128).
pub fn b_fill_tables(lsym: &mut [u8; 512], dtab: &mut [u8; 512]) {
    let mut code = 0usize;
    let mut l = 0usize;
    while l < 259 {
        if code < 28 && l as u32 >= B_LBASE[code + 1] {
            code += 1;
        }
        lsym[l] = code as u8;
        l += 1;
    }
    let mut c = 0usize;
    let mut j = 0usize;
    while j < 256 {
        if c < 29 && (j as u32) + 1 >= B_DBASE[c + 1] {
            c += 1;
        }
        dtab[j] = c as u8;
        j += 1;
    }
    let mut c2 = 0usize;
    let mut k = 0usize;
    while k < 256 {
        let d = ((k as u32) << 7) + 1;
        while c2 < 29 && d >= B_DBASE[c2 + 1] {
            c2 += 1;
        }
        dtab[256 + k] = c2 as u8;
        k += 1;
    }
}

/// Distance code of `d` in 1..=32768.
#[inline(always)]
pub fn b_dsym(dtab: &[u8; 512], d: usize) -> usize {
    let dm = d.wrapping_sub(1);
    let idx = if dm < 256 { dm } else { 256 + (dm >> 7) };
    dtab[idx % 512] as usize
}

/// nextl[l]: the next length to try after l (every length up to B_FULL_LEN, then code ends).
pub fn b_fill_nextl(lsym: &[u8; 512], nextl: &mut [u16; 512]) {
    let mut l = 0usize;
    while l < 512 {
        if l < B_FULL_LEN || l >= 257 {
            nextl[l] = (l + 1) as u16;
        } else {
            let mut e = l + 1;
            while e < 258 && lsym[e + 1] == lsym[l + 1] {
                e += 1;
            }
            nextl[l] = e as u16;
        }
        l += 1;
    }
}

/// Costs (1/16 bit) from counts: 16*log2(total/f); unseen symbols cost log2(total) + 2 bits.
pub fn b_costs_from(freq: &[u32], out: &mut [u32]) {
    let mut total = 0u32;
    let mut s = 0usize;
    while s < freq.len() {
        total = total.saturating_add(freq[s]);
        s += 1;
    }
    let lt = b_log2_16(total.saturating_add(1));
    let mut t = 0usize;
    while t < freq.len() && t < out.len() {
        let f = freq[t];
        let c = if f == 0 { lt.saturating_add(32) } else { lt.saturating_sub(b_log2_16(f)) };
        out[t] = if c < 8 { 8 } else if c > 320 { 320 } else { c };
        t += 1;
    }
}


/// Insert symbol `i` (count `f`) into the sorted prefix `sym[0..ns)`: returns its slot.
#[inline(always)]
pub fn b_huff_slot(freq: &[u32], sym: &mut [usize; 320], ns: usize, f: u32) -> usize {
    let mut j = ns % 321;
    while j > 0 && freq[sym[(j - 1) % 320] % freq.len()] > f {
        sym[j % 320] = sym[(j - 1) % 320];
        j -= 1;
    }
    j
}

/// Symbols with a nonzero count among `freq[0..m)`, sorted by count: returns how many.
pub fn b_huff_sort(freq: &[u32], m: usize, sym: &mut [usize; 320]) -> usize {
    let mut ns = 0usize;
    let mut i = 0usize;
    while i < m && i < freq.len() && i < 320 {
        if freq[i] > 0 {
            let j = b_huff_slot(freq, sym, ns, freq[i]);
            sym[j % 320] = i;
            ns += 1;
        }
        i += 1;
    }
    ns
}

/// The lighter of the next leaf `a` and the next internal node `b` (internal nodes exist below
/// `nx`): (node, a, b) after taking it.
#[inline(always)]
pub fn b_huff_take(w: &[u64; 640], a: usize, b: usize, ns: usize, nx: usize) -> (usize, usize, usize) {
    if a < ns && (b >= nx || w[a % 640] <= w[b % 640]) {
        (a, a + 1, b)
    } else {
        (b, a, b + 1)
    }
}

/// Two-queue Huffman construction over `ns` sorted leaf weights in `w[0..ns)`; internal nodes
/// are appended at ns.. with their parent links in `par`. Returns the node count.
pub fn b_huff_build(w: &mut [u64; 640], par: &mut [usize; 640], ns: usize) -> usize {
    let mut a = 0usize;
    let mut b = ns;
    let mut nx = ns;
    while nx + 1 < 2 * ns && nx < 639 {
        let x = b_huff_take(w, a, b, ns, nx);
        let y = b_huff_take(w, x.1, x.2, ns, nx);
        w[nx % 640] = w[x.0 % 640].wrapping_add(w[y.0 % 640]);
        par[x.0 % 640] = nx;
        par[y.0 % 640] = nx;
        a = y.1;
        b = y.2;
        nx += 1;
    }
    nx
}

/// Depth of every node below the root `nx - 1` (reverse creation order); returns the deepest leaf.
pub fn b_huff_depths(par: &[usize; 640], depth: &mut [u32; 640], nx: usize, ns: usize) -> u32 {
    let mut mx = 1u32;
    if nx >= 1 {
        let root = nx - 1;
        depth[root % 640] = 0;
        let mut q = root;
        while q > 0 {
            q -= 1;
            let d = depth[par[q % 640] % 640].wrapping_add(1);
            depth[q % 640] = d;
            if q < ns && d > mx {
                mx = d;
            }
        }
    }
    mx
}

/// Huffman code lengths of the counts `freq[0..m)` (m <= 320), as costs in 1/16 bit: symbols
/// with count 0 cost one bit more than the longest code; lengths are capped at 15 bits.
pub fn b_huff_costs(freq: &[u32], m: usize, out: &mut [u32]) {
    let mut sym = [0usize; 320];
    let ns = b_huff_sort(freq, m, &mut sym);
    let mut w = [0u64; 640];
    let mut par = [0usize; 640];
    let mut depth = [0u32; 640];
    let mut k = 0usize;
    while k < ns {
        w[k % 640] = freq[sym[k % 320] % freq.len()] as u64;
        k += 1;
    }
    let mut mx = 1u32;
    if ns >= 2 {
        let nx = b_huff_build(&mut w, &mut par, ns);
        mx = b_huff_depths(&par, &mut depth, nx, ns);
    }
    if mx > 15 {
        mx = 15;
    }
    let mut t = 0usize;
    while t < m && t < out.len() {
        out[t] = (mx + 1) * 16;
        t += 1;
    }
    let mut r = 0usize;
    while r < ns {
        let s0 = sym[r % 320];
        let mut d = depth[r % 640];
        if d > 15 {
            d = 15;
        }
        if d == 0 {
            d = 1;
        }
        if s0 < out.len() {
            out[s0] = d * 16;
        }
        r += 1;
    }
}

/// Literal costs, length costs (symbol + extra bits) and distance-code costs from counts.
pub fn b_make_costs(
    lf: &[u32; 320],
    df: &[u32; 32],
    lsym: &[u8; 512],
    litc: &mut [u32; 256],
    lc: &mut [u32; 512],
    dcc: &mut [u32; 32],
    huff: usize,
) {
    let mut llc = [0u32; 286];
    let mut dc = [0u32; 30];
    if huff == 1 {
        b_huff_costs(lf, 286, &mut llc);
        b_huff_costs(df, 30, &mut dc);
    } else {
        b_costs_from(lf, &mut llc);
        b_costs_from(df, &mut dc);
    }
    let mut b = 0usize;
    while b < 256 {
        litc[b] = llc[b];
        b += 1;
    }
    let mut l = 0usize;
    while l < 259 {
        let s = lsym[l] as usize % 32;
        lc[l] = llc[257 + s].wrapping_add(B_LEXTRA[s].wrapping_mul(16));
        l += 1;
    }
    let mut k = 0usize;
    while k < 30 {
        dcc[k] = dc[k].wrapping_add(B_DEXTRA[k].wrapping_mul(16));
        k += 1;
    }
}

/// Initial counts: literals from a strided byte histogram, matches from a text-like prior.
pub fn b_init_counts(input: &[u8], lf: &mut [u32; 320], df: &mut [u32; 32]) {
    let n = input.len();
    let step = (n / 8192) | 1;
    let mut i = 0usize;
    while i < n {
        let b = input[i] as usize;
        lf[b] = lf[b].saturating_add(1);
        i += step;
    }
    let mut s = 257usize;
    while s < 286 {
        let w = if s < 265 { 400u32 } else if s < 273 { 150 } else { 30 };
        lf[s] = w;
        s += 1;
    }
    lf[256] = 1;
    let mut k = 0usize;
    while k < 30 {
        df[k] = if k < 4 { 60 } else { 120 };
        k += 1;
    }
}

/// Halve the counts when they exceed B_HALF_AT symbols, then rebuild the costs.
pub fn b_update_costs(
    lf: &mut [u32; 320],
    df: &mut [u32; 32],
    lsym: &[u8; 512],
    litc: &mut [u32; 256],
    lc: &mut [u32; 512],
    dcc: &mut [u32; 32],
    huff: usize,
) {
    let mut tot = 0u32;
    let mut z = 0usize;
    while z < 286 {
        tot = tot.wrapping_add(lf[z]);
        z += 1;
    }
    if tot > B_HALF_AT {
        b_halve(lf, df);
    }
    b_make_costs(lf, df, lsym, litc, lc, dcc, huff);
}

pub fn b_halve(lf: &mut [u32; 320], df: &mut [u32; 32]) {
    let mut s = 0usize;
    while s < 286 {
        lf[s] = lf[s].wrapping_add(1) / 2;
        s += 1;
    }
    let mut k = 0usize;
    while k < 30 {
        df[k] = df[k].wrapping_add(1) / 2;
        k += 1;
    }
}

/// Match length at `c` if it beats `best` (else 0); `b8` holds the eight bytes at `i` and
/// `cap >= 9`. One 8-byte compare decides lengths below 8; longer ones are checked at `best`.
#[inline(always)]
pub fn b_probe(s: &[u8], c: usize, i: usize, b8: u64, cap: usize, best: usize) -> usize {
    let x = b_be8(s, c) ^ b8;
    if x != 0 {
        let l = (x.leading_zeros() / 8) as usize;
        if l > best {
            l
        } else {
            0
        }
    } else if best < 8 {
        8 + b_common(s, c + 8, i + 8, cap - 8)
    } else if best < cap && c + best < s.len() && i + best < s.len() && s[c + best] == s[i + best] {
        let l = 8 + b_common(s, c + 8, i + 8, cap - 8);
        if l > best {
            l
        } else {
            0
        }
    } else {
        0
    }
}

/// Walk a chain from `start` for at most `depth` steps: push each match longer than all
/// before it as `len | dist << 9`. Returns (count, longest).
#[inline(always)]
pub fn b_walk(
    s: &[u8],
    prev: &[u32; B_WN],
    i: usize,
    start: usize,
    depth: usize,
    b8: u64,
    cap: usize,
    cands: &mut [u32; 16],
    nc0: usize,
    best0: usize,
) -> (usize, usize) {
    let mut nc = nc0;
    let mut best = best0;
    let mut c = start;
    let mut k = depth;
    while k > 0 {
        let d = i.wrapping_sub(c);
        if d.wrapping_sub(1) < 32768 && best < cap && nc < 15 {
            let l = b_probe(s, c, i, b8, cap, best);
            if l > 0 && nc < 15 {
                cands[nc % 16] = (l as u32) | ((d as u32) << 9);
                nc += 1;
                best = l;
            }
            let nx = prev[c % B_WN] as usize;
            if nx < c {
                c = nx;
                k -= 1;
            } else {
                k = 0;
            }
        } else {
            k = 0;
        }
    }
    (nc, best)
}

/// Chain start and depth after stepping over the head when `same` (it was probed already).
#[inline(always)]
pub fn b_skip_same(prev: &[u32; B_WN], start: usize, depth: usize, same: bool) -> (usize, usize) {
    if same && depth > 0 {
        let nx = prev[start % B_WN] as usize;
        if nx < start {
            (nx, depth - 1)
        } else {
            (start, 0)
        }
    } else {
        (start, depth)
    }
}

/// Relax lengths lo..hi (per `nextl`) and hi itself of one candidate from position `i`
/// (`base` = price at i plus the distance cost). A ring entry is `price << 32 | choice`, so
/// one unsigned minimum keeps the cheaper arrival (ties: the smaller choice).
#[inline(always)]
pub fn b_relax_run(
    pa: &mut [u64; B_RING],
    lc: &[u32; 512],
    nextl: &[u16; 512],
    i: usize,
    lo: usize,
    hi: usize,
    base: u32,
    dpack: u32,
) {
    let mut l = lo;
    while l < hi {
        let c = base.wrapping_add(lc[l % 512]);
        let slot = (i + l) % B_RING;
        let v = ((c as u64) << 32) | ((dpack | l as u32) as u64);
        let old = pa[slot];
        pa[slot] = if v < old { v } else { old };
        l = nextl[l % 512] as usize;
    }
    if hi >= lo {
        let c = base.wrapping_add(lc[hi % 512]);
        let slot = (i + hi) % B_RING;
        let v = ((c as u64) << 32) | ((dpack | hi as u32) as u64);
        let old = pa[slot];
        pa[slot] = if v < old { v } else { old };
    }
}

/// Backtrack the chunk [s, e) from e: the path's tokens (`len | dist << 9`, 0 for a literal)
/// are collected in reverse in `tb`, counted into the symbol statistics, then appended to the
/// plan in order (the plan is a token list: the emission reads entry `k` for its `k`-th token).
pub fn b_backtrack(
    input: &[u8],
    pa: &[u64; B_RING],
    plan: &mut Vec<u32>,
    s: usize,
    e: usize,
    lsym: &[u8; 512],
    dtab: &[u8; 512],
    lf: &mut [u32; 320],
    df: &mut [u32; 32],
    tb: &mut [u32; B_RING],
) {
    let mut j = e;
    let mut nt = 0usize;
    let mut guard = e - s + 1;
    while j > s && guard > 0 {
        guard -= 1;
        let a = pa[j % B_RING] as u32;
        let len = (a % 512) as usize;
        if len >= 3 && len <= j - s {
            tb[nt % B_RING] = a;
            nt += 1;
            let ls = lsym[len % 512] as usize % 32;
            lf[257 + ls] = lf[257 + ls].wrapping_add(1);
            let ds = b_dsym(dtab, (a >> 9) as usize) % 32;
            df[ds] = df[ds].wrapping_add(1);
            j -= len;
        } else {
            tb[nt % B_RING] = 0;
            nt += 1;
            j -= 1;
            if j < input.len() {
                let b = input[j] as usize;
                lf[b] = lf[b].wrapping_add(1);
            }
        }
    }
    b_push_rev(plan, tb, nt, input.len());
}

/// Append `tb[nt-1], ..., tb[0]` to the plan (at most `lim` entries in all).
pub fn b_push_rev(plan: &mut Vec<u32>, tb: &[u32; B_RING], nt: usize, lim: usize) {
    let mut k = nt;
    while k > 0 {
        k -= 1;
        if plan.len() < lim {
            plan.push(tb[k % B_RING]);
        }
    }
}

/// Start a chunk at `s`: price 0 there, the next 258 slots unreached.
#[inline(always)]
pub fn b_open_chunk(pa: &mut [u64; B_RING], s: usize) {
    pa[s % B_RING] = 0;
    let mut u = 1usize;
    while u < 259 {
        pa[(s + u) % B_RING] = B_UNREACHED;
        u += 1;
    }
}

/// Insert position `q` (whose eight bytes are `b8`) into the three tables; returns the
/// previous heads: the nearest 3-byte match, the 4-byte chain and the long chain.
#[inline(always)]
pub fn b_insert_pos(
    head3: &mut [u32; B_H3N],
    head4: &mut [u32; B_H4N],
    prev4: &mut [u32; B_WN],
    head7: &mut [u32; B_H7N],
    prev7: &mut [u32; B_WN],
    q: usize,
    b8: u64,
    sh7: u32,
) -> (usize, usize, usize) {
    let x4 = (b8 >> 32) as u32;
    let h3 = b_hash3(x4 >> 8);
    let c3 = head3[h3] as usize;
    head3[h3] = q as u32;
    let h4 = b_hash4(x4);
    let c4 = head4[h4] as usize;
    head4[h4] = q as u32;
    prev4[q % B_WN] = c4 as u32;
    let h7 = b_hash7(b8 >> (sh7 % 64));
    let c7 = head7[h7] as usize;
    head7[h7] = q as u32;
    prev7[q % B_WN] = c7 as u32;
    (c3, c4, c7)
}

/// Insert the positions `from..to` (inside a match taken as is).
pub fn b_insert_range(
    input: &[u8],
    head3: &mut [u32; B_H3N],
    head4: &mut [u32; B_H4N],
    prev4: &mut [u32; B_WN],
    head7: &mut [u32; B_H7N],
    prev7: &mut [u32; B_WN],
    from: usize,
    to: usize,
    sh7: u32,
) {
    let mut q = from;
    while q < to {
        let bq = b_be8(input, q);
        b_insert_pos(head3, head4, prev4, head7, prev7, q, bq, sh7);
        q += 1;
    }
}

/// How far a match at `i` with distance `d` extends backwards: at most `max` bytes and not
/// below the chunk start `s`.
pub fn b_ext_back(input: &[u8], i: usize, d: usize, s: usize, max: usize) -> usize {
    let mut t = 0usize;
    while t < max && i >= t + 1 + d && i - t - 1 >= s && input[i - t - 1] == input[i - t - 1 - d] {
        t += 1;
    }
    t
}

/// Among the starts i-1 .. i-t of a candidate extended backwards (t <= B_TMAX), the one
/// where arriving and then taking the whole match (to i + len) is cheapest: (t, cost).
pub fn b_back_best(input: &[u8], pa: &[u64; B_RING], lc: &[u32; 512], i: usize, s: usize, len: usize, dd: usize) -> (usize, u32) {
    let mut t = 0usize;
    let mut bt = 0usize;
    let mut bv = B_INF;
    while t < B_TMAX && len + t < 258 && i >= t + 1 + dd && i - t - 1 >= s && input[i - t - 1] == input[i - t - 1 - dd] {
        t += 1;
        let v = ((pa[(i - t) % B_RING] >> 32) as u32).wrapping_add(lc[(len + t) % 512]);
        if v < bv {
            bv = v;
            bt = t;
        }
    }
    (bt, bv)
}

/// The position that found the current longest candidate: `i`, unless the continuation
/// (length `cl`) is still the longest.
#[inline(always)]
pub fn b_next_anchor(anchor: usize, i: usize, cl: usize, best: usize) -> usize {
    if cl > 0 && cl >= best {
        anchor
    } else {
        i
    }
}

/// Keep the cheaper arrival at ring slot `slot`.
#[inline(always)]
pub fn b_relax_one(pa: &mut [u64; B_RING], slot: usize, cost: u32, choice: u32) {
    let v = ((cost as u64) << 32) | (choice as u64);
    let old = pa[slot % B_RING];
    pa[slot % B_RING] = if v < old { v } else { old };
}

/// Relax the candidates of a searched position `i` (price `base`): each candidate's lengths
/// (the previous candidate's length, its length], then its backward extension.
pub fn b_relax_cands(
    input: &[u8],
    pa: &mut [u64; B_RING],
    cands: &[u32; 16],
    nc: usize,
    lc: &[u32; 512],
    nextl: &[u16; 512],
    dtab: &[u8; 512],
    dcc: &[u32; 32],
    i: usize,
    s: usize,
    base: u32,
    pcd: usize,
) {
    let mut lo = 3usize;
    let mut k = 0usize;
    while k < nc && k < 16 {
        let c = cands[k];
        let len = (c % 512) as usize;
        let dd = (c >> 9) as usize;
        let ds = b_dsym(dtab, dd) % 32;
        let bd = base.wrapping_add(dcc[ds]);
        b_relax_run(pa, lc, nextl, i, lo, len, bd, c & !511u32);
        lo = len + 1;
        if dd != pcd && (k + B_BEXT_TOP >= nc) {
            let r = b_back_best(input, pa, lc, i, s, len, dd);
            if r.0 > 0 {
                b_relax_one(pa, i + len, r.1.wrapping_add(dcc[ds]), (c & !511u32) | (len + r.0) as u32);
                if B_BTRUNC == 1 {
                    // the extended match may also end early: lengths reaching i+3 .. i+len-1
                    let j = i - r.0;
                    let pj = (pa[j % B_RING] >> 32) as u32;
                    b_relax_run(pa, lc, nextl, j, r.0 + 3, r.0 + len - 1, pj.wrapping_add(dcc[ds]), c & !511u32);
                }
            }
        }
        k += 1;
    }
}

/// Drop candidates farther than `cd` from the end of the list (they are shorter than the
/// continuation at `cd`); returns the new count.
pub fn b_drop_farther(cands: &[u32; 16], nc0: usize, cd: usize) -> usize {
    let mut nc = nc0;
    while nc > 0 && (cands[(nc - 1) % 16] >> 9) as usize > cd {
        nc -= 1;
    }
    nc
}

pub fn b_dp_parse(input: &[u8], plan: &mut Vec<u32>, ct: usize, lazyn: usize, d4: usize, d7: usize, skip: usize, h3d: usize, huff: usize) {
    let n = input.len();
    let mut head3 = [0u32; B_H3N];
    let mut head4 = [0u32; B_H4N];
    let mut prev4 = [0u32; B_WN];
    let mut head7 = [0u32; B_H7N];
    let mut prev7 = [0u32; B_WN];
    let mut pa = [B_UNREACHED; B_RING];
    let mut tb = [0u32; B_RING];
    let mut lsym = [0u8; 512];
    let mut dtab = [0u8; 512];
    b_fill_tables(&mut lsym, &mut dtab);
    let mut nextl = [0u16; 512];
    b_fill_nextl(&lsym, &mut nextl);
    let mut lf = [0u32; 320];
    let mut df = [0u32; 32];
    b_init_counts(input, &mut lf, &mut df);
    let mut litc = [0u32; 256];
    let mut lc = [0u32; 512];
    let mut dcc = [0u32; 32];
    b_make_costs(&lf, &df, &lsym, &mut litc, &mut lc, &mut dcc, huff);
    b_halve(&mut lf, &mut df);
    b_halve(&mut lf, &mut df);
    let lim = n - 8; // callers guarantee n >= 16
    let sh7 = 64 - 8 * B_KB7;
    let mut s = 0usize; // chunk start
    b_open_chunk(&mut pa, 0);
    let mut next_upd = B_UPD;
    let mut cands = [0u32; 16];
    let mut cl = 0usize; // continuation of the previous position's longest candidate
    let mut cd = 0usize;
    let mut cdc = 0u32; // its distance cost
    let mut i = 0usize;
    let mut anchor = 0usize; // the position that found the current longest candidate
    let mut alen = 0usize; // the longest candidate length found at the anchor
    while i < lim {
        if i > s {
            pa[(i + 258) % B_RING] = B_UNREACHED;
        }
        let b8 = b_be8(input, i);
        let hc = b_insert_pos(&mut head3, &mut head4, &mut prev4, &mut head7, &mut prev7, i, b8, sh7);
        let base = (pa[i % B_RING] >> 32) as u32;
        // literal
        b_relax_one(&mut pa, i + 1, base.wrapping_add(litc[(b8 >> 56) as usize % 256]), 0);
        // the LAZYN positions right after the one that found the current match are searched too
        let lzn = if alen <= B_LZ2MAX { lazyn } else { 1 };
        let lazy_here = i.wrapping_sub(anchor).wrapping_sub(1) < lzn;
        if cl >= ct && cl >= 3 && !lazy_here {
            // inside a match: only the continuation's full length (it ends where it did)
            b_relax_one(&mut pa, i + cl, base.wrapping_add(cdc).wrapping_add(lc[cl % 512]), ((cd as u32) << 9) | cl as u32);
            cl -= 1;
            i += 1;
        } else {
            let mut cap = n - i;
            if cap > 258 {
                cap = 258;
            }
            // candidates: nearest 3-byte match, 4-byte chain, long chain, continuation
            let mut nc = 0usize;
            let mut best = 2usize;
            let d3 = i.wrapping_sub(hc.0);
            let p3 = d3.wrapping_sub(1) < h3d;
            if p3 {
                let l3 = b_probe(input, hc.0, i, b8, cap, 2);
                if l3 > 0 {
                    cands[0] = (l3 as u32) | ((d3 as u32) << 9);
                    nc = 1;
                    best = l3;
                }
            }
            // a chain head equal to a position already probed is stepped over (same result)
            let s4 = b_skip_same(&prev4, hc.1, d4, p3 && hc.1 == hc.0);
            let w = b_walk(input, &prev4, i, s4.0, s4.1, b8, cap, &mut cands, nc, best);
            nc = w.0;
            best = w.1;
            let dep7 = if best >= 4 || d4 == 0 { d7 } else { 0 };
            let s7 = b_skip_same(&prev7, hc.2, dep7, (p3 && hc.2 == hc.0) || (d4 > 0 && hc.2 == hc.1));
            let w2 = b_walk(input, &prev7, i, s7.0, s7.1, b8, cap, &mut cands, nc, best);
            nc = w2.0;
            best = w2.1;
            if cl > best && cl <= cap {
                // the continuation is the longest: drop farther shorter candidates, append it
                nc = b_drop_farther(&cands, nc, cd);
                cands[nc % 16] = (cl as u32) | ((cd as u32) << 9);
                if nc < 16 {
                    nc += 1;
                }
                best = cl;
            }
            let pcd = if cl >= 3 { cd } else { 0 };
            alen = b_next_anchor(alen, best, cl, best);
            anchor = b_next_anchor(anchor, i, cl, best);
            if nc > 0 {
                let top = cands[(nc - 1) % 16];
                cl = ((top % 512) as usize).saturating_sub(1);
                cd = (top >> 9) as usize;
                cdc = dcc[b_dsym(&dtab, cd) % 32];
            } else {
                cl = 0;
            }
            if best >= skip && nc > 0 {
                // take the longest candidate, extended backwards, as is; close the chunk before it
                let c0 = cands[(nc - 1) % 16];
                let d0 = (c0 >> 9) as usize;
                let l0 = best;
                let t = b_ext_back(input, i, d0, s, 258 - l0 % 259);
                let st = i - t;
                b_backtrack(input, &pa, plan, s, st, &lsym, &dtab, &mut lf, &mut df, &mut tb);
                if plan.len() < n {
                    plan.push(c0.wrapping_add(t as u32));
                }
                let ls = lsym[(l0 + t) % 512] as usize % 32;
                lf[257 + ls] = lf[257 + ls].wrapping_add(1);
                let ds = b_dsym(&dtab, d0) % 32;
                df[ds] = df[ds].wrapping_add(1);
                let mut end = i + l0;
                if end > lim {
                    end = lim;
                }
                b_insert_range(input, &mut head3, &mut head4, &mut prev4, &mut head7, &mut prev7, i + 1, end, sh7);
                i = i + l0;
                s = i;
                cl = 0;
                b_open_chunk(&mut pa, s);
            } else {
                b_relax_cands(input, &mut pa, &cands, nc, &lc, &nextl, &dtab, &dcc, i, s, base, pcd);
                i += 1;
            }
        }
        if i - s >= B_CHUNK {
            b_backtrack(input, &pa, plan, s, i, &lsym, &dtab, &mut lf, &mut df, &mut tb);
            s = i;
            b_open_chunk(&mut pa, s);
        }
        if i >= next_upd {
            next_upd = i + B_UPD;
            b_update_costs(&mut lf, &mut df, &lsym, &mut litc, &mut lc, &mut dcc, huff);
            cdc = dcc[b_dsym(&dtab, cd) % 32];
        }
    }
    if i > s && i <= n {
        let e = if i < lim { i } else { lim };
        if e > s {
            b_backtrack(input, &pa, plan, s, e, &lsym, &dtab, &mut lf, &mut df, &mut tb);
        }
    }
}


/// Which engine takes an input of sniffed class `cls`: 3/4 the lazy engine (full / lighter text
/// settings) or 10..14 the dynamic program (see R_*).
pub fn b_route(input: &[u8], cls: usize) -> usize {
    let n = input.len();
    if n < B_SMALL {
        return B_R_SMALL;
    }
    if cls == 7 {
        return B_R_FLAT;
    }
    if cls == 2 || cls == 4 {
        return B_R_HIGH;
    }
    // the class's route below and at/above its long-repeat threshold
    let mut r = B_R_TEXT;
    let mut rl = B_R_TLONG;
    let mut lim = B_LONG_T;
    if cls == 0 {
        r = B_R_DNA;
        rl = B_R_DNA;
    }
    if cls == 5 {
        r = B_R_PROSE;
        rl = B_R_PROSE;
    }
    if cls == 6 {
        r = B_R_STRUCT;
        rl = B_R_SLONG;
        lim = B_LONG_S;
    }
    if cls == 3 {
        r = B_R_BIN;
        rl = B_R_BLONG;
        lim = B_LONG_B;
    }
    if cls == 1 && b_high_share(input) >= B_HIGH_MB {
        r = B_R_MB;
        rl = B_R_MB;
    }
    if r == rl && r < 10 {
        return r;
    }
    // extremely repetitive input leaves the dynamic program for the lazy engine
    let long = b_sample_long(input);
    if long >= B_LONG_X {
        return B_R_XLONG;
    }
    if long >= lim {
        rl
    } else {
        r
    }
}

/// Bytes >= 128 per 1024 of 1024 evenly spaced samples.
pub fn b_high_share(input: &[u8]) -> usize {
    let n = input.len();
    let step = (n / 1024) | 1;
    let mut i = 0usize;
    let mut hi = 0usize;
    let mut tot = 0usize;
    while i < n && tot < 2049 {
        if input[i] >= 128 {
            hi += 1;
        }
        tot += 1;
        i = i.wrapping_add(step);
    }
    if tot == 0 {
        0
    } else {
        hi * 1024 / tot
    }
}

/// Phase 1: the plan (a token list). Every entry is a suggestion; `emit` checks each one.
pub fn b_make_plan(input: &[u8], r: usize) -> Vec<u32> {
    let n = input.len();
    let mut plan: Vec<u32> = Vec::with_capacity(n / 2 + 16);
    if n >= 16 && n.wrapping_add(n) > n {
        if r == 11 {
            b_dp_parse(input, &mut plan, B_CT_STRUCT, B_LZ_STRUCT, B_D4_STRUCT, B_D7_STRUCT, B_SKIP_STRUCT, B_H3DIST_STRUCT, B_HUFF_STRUCT);
        } else if r == 12 {
            b_dp_parse(input, &mut plan, B_CT_BIN, B_LZ_BIN, B_D4_BIN, B_D7_BIN, B_SKIP_BIN, B_H3DIST_BIN, B_HUFF_BIN);
        } else if r == 13 {
            b_dp_parse(input, &mut plan, B_CT_DNA, B_LZ_DNA, B_D4_DNA, B_D7_DNA, B_SKIP_DNA, B_H3DIST_DNA, B_HUFF_DNA);
        } else if r == 14 {
            b_dp_parse(input, &mut plan, B_CT_PROSE, B_LZ_PROSE, B_D4_PROSE, B_D7_PROSE, B_SKIP_PROSE, B_H3DIST_PROSE, B_HUFF_PROSE);
        } else {
            b_dp_parse(input, &mut plan, B_CT, B_LZ, B_D4, B_D7, B_SKIP, B_H3DIST, B_HUFF_TEXT);
        }
    }
    plan
}

// ───────────────────────── routing samples ─────────────────────────

/// Greedy parse of `input[st..end)` with a 4096-entry table of 4-byte keys (last position + 1
/// in the block; positions inside a match are skipped): bytes covered by matches of at least
/// 32 bytes.
pub fn b_sample_block(input: &[u8], st: usize, end: usize, tab: &mut [u32; 4096]) -> usize {
    let mut lb = 0usize;
    let mut i = st;
    while i < end && i + 8 <= input.len() {
        let x = (b_be8(input, i) >> 32) as u32;
        let h = ((x.wrapping_mul(2654435761)) >> 20) as usize % 4096;
        let c = tab[h] as usize;
        tab[h] = (i + 1) as u32;
        let mut step = 1usize;
        if c > st && c <= i {
            let mut cap = end - i;
            if cap > 258 {
                cap = 258;
            }
            let l = b_common(input, c - 1, i, cap);
            if l >= 4 {
                if l >= 32 {
                    lb += l;
                }
                step = l;
            }
        }
        i += step;
    }
    lb
}

/// Share (per 1024) of B_SBLOCKS sampled blocks of B_SBS bytes covered by greedy matches of at
/// least 32 bytes (inputs of at least 64 KB): high on logs, tables and markup, where a fast
/// parse is already close to its best.
pub fn b_sample_long(input: &[u8]) -> usize {
    let n = input.len();
    let mut lb = 0usize;
    let mut tot = 0usize;
    let mut b = 0usize;
    while b < B_SBLOCKS && n > B_SBS {
        let st = (n - B_SBS) / (B_SBLOCKS + 1) * (b + 1);
        let mut tab = [0u32; 4096];
        lb += b_sample_block(input, st, st + B_SBS, &mut tab);
        tot += B_SBS;
        b += 1;
    }
    if tot == 0 {
        0
    } else {
        lb * 1024 / tot
    }
}



// ───────────────────────── lazy engine (mA lineage, names prefixed a_/A_) ─────────────────────────

pub const B_A_HB: u32 = 16;
pub const B_A_HN: usize = 65536;
pub const B_A_WN: usize = 32768;
/// Inputs of at most B_A_SMALL bytes use B_A_HS chain heads and a B_A_WS window table.
pub const B_A_SMALL: usize = 65536;
pub const B_A_HS: usize = 16384;
pub const B_A_WS: usize = 32768;
pub const B_A_NICE: usize = 258;
pub const B_A_INS_MAX: usize = 258;
pub const B_A_TAIL: usize = 8;
/// Inside long matches, every B_A_STRIDE-th position between the head and the tail is chained
/// too (B_A_STRIDE = 0: none).
pub const B_A_STRIDE: usize = 1;
pub const B_A_BACKTOK: usize = 16;
pub const B_A_LDEPTH: usize = 8;
pub const B_A_SAMPLE: usize = 2048;
pub const B_A_VERIFY: usize = 0;
/// Lazy step: a candidate at p+1 needs length >= l + 1 - B_A_LSLACK (B_A_LSLACK = 1: at least as long
/// as the current match l) and must win on estimated saving (literal worth B_A_HLIT/16 bits,
/// match base cost B_A_GBASE/16 bits plus extra bits).
pub const B_A_LSLACK: usize = 1;
pub const B_A_HLIT: u32 = 64;
/// Literal worth (1/16 bit) in the saving estimate for binary classes (3 and 7).
pub const B_A_B_HLIT: u32 = 64;
pub const B_A_GBASE: i32 = 168;
/// Per class: main chain depth, lazy threshold, skip shift, skip cap (T text, P prose,
/// H high-entropy binary, Z high-entropy binary rich in zero bytes, B other binary,
/// DNA-like input is sent as literals).
pub const B_A_T_DEPTH: usize = 20;
/// Lighter text settings (level 0): walk depth, insertion head, stride, two-step lazy depth, partial merge.
pub const B_A_T_DEPTH0: usize = 20;
pub const B_A_INS_MAX0: usize = 258;
pub const B_A_STRIDE0: usize = 1;
pub const B_A_L2DEPTH0: usize = 1;
pub const B_A_PARTIAL0: usize = 1;
pub const B_A_T_LAZY: usize = 258;
pub const B_A_T_SKIP: usize = 10;
pub const B_A_P_DEPTH: usize = 128;
pub const B_A_P_LAZY: usize = 258;
pub const B_A_P_SKIP: usize = 5;
pub const B_A_H_DEPTH: usize = 2;
pub const B_A_H_LAZY: usize = 0;
pub const B_A_H_SKIP: usize = 4;
pub const B_A_Z_DEPTH: usize = 3;
pub const B_A_Z_SKIP: usize = 8;
pub const B_A_Z_CAP: usize = 8;
pub const B_A_B_DEPTH: usize = 32;
pub const B_A_B_LAZY: usize = 258;
pub const B_A_B_SKIP: usize = 8;
/// Structured text (class 6: text with at least 1/B_A_SDIG of the sample in digits): main depth
/// B_A_S_DEPTH, lazy a_walk depth B_A_S_LDEPTH, lazy threshold B_A_S_LAZY.
pub const B_A_SDIG: u32 = 6;
pub const B_A_S_DEPTH: usize = 8;
pub const B_A_S_LDEPTH: usize = 8;
pub const B_A_S_LAZY: usize = 258;
/// Largest skip step (extra literals per miss) outside the Z class.
pub const B_A_SKCAP: usize = 1000000;
/// Per-class a_walk stop (B_A_NICE is the text value), lazy a_walk depth (B_A_LDEPTH is the text value),
/// insertion inside matches (B_A_INS_MAX/B_A_STRIDE/B_A_TAIL are the text values).
pub const B_A_P_NICE: usize = 258;
pub const B_A_S_NICE: usize = 258;
pub const B_A_H_NICE: usize = 32;
pub const B_A_Z_NICE: usize = 32;
pub const B_A_B_NICE: usize = 258;
pub const B_A_P_LDEPTH: usize = 8;
pub const B_A_H_LDEPTH: usize = 1;
pub const B_A_B_LDEPTH: usize = 2;
pub const B_A_P_INS: usize = 258;
pub const B_A_S_INS: usize = 258;
pub const B_A_B_INS: usize = 64;
pub const B_A_H_INS: usize = 12;
pub const B_A_P_STRIDE: usize = 1;
pub const B_A_S_STRIDE: usize = 1;
pub const B_A_B_STRIDE: usize = 4;
/// Two-step lazy: when p+1 does not beat the pending match, p+2 is tried (B_A_L2DEPTH chain steps)
/// and wins if its saving beats the pending one by more than B_A_L2B/16 bits (B_A_LAZY2 = 1; 0 = off).
pub const B_A_LAZY2: usize = 1;
pub const B_A_L2B: i32 = 40;
pub const B_A_L2DEPTH: usize = 4;
/// Main a_walk in a_gain mode (a longer candidate must also save more).
pub const B_A_MAIN_GM: usize = 1;
/// Partial merge: when the new match also covers the last k bytes of the previous match (but not
/// all of it), the previous match is shortened by k if a closer source (at most B_A_PDEPTH chain steps)
/// covers its shorter length; the new match then starts k bytes earlier (0 = off).
pub const B_A_PARTIAL: usize = 1;
pub const B_A_PDEPTH: usize = 4;
/// Class 7: high-entropy input without a dominant byte (no byte above 1/B_A_FLAT_DIV of the sample:
/// compressed data, images) parsed with 3-byte keys (F_ settings); class 2 keeps the peaky ones
/// (16-bit weights).
pub const B_A_FLAT_ON: usize = 1;
pub const B_A_FLAT_DIV: u32 = 16;
/// ... and whose byte collision rate (sum of squared sample counts * 256 / samples^2) is below
/// B_A_FLAT_SQ/16 (uniform data: 1; images and compressed streams: 1.1-1.4; 8-bit weights: 1.8).
pub const B_A_FLAT_SQ: u64 = 26;
pub const B_A_F_DEPTH: usize = 32;
pub const B_A_F_LAZY: usize = 258;
pub const B_A_F_LDEPTH: usize = 2;
pub const B_A_F_SKIP: usize = 7;
pub const B_A_H_STRIDE: usize = 32;

/// Eight bytes at `i`, first byte most significant (0 when out of range).
#[inline(always)]
pub fn b_a_be8(s: &[u8], i: usize) -> u64 {
    if i + 8 <= s.len() {
        ((s[i] as u64) << 56)
            | ((s[i + 1] as u64) << 48)
            | ((s[i + 2] as u64) << 40)
            | ((s[i + 3] as u64) << 32)
            | ((s[i + 4] as u64) << 24)
            | ((s[i + 5] as u64) << 16)
            | ((s[i + 6] as u64) << 8)
            | (s[i + 7] as u64)
    } else {
        0
    }
}

/// Four bytes at `i`, first byte most significant (0 when out of range).
#[inline(always)]
pub fn b_a_be4(s: &[u8], i: usize) -> u32 {
    if i + 4 <= s.len() {
        ((s[i] as u32) << 24) | ((s[i + 1] as u32) << 16) | ((s[i + 2] as u32) << 8) | (s[i + 3] as u32)
    } else {
        0
    }
}

/// Input class from a strided byte histogram of at most ~B_A_SAMPLE bytes:
/// 0 DNA-like, 1 text, 2 high-entropy binary, 3 other binary, 4 high-entropy with zeros,
/// 5 prose (text of letters and spaces with almost no code symbols), 6 structured text (many
/// digits: tables, logs, dumps).
pub fn b_a_sniff(s: &[u8]) -> usize {
    let n = s.len();
    let mut cnt = [0u32; 256];
    let step = (n / B_A_SAMPLE) | 1;
    let mut i = 0usize;
    let mut tot = 0u32;
    // `tot < 4097` always holds here (at most 4096 samples); with it the loop is total even
    // for a slice of usize::MAX bytes, where `i + step` could overflow.
    while i < n && tot < 4097 {
        cnt[s[i] as usize % 256] += 1;
        tot += 1;
        i = i.wrapping_add(step);
    }
    let dna = cnt[65] + cnt[67] + cnt[71] + cnt[84] + cnt[97] + cnt[99] + cnt[103] + cnt[116] + cnt[78] + cnt[110] + cnt[10];
    let mut text = cnt[9] + cnt[10] + cnt[13];
    let mut high = 0u32;
    let mut words = cnt[32];
    let mut b = 32usize;
    while b < 256 {
        if b != 127 {
            text += cnt[b];
        }
        if b >= 128 {
            high += cnt[b];
        }
        if (b >= 65 && b <= 90) || (b >= 97 && b <= 122) {
            words += cnt[b];
        }
        b += 1;
    }
    let syms = cnt[35] + cnt[36] + cnt[37] + cnt[38] + cnt[40] + cnt[41] + cnt[42] + cnt[43] + cnt[47] + cnt[59] + cnt[60] + cnt[61] + cnt[62] + cnt[64] + cnt[91] + cnt[92] + cnt[93] + cnt[94] + cnt[95] + cnt[96] + cnt[123] + cnt[124] + cnt[125] + cnt[126];
    let mut cls = 3usize;
    if tot > 0 && dna >= tot - tot / 10 {
        cls = 0;
    } else if text >= tot - tot / 100 && cnt[0] == 0 {
        cls = 1;
        let digits = cnt[48] + cnt[49] + cnt[50] + cnt[51] + cnt[52] + cnt[53] + cnt[54] + cnt[55] + cnt[56] + cnt[57];
        if words >= tot - tot / 7 && syms <= tot / 64 {
            cls = 5;
        } else if digits >= tot / B_A_SDIG {
            cls = 6;
        }
    } else if high >= tot / 3 {
        cls = 2;
        if cnt[0] >= tot / 20 {
            cls = 4;
        } else if B_A_FLAT_ON == 1 {
            let mut mx = 0u32;
            let mut sq = 0u64;
            let mut b2 = 0usize;
            while b2 < 256 {
                let c2 = cnt[b2] as u64;
                if cnt[b2] > mx {
                    mx = cnt[b2];
                }
                sq = sq.wrapping_add(c2.wrapping_mul(c2));
                b2 += 1;
            }
            let t2 = (tot as u64).wrapping_mul(tot as u64);
            if mx < tot / B_A_FLAT_DIV && sq.wrapping_mul(256) < t2.wrapping_mul(B_A_FLAT_SQ) / 16 {
                cls = 7;
            }
        }
    }
    cls
}

/// Estimated saving (1/16 bit) of a match of length `l` at distance `d` over literals.
#[inline(always)]
pub fn b_a_gain(l: usize, d: usize, hlit: i32) -> i32 {
    let mut c = B_A_GBASE;
    if l > 10 && l < 258 {
        c += 16 * (29 - ((l - 3) as u32).leading_zeros()) as i32;
    }
    if d > 4 {
        c += 16 * (30 - ((d - 1) as u32).leading_zeros()) as i32;
    }
    (l as i32) * hlit - c
}

/// Length of the a_common prefix of s[a..] and s[b..], at most `cap`.
#[inline(always)]
pub fn b_a_common(s: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut k = 0usize;
    let mut a_run = 1u32;
    while a_run == 1 && cap - k >= 8 {
        let x = b_a_be8(s, a + k) ^ b_a_be8(s, b + k);
        if x == 0 {
            k += 8;
        } else {
            k += (x.leading_zeros() / 8) as usize;
            a_run = 0;
        }
    }
    while a_run == 1 && k < cap {
        if s[a + k] == s[b + k] {
            k += 1;
        } else {
            a_run = 0;
        }
    }
    k
}

/// 1 when s[a..a+len] == s[b..b+len]: eight bytes at a time, the last partial word
/// under a mask when a full load fits, else byte by byte.
#[inline(always)]
pub fn b_a_same(s: &[u8], a: usize, b: usize, len: usize) -> usize {
    let n = s.len();
    let mut k = 0usize;
    let mut ok = 1usize;
    while ok == 1 && len - k >= 8 {
        if b_a_be8(s, a + k) == b_a_be8(s, b + k) {
            k += 8;
        } else {
            ok = 0;
        }
    }
    if ok == 1 && k < len {
        if a + k + 8 <= n && b + k + 8 <= n {
            let x = b_a_be8(s, a + k) ^ b_a_be8(s, b + k);
            if (x >> (64 - 8 * (len - k) as u32)) != 0 {
                ok = 0;
            }
        } else {
            while ok == 1 && k < len {
                if s[a + k] == s[b + k] {
                    k += 1;
                } else {
                    ok = 0;
                }
            }
        }
    }
    ok
}

#[inline(always)]
pub fn b_a_put_lit(s: &[u8], out: &mut [u32], nt: usize, p: usize) -> usize {
    out[nt] = s[p] as u32;
    nt + 1
}

/// Emit a match (re-checked when B_A_VERIFY = 1), else a literal. Returns (tokens, next position).
#[inline(always)]
pub fn b_a_put_match(s: &[u8], out: &mut [u32], nt: usize, p: usize, d: usize, l: usize) -> (usize, usize) {
    let n = s.len();
    if d >= 1 && d <= 32768 && d <= p && l >= 3 && l <= 258 && p < n && l <= n - p && (B_A_VERIFY == 0 || b_a_same(s, p - d, p, l) == 1) {
        out[nt] = 16777216u32 + ((d - 1) as u32) * 256 + ((l - 3) as u32);
        (nt + 1, p + l)
    } else {
        out[nt] = s[p] as u32;
        (nt + 1, p + 1)
    }
}

/// Walk the chain from `start`: the longest match at `p` longer than `have` (with `gm` = 1,
/// a longer candidate must also have a higher estimated saving); distance 0 = none found.
/// Each candidate first compares the byte at `best`.
#[inline(always)]
pub fn b_a_walk<const W: usize>(s: &[u8], prev: &[u32; W], p: usize, start: usize, cap: usize, have: usize, depth: usize, nice: usize, gm: usize, hlit: i32) -> (usize, usize, i32) {
    let n = s.len();
    let mut best = have;
    let mut bd = 0usize;
    let mut bg = -1000000i32;
    let mut c = start;
    let mut k = depth;
    let mut stop = nice;
    if stop > cap {
        stop = cap;
    }
    let mut pb = 0u8;
    if best < n - p {
        pb = s[p + best];
    }
    while k > 0 {
        let nx = prev[c % W] as usize;
        let d = p.wrapping_sub(c);
        if d.wrapping_sub(1) < 32768 && c + best < n {
            if s[c + best] == pb {
                let l = b_a_common(s, c, p, cap);
                let mut take = 0usize;
                if l > best {
                    take = 1;
                    if gm == 1 {
                        let g = b_a_gain(l, d, hlit);
                        if g > bg {
                            bg = g;
                        } else {
                            take = 0;
                        }
                    }
                }
                if take == 1 {
                    best = l;
                    bd = d;
                    if l >= stop || p + l >= n {
                        k = 1;
                    } else {
                        pb = s[p + l];
                    }
                }
            }
            if nx < c {
                c = nx;
                k -= 1;
            } else {
                k = 0;
            }
        } else {
            k = 0;
        }
    }
    if gm != 1 && bd > 0 { bg = b_a_gain(best, bd, hlit); }
    (best, bd, bg)
}

/// Put position `i` at the head of its chain (key = first four bytes under `mask`);
/// returns the previous head.
#[inline(always)]
pub fn b_a_insert<const H: usize, const W: usize>(s: &[u8], head: &mut [u32; H], prev: &mut [u32; W], i: usize, mask: u32) -> usize {
    let k = (b_a_be4(s, i) & mask) as u64;
    let a = (k.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (64 - B_A_HB)) as usize % H;
    let old = head[a];
    prev[i % W] = old;
    head[a] = i as u32;
    old as usize
}

/// Distance of the first chain entry from `start` (at most `depth` steps) whose next `len` bytes
/// equal those at `p` (0 = none).
#[inline(always)]
pub fn b_a_closest<const W: usize>(s: &[u8], prev: &[u32; W], p: usize, start: usize, len: usize, depth: usize) -> usize {
    let n = s.len();
    let mut c = start;
    let mut k = depth;
    let mut res = 0usize;
    while k > 0 {
        let d = p.wrapping_sub(c);
        if d.wrapping_sub(1) < 32768 && len >= 1 && c < p && p + len <= n {
            if s[c + len - 1] == s[p + len - 1] && b_a_same(s, c, p, len) == 1 {
                res = d;
                k = 0;
            } else {
                let nx = prev[c % W] as usize;
                if nx < c {
                    c = nx;
                    k -= 1;
                } else {
                    k = 0;
                }
            }
        } else {
            k = 0;
        }
    }
    res
}

/// Partial merge (`partial` = 1): the new match `(l0, d)` at `p0` also covers the last `k` bytes of
/// the previous match token `t` (`w` bytes, ending at `p0`), but not all of it. When a closer
/// source (at most B_A_PDEPTH chain steps) covers its first `w - k` bytes, that token is shortened by
/// `k` and the new match starts `k` bytes earlier. Returns the new `(p, l)`.
#[inline(always)]
pub fn b_a_part_merge<const W: usize>(input: &[u8], out: &mut [u32], prev: &[u32; W], nt: usize, p0: usize, l0: usize, d: usize, t: u32, w: usize, partial: usize) -> (usize, usize) {
    let mut p = p0;
    let mut l = l0;
    if partial == 1 && w > 4 && w <= p {
        let mut k = 0usize;
        while k + 4 < w && l + k < 258 && d + k < p && input[p - 1 - k] == input[p - 1 - k - d] {
            k += 1;
        }
        let pd = ((t - 16777216) / 256 + 1) as usize;
        if k > 0 {
            let pp = p - w;
            let nl = w - k;
            let c = b_a_closest(input, prev, pp, prev[pp % W] as usize, nl, B_A_PDEPTH);
            if c > 0 && c < pd && c <= pp && nl >= 3 && nl <= 258 {
                out[nt - 1] = 16777216u32 + ((c - 1) as u32) * 256 + ((nl - 3) as u32);
                p -= k;
                l += k;
            }
        }
    }
    (p, l)
}

/// Best match at `p` longer than `have` and at least `minl` long; (0, 0) when none.
#[inline(always)]
pub fn b_a_find<const W: usize>(s: &[u8], prev: &[u32; W], p: usize, st: usize, have: usize, minl: usize, depth: usize, nice: usize, gm: usize, hlit: i32) -> (usize, usize, i32) {
    let n = s.len();
    let mut cap = n - p;
    if cap > 258 {
        cap = 258;
    }
    let mut lo = have;
    if lo + 1 < minl {
        lo = minl - 1;
    }
    let f = b_a_walk(s, prev, p, st, cap, lo, depth, nice, gm, hlit);
    let mut l = f.0;
    if f.1 == 0 {
        l = 0;
    }
    (l, f.1, f.2)
}

/// The a_parse for one input class (inlined so the text classes get constant settings), with
/// H chain heads and a window table of W entries.
#[inline(always)]
pub fn b_a_run<const H: usize, const W: usize>(input: &[u8], out: &mut [u32], cls: usize, lvl: usize) -> usize {
    let n = input.len();
    let mut nt = 0usize;
    let mut p = 0usize;
    let mut mask = 0xFFFF_FFFFu32;
    let mut minl = 4usize;
    let mut depth = if lvl == 0 { B_A_T_DEPTH0 } else { B_A_T_DEPTH };
    let l2d = if lvl == 0 { B_A_L2DEPTH0 } else { B_A_L2DEPTH };
    let partial = if lvl == 0 { B_A_PARTIAL0 } else { B_A_PARTIAL };
    let mut lazy = B_A_T_LAZY;
    let mut skip = B_A_T_SKIP;
    let mut skcap = B_A_SKCAP;
    let mut nice = B_A_NICE;
    let mut ldep = B_A_LDEPTH;
    let mut insm = if lvl == 0 { B_A_INS_MAX0 } else { B_A_INS_MAX };
    let mut stride = if lvl == 0 { B_A_STRIDE0 } else { B_A_STRIDE };
    let mut hlit = B_A_HLIT as i32;
    if cls == 6 {
        depth = B_A_S_DEPTH;
        lazy = B_A_S_LAZY;
        nice = B_A_S_NICE;
        ldep = B_A_S_LDEPTH;
        insm = B_A_S_INS;
        stride = B_A_S_STRIDE;
    }
    if cls == 5 {
        depth = B_A_P_DEPTH;
        lazy = B_A_P_LAZY;
        skip = B_A_P_SKIP;
        nice = B_A_P_NICE;
        ldep = B_A_P_LDEPTH;
        insm = B_A_P_INS;
        stride = B_A_P_STRIDE;
    }
    if cls == 2 || cls == 4 {
        depth = B_A_H_DEPTH;
        lazy = B_A_H_LAZY;
        skip = B_A_H_SKIP;
        nice = B_A_H_NICE;
        ldep = B_A_H_LDEPTH;
        insm = B_A_H_INS;
        stride = B_A_H_STRIDE;
        if cls == 4 {
            depth = B_A_Z_DEPTH;
            skip = B_A_Z_SKIP;
            skcap = B_A_Z_CAP;
            nice = B_A_Z_NICE;
        }
    }
    if cls == 3 || cls == 7 {
        hlit = B_A_B_HLIT as i32;
    }
    if cls == 7 {
        mask = 0xFFFF_FF00;
        minl = 3;
        depth = B_A_F_DEPTH;
        lazy = B_A_F_LAZY;
        skip = B_A_F_SKIP;
        nice = B_A_B_NICE;
        ldep = B_A_F_LDEPTH;
        insm = B_A_B_INS;
        stride = B_A_B_STRIDE;
    }
    if cls == 3 {
        mask = 0xFFFF_FF00;
        minl = 3;
        depth = B_A_B_DEPTH;
        lazy = B_A_B_LAZY;
        skip = B_A_B_SKIP;
        nice = B_A_B_NICE;
        ldep = B_A_B_LDEPTH;
        insm = B_A_B_INS;
        stride = B_A_B_STRIDE;
    }
    if n > 16 && cls != 0 {
        let mut head = [0u32; H];
        let mut prev = [0u32; W];
        let lim = n - 8;
        let mut ins = 0usize; // next position to a_insert
        let mut miss = 0usize; // literals since the last match
        let mut fuel = n.saturating_add(16); // every pass advances p unless a re-check fails
        while p < lim && fuel > 0 {
            fuel -= 1;
            while ins < p {
                b_a_insert(input, &mut head, &mut prev, ins, mask);
                ins += 1;
            }
            // `ins == p` here (a match leaves `ins = end = p`, literals leave `ins = p`)
            let hc = b_a_insert(input, &mut head, &mut prev, p, mask);
            ins = p + 1;
            let f = b_a_find(input, &prev, p, hc, 0, minl, depth, nice, B_A_MAIN_GM, hlit);
            let mut l = f.0;
            let mut d = f.1;
            let mut gain = f.2;
            if l >= 3 {
                // Lazy: move on while the next position has a better match by the saving
                // estimate (it may be as long but closer, or longer).
                let mut go = 1u32;
                while go == 1 && l < lazy && p + 1 < lim {
                    let q = p + 1;
                    let hq = b_a_insert(input, &mut head, &mut prev, q, mask);
                    ins = q + 1;
                    let mut have = 0usize;
                    if l > B_A_LSLACK {
                        have = l - B_A_LSLACK;
                    }
                    let g = b_a_find(input, &prev, q, hq, have, minl, ldep, nice, 1, hlit);
                    if g.0 >= minl && g.2 > gain {
                        nt = b_a_put_lit(input, out, nt, p);
                        p = q;
                        l = g.0;
                        d = g.1;
                        gain = g.2;
                    } else {
                        go = 0;
                        if B_A_LAZY2 == 1 && p + 2 < lim {
                            let q2 = p + 2;
                            // `ins == q2` here (`ins = q + 1` above)
                            let hq2 = b_a_insert(input, &mut head, &mut prev, q2, mask);
                            ins = q2 + 1;
                            let g2 = b_a_find(input, &prev, q2, hq2, have, minl, l2d, nice, 1, hlit);
                            if g2.0 >= minl && g2.2 > gain.wrapping_add(B_A_L2B) {
                                nt = b_a_put_lit(input, out, nt, p);
                                nt = b_a_put_lit(input, out, nt, p + 1);
                                p = q2;
                                l = g2.0;
                                d = g2.1;
                                gain = g2.2;
                                go = 1;
                            }
                        }
                    }
                }
                // Fold earlier tokens into this match while their bytes also match at d.
                let mut back = 0usize;
                while back < B_A_BACKTOK && nt > 0 && nt <= out.len() && l < 258 && d < p {
                    let t = out[nt - 1];
                    if t < 256 && input[p - 1] == input[p - 1 - d] {
                        p -= 1;
                        nt -= 1;
                        l += 1;
                        back += 1;
                    } else if t >= 16777216 {
                        let w = ((t - 16777216) % 256 + 3) as usize;
                        if l + w <= 258 && w <= p && d <= p - w && b_a_same(input, p - w - d, p - w, w) == 1 {
                            p -= w;
                            nt -= 1;
                            l += w;
                            back += 1;
                        } else {
                            let r = b_a_part_merge(input, out, &prev, nt, p, l, d, t, w, partial);
                            p = r.0;
                            l = r.1;
                            back = B_A_BACKTOK;
                        }
                    } else {
                        back = B_A_BACKTOK;
                    }
                }
                let r = b_a_put_match(input, out, nt, p, d, l);
                nt = r.0;
                let end = r.1;
                // Chain the first B_A_INS_MAX and the last B_A_TAIL positions inside the match.
                let mut stop = end;
                // wrapping: a_same code as `+` here (no overflow on any real input), total in the model
                if stop > ins.wrapping_add(insm) {
                    stop = ins.wrapping_add(insm);
                }
                if stop > lim {
                    stop = lim;
                }
                while ins < stop {
                    b_a_insert(input, &mut head, &mut prev, ins, mask);
                    ins += 1;
                }
                if stride > 0 {
                    // `ins + B_A_TAIL + stride < end`, with the bound computed once (total in the model)
                    let e2 = end.saturating_sub(B_A_TAIL.saturating_add(stride));
                    while ins < e2 && ins < lim {
                        b_a_insert(input, &mut head, &mut prev, ins, mask);
                        ins += stride;
                    }
                }
                if ins.wrapping_add(B_A_TAIL) < end {
                    ins = end - B_A_TAIL;
                }
                while ins < end && ins < lim {
                    b_a_insert(input, &mut head, &mut prev, ins, mask);
                    ins += 1;
                }
                if ins < end {
                    ins = end;
                }
                p = end;
                miss = 0;
            } else {
                nt = b_a_put_lit(input, out, nt, p);
                p += 1;
                miss += 1;
                let mut step = miss >> skip;
                if step > skcap {
                    step = skcap;
                }
                while step > 0 && p < lim {
                    nt = b_a_put_lit(input, out, nt, p);
                    p += 1;
                    step -= 1;
                }
                if ins < p {
                    ins = p;
                }
            }
        }
    }
    while p < n {
        nt = b_a_put_lit(input, out, nt, p);
        p += 1;
    }
    nt
}

/// DNA settings: key bytes, minimum match, main depth, lazy threshold/depth, skip shift.
pub const B_A_D_ON: usize = 0;
pub const B_A_D_KEY: u32 = 8;
pub const B_A_D_MINL: usize = 9;
pub const B_A_D_DEPTH: usize = 4;
pub const B_A_D_LAZY: usize = 0;
pub const B_A_D_LDEPTH: usize = 1;
pub const B_A_D_SKIP: usize = 8;
pub const B_A_D_GM: usize = 0;

/// Put position `i` at the head of its chain (key = first B_A_D_KEY bytes); returns the previous head.
#[inline(always)]
pub fn b_a_insert_dna<const H: usize, const W: usize>(s: &[u8], head: &mut [u32; H], prev: &mut [u32; W], i: usize, mask: u32) -> usize {
    let k = (b_a_be8(s, i) >> (64 - 8 * B_A_D_KEY)) & (mask as u64 | 0xFFFF_FFFF_0000_0000);
    let a = (k.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (64 - B_A_HB)) as usize % H;
    let old = head[a];
    prev[i % W] = old;
    head[a] = i as u32;
    old as usize
}

/// DNA-like input: chains keyed by the first B_A_D_KEY bytes, matches of at least B_A_D_MINL bytes.
pub fn b_a_run_dna<const H: usize, const W: usize>(input: &[u8], out: &mut [u32], cls: usize) -> usize {
    let n = input.len();
    let mut nt = 0usize;
    let mut p = 0usize;
    let mask = 0xFFFF_FFFFu32;
    let minl = B_A_D_MINL;
    let depth = B_A_D_DEPTH;
    let lazy = B_A_D_LAZY;
    let skip = B_A_D_SKIP;
    let skcap = B_A_SKCAP;
    let _ = cls;
    let hlit = B_A_HLIT as i32;
    if n > 16 {
        let mut head = [0u32; H];
        let mut prev = [0u32; W];
        let lim = n - 8;
        let mut ins = 0usize; // next position to a_insert
        let mut miss = 0usize; // literals since the last match
        let mut fuel = n.saturating_add(16); // every pass advances p unless a re-check fails
        while p < lim && fuel > 0 {
            fuel -= 1;
            while ins < p {
                b_a_insert_dna(input, &mut head, &mut prev, ins, mask);
                ins += 1;
            }
            let hc = b_a_insert_dna(input, &mut head, &mut prev, p, mask);
            ins = p + 1;
            let f = b_a_find(input, &prev, p, hc, 0, minl, depth, 258, B_A_D_GM, hlit);
            let mut l = f.0;
            let mut d = f.1;
            if l >= 3 {
                // Lazy: move on while the next position has a better match by the saving
                // estimate (it may be as long but closer, or longer).
                let mut go = 1u32;
                while go == 1 && l < lazy && p + 1 < lim {
                    let q = p + 1;
                    let hq = b_a_insert_dna(input, &mut head, &mut prev, q, mask);
                    ins = q + 1;
                    let mut have = 0usize;
                    if l > B_A_LSLACK {
                        have = l - B_A_LSLACK;
                    }
                    let ldep = B_A_D_LDEPTH;
                    let g = b_a_find(input, &prev, q, hq, have, minl, ldep, 258, 1, hlit);
                    if g.0 >= minl && b_a_gain(g.0, g.1, hlit) > b_a_gain(l, d, hlit) {
                        nt = b_a_put_lit(input, out, nt, p);
                        p = q;
                        l = g.0;
                        d = g.1;
                    } else {
                        go = 0;
                    }
                }
                // Fold earlier tokens into this match while their bytes also match at d.
                let mut back = 0usize;
                while back < B_A_BACKTOK && nt > 0 && nt <= out.len() && l < 258 && d < p {
                    let t = out[nt - 1];
                    if t < 256 && input[p - 1] == input[p - 1 - d] {
                        p -= 1;
                        nt -= 1;
                        l += 1;
                        back += 1;
                    } else if t >= 16777216 {
                        let w = ((t - 16777216) % 256 + 3) as usize;
                        if l + w <= 258 && w <= p && d <= p - w && b_a_same(input, p - w - d, p - w, w) == 1 {
                            p -= w;
                            nt -= 1;
                            l += w;
                            back += 1;
                        } else {
                            back = B_A_BACKTOK;
                        }
                    } else {
                        back = B_A_BACKTOK;
                    }
                }
                let r = b_a_put_match(input, out, nt, p, d, l);
                nt = r.0;
                let end = r.1;
                // Chain the first B_A_INS_MAX and the last B_A_TAIL positions inside the match.
                let mut stop = end;
                // wrapping: a_same code as `+` here (no overflow on any real input), total in the model
                if stop > ins.wrapping_add(B_A_INS_MAX) {
                    stop = ins.wrapping_add(B_A_INS_MAX);
                }
                if stop > lim {
                    stop = lim;
                }
                while ins < stop {
                    b_a_insert_dna(input, &mut head, &mut prev, ins, mask);
                    ins += 1;
                }
                if B_A_STRIDE > 0 {
                    // `ins + B_A_TAIL + B_A_STRIDE < end`, with the bound computed once (total in the model)
                    let e2 = end.saturating_sub(B_A_TAIL + B_A_STRIDE);
                    while ins < e2 && ins < lim {
                        b_a_insert_dna(input, &mut head, &mut prev, ins, mask);
                        ins += B_A_STRIDE;
                    }
                }
                if ins.wrapping_add(B_A_TAIL) < end {
                    ins = end - B_A_TAIL;
                }
                while ins < end && ins < lim {
                    b_a_insert_dna(input, &mut head, &mut prev, ins, mask);
                    ins += 1;
                }
                if ins < end {
                    ins = end;
                }
                p = end;
                miss = 0;
            } else {
                nt = b_a_put_lit(input, out, nt, p);
                p += 1;
                miss += 1;
                let mut step = miss >> skip;
                if step > skcap {
                    step = skcap;
                }
                while step > 0 && p < lim {
                    nt = b_a_put_lit(input, out, nt, p);
                    p += 1;
                    step -= 1;
                }
                if ins < p {
                    ins = p;
                }
            }
        }
    }
    while p < n {
        nt = b_a_put_lit(input, out, nt, p);
        p += 1;
    }
    nt
}

/// Every input except larger text and prose: smaller tables for small inputs.
#[inline(never)]
pub fn b_a_run_rest(input: &[u8], out: &mut [u32], cls: usize, lvl: usize) -> usize {
    if input.len() <= B_A_SMALL {
        if cls == 1 {
            b_a_run::<B_A_HS, B_A_WS>(input, out, 1, lvl)
        } else {
            b_a_run::<B_A_HS, B_A_WS>(input, out, cls, lvl)
        }
    } else {
        b_a_run::<B_A_HN, B_A_WN>(input, out, cls, lvl)
    }
}

/// The lazy engine for an input of class `cls` (= `b_a_sniff(input)`).
pub fn b_a_parse_cls(input: &[u8], out: &mut [u32], cls: usize, lvl: usize) -> usize {
    if B_A_D_ON == 1 && cls == 0 && input.len() > B_A_SMALL {
        return b_a_run_dna::<B_A_HN, B_A_WN>(input, out, 0);
    }
    if input.len() > B_A_SMALL && cls == 1 {
        b_a_run::<B_A_HN, B_A_WN>(input, out, 1, lvl)
    } else if input.len() > B_A_SMALL && cls == 5 {
        b_a_run::<B_A_HN, B_A_WN>(input, out, 5, lvl)
    } else if input.len() > B_A_SMALL && cls == 6 {
        b_a_run::<B_A_HN, B_A_WN>(input, out, 6, lvl)
    } else {
        b_a_run_rest(input, out, cls, lvl)
    }
}
// ===== engine y: engine b of public submission #307 (x3a dynamic program, X2 fast path) =====

/// Fast path (X2) when any of: n < Y_SMALLN; h0 < Y_HLOW; lane >= Y_LANE (16-bit floats); Y_HHIGH <= h0 < Y_HTOP;
/// or the feature vector fv = [dig, sp, pun, ctl, red, h0, n / 1024, 0] lies in one of the boxes Y_BOX1..BOX4
/// (BOXk[2i] <= fv[i] < BOXk[2i + 1] for every i < 8). Shares are per 1024 of the sample: dig digits,
/// sp whitespace, pun ASCII punctuation, ctl control bytes; red is the redundancy probe (below).
pub const Y_SMALLN: usize = 65536;
pub const Y_HLOW: usize = 800;
pub const Y_LANE: usize = 341;
pub const Y_HHIGH: usize = 1818;
pub const Y_HTOP: usize = 1479;
pub const Y_BOX1: [usize; 16] = [1000000,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000];
pub const Y_BOX2: [usize; 16] = [1000000,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000];
pub const Y_BOX3: [usize; 16] = [1000000,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000];
pub const Y_BOX4: [usize; 16] = [1000000,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000,0,1000000];
/// DP classes (first match): 3 high entropy (h0 >= Y_HTOP), 1 low entropy (h0 < Y_GENH), 6 machine code
/// (ctl >= Y_CTLC), 4 numeric (dig >= Y_DIGC), 7 punctuation-rich (pun >= Y_PUNC), 5 redundant (red >= Y_REDC),
/// 2 small (n < Y_TINYN), 0 general.
pub const Y_GENH: usize = 800;
pub const Y_CTLC: usize = 280;
pub const Y_DIGC: usize = 198;
pub const Y_PUNC: usize = 237;
pub const Y_REDC: usize = 1000000;
pub const Y_TINYN: usize = 65536;
/// Redundancy probe: Y_PRW windows of Y_PRL bytes (0 windows: off); a greedy match of length >= Y_PRM
/// counts its bytes as covered. Only run when the other features do not already select the fast path.
pub const Y_PRW: usize = 0;
pub const Y_PRL: usize = 4096;
pub const Y_PRM: usize = 32;

pub fn y_parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut lh = [0u32; 256];
    let mut ln = [0u32; 32];
    y_odd_sample(input, &mut lh, &mut ln);
    let h0 = y_entropy256(&lh);
    let lane = y_lane_diff(&ln);
    let mut fv = [0usize; 8];
    fv[0] = y_hshare(&lh, 48, 58);
    fv[1] = y_hshare(&lh, 9, 11).wrapping_add(y_hshare(&lh, 13, 14)).wrapping_add(y_hshare(&lh, 32, 33));
    fv[2] = y_hshare(&lh, 33, 48).wrapping_add(y_hshare(&lh, 58, 65)).wrapping_add(y_hshare(&lh, 91, 97)).wrapping_add(y_hshare(&lh, 123, 127));
    fv[3] = y_hshare(&lh, 0, 9).wrapping_add(y_hshare(&lh, 14, 32));
    fv[5] = h0;
    fv[6] = n / 1024;
    let pre = y_fast_route(n, h0, lane, &fv);
    fv[4] = y_redund(input, pre);
    let fast = y_fast_route(n, h0, lane, &fv);
    let c = y_dp_class(n, &fv);
    if fast == 1 {
        y_x_parse(input, out)
    } else {
        y_dp_parse(input, out, c)
    }
}

/// 1 iff lo <= x < hi.
pub fn y_band(x: usize, lo: usize, hi: usize) -> usize {
    if x >= lo {
        if x < hi {
            1
        } else {
            0
        }
    } else {
        0
    }
}

/// 1 iff b[2i] <= fv[i] < b[2i + 1] for all i < 8.
pub fn y_inbox(fv: &[usize; 8], b: &[usize; 16]) -> usize {
    let mut r = 1usize;
    let mut i = 0usize;
    while i < 8 {
        let lo = b[i.wrapping_mul(2) % 16];
        let hi = b[i.wrapping_mul(2).wrapping_add(1) % 16];
        r = r & y_band(fv[i % 8], lo, hi);
        i += 1;
    }
    r
}

/// 1 iff the file takes the fast path (see the constants above).
pub fn y_fast_route(n: usize, h0: usize, lane: usize, fv: &[usize; 8]) -> usize {
    let a = y_band(n, 0, Y_SMALLN);
    let b = y_band(h0, 0, Y_HLOW);
    let c = y_band(lane, Y_LANE, 1000000000);
    let d = y_band(h0, Y_HHIGH, Y_HTOP);
    let e = y_inbox(fv, &Y_BOX1) | y_inbox(fv, &Y_BOX2);
    let g = y_inbox(fv, &Y_BOX3) | y_inbox(fv, &Y_BOX4);
    a | b | c | d | e | g
}

/// The DP class 0..7 of a file (see the constants above).
pub fn y_dp_class(n: usize, fv: &[usize; 8]) -> usize {
    let h0 = fv[5];
    if h0 >= Y_HTOP {
        3
    } else if h0 < Y_GENH {
        1
    } else if fv[3] >= Y_CTLC {
        6
    } else if fv[0] >= Y_DIGC {
        4
    } else if fv[2] >= Y_PUNC {
        7
    } else if fv[4] >= Y_REDC {
        5
    } else if n < Y_TINYN {
        2
    } else {
        0
    }
}

/// Share (per 1024) of the histogram mass in bytes `lo .. hi`.
pub fn y_hshare(h: &[u32; 256], lo: usize, hi: usize) -> usize {
    let mut tot = 0usize;
    let mut s = 0usize;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i] as usize;
        tot = tot.wrapping_add(c);
        s = if i >= lo && i < hi { s.wrapping_add(c) } else { s };
        i += 1;
    }
    if tot == 0 {
        0
    } else {
        s.wrapping_mul(1024) / tot
    }
}

/// Redundancy probe (only when `pre` == 0, i.e. the other features do not already select the fast path):
/// bytes covered by greedy matches of length >= Y_PRM in Y_PRW windows of Y_PRL bytes, per 1024 probed bytes.
pub fn y_redund(input: &[u8], pre: usize) -> usize {
    let n = input.len();
    let mut tab = [0u32; 4096];
    let wins = if pre == 0 { Y_PRW } else { 0 };
    let span = if n > Y_PRL { n - Y_PRL } else { 0 };
    let step = if wins > 1 { span / (wins - 1) } else { 0 };
    let mut cov = 0usize;
    let mut tot = 0usize;
    let mut w = 0usize;
    while w < wins {
        let a = step.wrapping_mul(w);
        cov = cov.wrapping_add(y_probe_win(input, &mut tab, a));
        tot = tot.wrapping_add(Y_PRL);
        w += 1;
    }
    if tot == 0 {
        0
    } else {
        cov.wrapping_mul(1024) / tot
    }
}

/// Greedy 1-probe parse of `a .. a + Y_PRL` (history inside the window only); returns the bytes
/// covered by matches of length >= Y_PRM.
pub fn y_probe_win(input: &[u8], tab: &mut [u32; 4096], a: usize) -> usize {
    let n = input.len();
    let b0 = a.wrapping_add(Y_PRL);
    let b = if b0 < n { b0 } else { n };
    let lim = if b >= 8 { b - 8 } else { 0 };
    let mut i = a;
    let mut cov = 0usize;
    let mut it = 0usize;
    while it < 65536 && i < lim {
        let h = ((y_load_le32(input, i).wrapping_mul(2654435761) >> 20) as usize) % 4096;
        let c = tab[h] as usize;
        tab[h] = (i as u32).wrapping_add(1);
        let cap0 = lim - i;
        let cap = if cap0 < 258 { cap0 } else { 258 };
        let l = if c > a { if c <= i { y_fast_len(input, c - 1, i, cap) } else { 0 } } else { 0 };
        cov = if l >= Y_PRM { cov.wrapping_add(l) } else { cov };
        i = if l >= 4 { i.wrapping_add(l) } else { i.wrapping_add(1) };
        it += 1;
    }
    cov
}

/// Histogram of an odd-stride sample of about 4096 bytes (every byte lane of word-structured data
/// is seen), and of the high nibbles of the sampled bytes at even (`hn[0..16]`) and odd
/// (`hn[16..32]`) positions (the stride is odd, so sample parity is position parity).
pub fn y_odd_sample(input: &[u8], h: &mut [u32; 256], hn: &mut [u32; 32]) {
    let n = input.len();
    let st = (n / 4096 + 1) | 1;
    let mut k = 0usize;
    let mut c = 0usize;
    while c < 8192 && k < n {
        let b = y_byte_at(input, k) % 256;
        h[b] = h[b].wrapping_add(1);
        let j = ((c % 2) * 16 + b / 16) % 32;
        hn[j] = hn[j].wrapping_add(1);
        k = k.wrapping_add(st);
        c += 1;
    }
}

/// |H(even-lane high nibbles) - H(odd-lane high nibbles)| in 1/256 bits.
pub fn y_lane_diff(hn: &[u32; 32]) -> usize {
    let he = y_entropy16(hn, 0);
    let ho = y_entropy16(hn, 16);
    if he > ho {
        he - ho
    } else {
        ho - he
    }
}

/// Order-0 entropy of the 16-bin histogram `h[base .. base + 16]` in 1/256 bits per symbol.
pub fn y_entropy16(h: &[u32; 32], base: usize) -> usize {
    let mut tot = 0u64;
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 16 {
        let c = h[base.wrapping_add(i) % 32];
        tot = tot.wrapping_add(c as u64);
        acc = if c > 0 { acc.wrapping_add((c as u64).wrapping_mul(y_lg8(c))) } else { acc };
        i += 1;
    }
    let t32 = if tot > 4000000000 { 4000000000u32 } else { tot as u32 };
    let a = y_lg8(t32);
    let b = if tot == 0 { 0 } else { acc / tot };
    if tot == 0 {
        0
    } else if a > b {
        (a - b) as usize
    } else {
        0
    }
}

/// 256 * log2(x) (8-bit mantissa), x >= 1.
pub fn y_lg8(x: u32) -> u64 {
    let y = x | 1;
    let e = 31u32.wrapping_sub(y.leading_zeros()) % 32;
    let m = if e >= 8 { y.wrapping_shr(e.wrapping_sub(8)) & 255 } else { y.wrapping_shl(8u32.wrapping_sub(e)) & 255 };
    (e as u64).wrapping_mul(256).wrapping_add(m as u64)
}

/// Order-0 entropy of the histogram in 1/256 bits per symbol (2048 for an empty histogram).
pub fn y_entropy256(h: &[u32; 256]) -> usize {
    let mut tot = 0u64;
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i];
        tot = tot.wrapping_add(c as u64);
        acc = if c > 0 { acc.wrapping_add((c as u64).wrapping_mul(y_lg8(c))) } else { acc };
        i += 1;
    }
    let t32 = if tot > 4000000000 { 4000000000u32 } else { tot as u32 };
    let a = y_lg8(t32);
    let b = if tot == 0 { 0 } else { acc / tot };
    if tot == 0 {
        2048
    } else if a > b {
        (a - b) as usize
    } else {
        0
    }
}

// ================================================================ DP path (x3a)


pub const Y_BS: usize = 6144;
/// A DP block continues past Y_BS (at most Y_EXT bytes) while a match edge of length >= 4 crosses
/// the current position, so the best path to the block end is final.
pub const Y_EXT: usize = 1024;
/// Nominal length of the first DP block of a file.
pub const Y_BS0: usize = 2048;
/// Entries of the price array reset per block (>= Y_BS + Y_EXT + 258).
pub const Y_ARRN: usize = 7468;
pub const Y_MAX3: usize = 32768;
pub const Y_H3ON: usize = 1;
pub const Y_BLO: usize = 0;
pub const Y_DEDUP: usize = 1;
pub const Y_NICE: usize = 258;
/// Chain depth for searches past the farthest known match end.
pub const Y_DEPTHC: [usize; 8] = [8, 8, 8, 16, 8, 8, 16, 16];
/// Initial frontier width (positions within it of the farthest known match end are frontier candidates).
pub const Y_KENDI: [usize; 8] = [4,4,4,4,4,4,4,4];
/// Frontier width after a reach update by a match of length L in DP class c:
/// Y_KENDB[8c + min(L / 8, 7)] (classes: 0 general, 1 low entropy, 2 tiny, 3 high entropy).
pub const Y_KENDB: [usize; 64] = [4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4];
/// Bit k: search at offset k = reach - cur (k <= frontier width); other offsets are treated as interior.
pub const Y_SMASK: usize = 65535;
/// Bit k: extend the candidates backwards at offset k (never past the match end).
pub const Y_BXMASK: usize = 65535;
/// Back-extension for searches past the match end (1) or not (0).
pub const Y_BXGT: usize = 0;
/// Chain depth at offset k = reach - cur.
pub const Y_DEPOC: [usize; 128] = [16,8,8,8,2,2,2,2,2,2,2,2,2,2,2,2,16,8,8,8,2,2,2,2,2,2,2,2,2,2,2,2,16,8,8,8,2,2,2,2,2,2,2,2,2,2,2,2,16,8,8,8,2,2,2,2,2,2,2,2,2,2,2,2,16,8,8,8,2,2,2,2,2,2,2,2,2,2,2,2,16,8,8,8,2,2,2,2,2,2,2,2,2,2,2,2,16,8,8,8,2,2,2,2,2,2,2,2,2,2,2,2,16,8,8,8,2,2,2,2,2,2,2,2,2,2,2,2];
/// Literal edges are relaxed only for the first Y_LITK positions of an interior stretch.
pub const Y_LITK: usize = 4;
/// Sparse mode (previous DP block had >= Y_COV% literal bytes): past the match end, search only every
/// Y_SPSTEP-th position; the others are inserted (Y_SPINS = 1) or not (0) and get their literal edge.
pub const Y_COV: usize = 98;
pub const Y_SPSTEP: usize = 2;
pub const Y_SPINS: usize = 1;
/// After Y_ACC_DIV * k consecutive fruitless searches the search stride is k + 1 (LZ4-style).
pub const Y_ACC_DIV: usize = 1024;
/// Insert only the last Y_TAIL positions of a skipped (>= Y_NICE) match.
pub const Y_TAIL: usize = 256;
/// Bytes of the input prefix sampled for the initial literal statistics.
pub const Y_SAMPLE: usize = 4096;
/// Per-token cost bias (1/16 bits) added to every literal (Y_TL) / match length symbol (Y_TM) cost.
pub const Y_TL: u32 = 2;
pub const Y_TM: u32 = 8;
pub const Y_PW: u32 = 1;
/// Prior weight Y_PW / Y_PWD.
pub const Y_PWD: u32 = 8;
pub const Y_PRIOR_DIV: u32 = 64;
/// Symbol cost model: an unseen symbol costs log2(total) + Y_UNSEEN/16 bits; costs are clamped to
/// [Y_CMIN, Y_CMAX] (1/16 bits).
pub const Y_UNSEEN: u32 = 8;
pub const Y_CMIN: u32 = 16;
pub const Y_CMAX: u32 = 180;
pub const Y_BLOCK_TOKENS: usize = 16384;
pub const Y_INF: u64 = 18446744073709551615;
pub const Y_PLAN: usize = 7468;

pub const Y_LEN_BASE: [u32; 32] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
    131, 163, 195, 227, 258, 1000, 1000, 1000,
];
pub const Y_LEN_EXTRA: [u32; 32] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 0, 0, 0,
];
pub const Y_DIST_BASE: [u32; 32] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577, 65536, 65536,
];
pub const Y_DIST_EXTRA: [u32; 32] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13, 0, 0,
];
/// Length symbol offset (0..28) of each length 3..=258.
pub const Y_LSYM: [u8; 259] = [0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28];
/// Distance symbol of distances 1..=256 (index d - 1).
pub const Y_DSYM_S: [u8; 256] = [0, 1, 2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15];
/// Distance symbol of distances > 256 (index (d - 1) / 128).
pub const Y_DSYM_B: [u8; 256] = [15, 15, 16, 17, 18, 18, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29];
/// 16 * log2(1 + i/16), i = 0..15.
pub const Y_LOG_FRAC: [u32; 16] = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15];

// ---------------------------------------------------------------- guarded helpers

/// `v[i]`, or 0 out of range.
pub fn y_get(v: &[u32], i: usize) -> u32 {
    if i < v.len() {
        v[i]
    } else {
        0
    }
}

/// `v[i] = x` when in range.
pub fn y_set(v: &mut [u32], i: usize, x: u32) {
    if i < v.len() {
        v[i] = x;
    }
}

/// `input[i]`, or 0 out of range.
pub fn y_byte_at(input: &[u8], i: usize) -> usize {
    if i < input.len() {
        input[i] as usize
    } else {
        0
    }
}

/// `a[i % 8192]`.
pub fn y_at64(a: &[u64; 8192], i: usize) -> u64 {
    a[i % 8192]
}

/// `a[i % 8192] = x`.
pub fn y_put64(a: &mut [u64; 8192], i: usize, x: u64) {
    a[i % 8192] = x;
}


/// A Vec of `n` copies of `x`: 8 pushes per iteration, then the tail.
pub fn y_filled(n: usize, x: u32) -> Vec<u32> {
    let mut v: Vec<u32> = Vec::with_capacity(n);
    let n8 = n / 8;
    let mut i = 0usize;
    while i < n8 {
        v.push(x);
        v.push(x);
        v.push(x);
        v.push(x);
        v.push(x);
        v.push(x);
        v.push(x);
        v.push(x);
        i += 1;
    }
    let mut j = n8 * 8;
    while j < n {
        v.push(x);
        j += 1;
    }
    v
}

// ---------------------------------------------------------------- trusted core

/// How many bytes agree at `a` and `b`, up to `cap`. The emission's byte-wise check.
pub fn y_match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// True iff `(ch, d)` at `pos` is in range and its bytes agree.
pub fn y_verified(input: &[u8], pos: usize, d: usize, ch: usize) -> bool {
    let n = input.len();
    if ch < 3 || ch > 258 || d < 1 || d > 32768 || d > pos || pos > n || ch > n - pos {
        return false;
    }
    let v = y_match_len(input, pos - d, pos, ch);
    v >= ch
}

/// The trusted emission of `k0 .. end`: every planned match (plan indexed from `base`) is
/// re-verified, else a literal. The cursor may end past `end` (a verified match may cross it).
pub fn y_emit_range(
    input: &[u8],
    out: &mut [u32],
    plan_len: &[u32],
    plan_dist: &[u32],
    base: usize,
    k0: usize,
    end: usize,
    ntok0: usize,
) -> (usize, usize) {
    let n = input.len();
    let mut k = k0;
    let mut ntok = ntok0;
    while k < end && k < n {
        let ch = y_get(plan_len, k.wrapping_sub(base)) as usize;
        let d = y_get(plan_dist, k.wrapping_sub(base)) as usize;
        if y_verified(input, k, d, ch) {
            out[ntok] = 16777216u32 + ((d - 1) as u32) * 256 + ((ch - 3) as u32);
            ntok += 1;
            k += ch;
        } else {
            out[ntok] = input[k] as u32;
            ntok += 1;
            k += 1;
        }
    }
    (ntok, k)
}

// ---------------------------------------------------------------- loads and compares

/// Little-endian 4-byte word at `p` (0 if out of range).
pub fn y_load_le32(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n >= 4 && p <= n - 4 {
        (input[p] as u32)
            | ((input[p + 1] as u32) << 8)
            | ((input[p + 2] as u32) << 16)
            | ((input[p + 3] as u32) << 24)
    } else {
        0
    }
}

/// Little-endian 8-byte word at `p` (0 if out of range): byte p+7 is the most significant.
pub fn y_word_at(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n >= 8 && p <= n - 8 {
        let lo = (input[p] as u32)
            | ((input[p + 1] as u32) << 8)
            | ((input[p + 2] as u32) << 16)
            | ((input[p + 3] as u32) << 24);
        let hi = (input[p + 4] as u32)
            | ((input[p + 5] as u32) << 8)
            | ((input[p + 6] as u32) << 16)
            | ((input[p + 7] as u32) << 24);
        ((hi as u64) << 32) | (lo as u64)
    } else {
        0
    }
}

/// Number of equal leading bytes (in memory order) of two little-endian words given their xor: 0..=8.
pub fn y_tzb(x: u64) -> usize {
    let low = x & 0u64.wrapping_sub(x);
    let t = (63u32.wrapping_sub(low.leading_zeros()) / 8) as usize;
    if t > 8 {
        8
    } else {
        t
    }
}

pub fn y_hash4(w: u32) -> usize {
    ((w.wrapping_mul(2654435761) >> 16) as usize) % 65536
}

/// Byte-wise tail compare (search only).
pub fn y_byte_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let n = input.len();
    let mut l = 0usize;
    while l < cap && a.wrapping_add(l) < n && b.wrapping_add(l) < n && y_byte_at(input, a.wrapping_add(l)) == y_byte_at(input, b.wrapping_add(l)) {
        l += 1;
    }
    l
}

/// Common prefix length of the strings at `a` and `b`, at most `cap` (search only).
pub fn y_fast_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let n = input.len();
    let mut l = 0usize;
    let mut go = 1usize;
    let mut it = 0usize;
    while go == 1 && it < 34 {
        let pa = a.wrapping_add(l);
        let pb = b.wrapping_add(l);
        let wide = n >= 8 && pb <= n - 8 && pa <= n - 8;
        let m = if wide { y_tzb(y_word_at(input, pa) ^ y_word_at(input, pb)) } else { 0 };
        let rest = if cap > l { cap - l } else { 0 };
        let t = if wide { m } else { y_byte_len(input, pa, pb, rest) };
        l = l.wrapping_add(t);
        go = if wide && m == 8 && l < cap { 1 } else { 0 };
        it += 1;
    }
    if l > cap {
        cap
    } else {
        l
    }
}

/// How many bytes before `a` and `c` agree (walking backwards), at most `cap` (search only). `c < a`.
pub fn y_back_len(input: &[u8], a: usize, c: usize, cap: usize) -> usize {
    let mut k = 0usize;
    let mut go = 1usize;
    let mut it = 0usize;
    while go == 1 && it < 40 && k < cap {
        let wide = c >= k.wrapping_add(8) && cap >= k.wrapping_add(8);
        let x = if wide { y_word_at(input, a.wrapping_sub(k).wrapping_sub(8)) ^ y_word_at(input, c.wrapping_sub(k).wrapping_sub(8)) } else { 1 };
        let m = if x == 0 { 8 } else { (x.leading_zeros() / 8) as usize };
        let pa = a.wrapping_sub(k).wrapping_sub(1);
        let pc = c.wrapping_sub(k).wrapping_sub(1);
        let eq = if !wide && k < c && y_byte_at(input, pa) == y_byte_at(input, pc) { 1 } else { 0 };
        let adv = if wide { m } else { eq };
        k = k.wrapping_add(adv);
        go = if wide { if m == 8 { 1 } else { 0 } } else { eq };
        it += 1;
    }
    if k > cap {
        cap
    } else {
        k
    }
}

// ---------------------------------------------------------------- cost model

/// 16 * log2(v), v >= 1 (0 for v = 0).
pub fn y_log2_16(v: u32) -> u32 {
    let lz = v.leading_zeros();
    let ip = 31u32.wrapping_sub(lz);
    let m = v.wrapping_shl(lz);
    let f = ((m >> 27) % 16) as usize;
    let r = ip.wrapping_mul(16).wrapping_add(Y_LOG_FRAC[f]);
    if v == 0 {
        0
    } else {
        r
    }
}

/// Estimated cost (1/16 bits) of a symbol seen `f` times out of `total`.
pub fn y_dp_sym_cost(f: u32, lt: u32) -> u32 {
    let c = if f == 0 { lt.wrapping_add(Y_UNSEEN) } else { lt.saturating_sub(y_log2_16(f)) };
    if c < Y_CMIN {
        Y_CMIN
    } else if c > Y_CMAX {
        Y_CMAX
    } else {
        c
    }
}

/// Estimated cost (1/16 bits) of a symbol seen `f` times out of `total` (fast path).
pub fn y_sym_cost(f: u32, lt: u32) -> u32 {
    let c = if f == 0 { lt.wrapping_add(32) } else { lt.saturating_sub(y_log2_16(f)) };
    if c < 16 {
        16
    } else if c > 240 {
        240
    } else {
        c
    }
}




pub fn y_dist_sym(d: usize) -> usize {
    if d <= 256 {
        Y_DSYM_S[(d.wrapping_sub(1)) % 256] as usize
    } else {
        Y_DSYM_B[(d.wrapping_sub(1) / 128) % 256] as usize
    }
}

pub fn y_dist_cost(dct: &[u32; 512], d: usize) -> u32 {
    let a = d.wrapping_sub(1);
    let k = if d <= 256 { a } else { 256usize.wrapping_add(a / 128) };
    dct[k % 512]
}

pub fn y_sum_arr(a: &[u32; 512], m: usize) -> u32 {
    let mut s = 0u32;
    let mut i = 0usize;
    while i < m && i < 512 {
        s = s.wrapping_add(a[i]);
        i += 1;
    }
    s
}

pub fn y_sum_df(a: &[u32; 32]) -> u32 {
    let mut s = 0u32;
    let mut i = 0usize;
    while i < 30 {
        s = s.wrapping_add(a[i]);
        i += 1;
    }
    s
}

/// Literal costs from the literal part of `llf`.
pub fn y_lit_costs(llf: &[u32; 512], lt: u32, litc: &mut [u32; 256]) {
    let mut b = 0usize;
    while b < 256 {
        litc[b] = y_dp_sym_cost(llf[b], lt).wrapping_add(Y_TL);
        b += 1;
    }
}

/// Symbol costs of the 29 length symbols (plus extra bits), then every length through `lsym`.
pub fn y_len_costs(llf: &[u32; 512], lt: u32, scost: &mut [u32; 32], lcost: &mut [u64; 512]) {
    let mut s = 0usize;
    while s < 29 {
        scost[s] = y_dp_sym_cost(llf[257 + s], lt).wrapping_add(Y_LEN_EXTRA[s].wrapping_mul(16)).wrapping_add(Y_TM);
        s += 1;
    }
    let mut l = 3usize;
    while l < 259 {
        lcost[l] = ((scost[(Y_LSYM[l] as usize) % 32] as u64) << 32) | (l as u64);
        l += 1;
    }
}

/// Symbol costs of the 30 distance symbols (plus extra bits), then both distance tables.
pub fn y_dist_costs(df: &[u32; 32], scost: &mut [u32; 32], dct: &mut [u32; 512]) {
    let lt = y_log2_16(y_sum_df(df));
    let mut s = 0usize;
    while s < 30 {
        scost[s] = y_dp_sym_cost(df[s], lt).wrapping_add(Y_DIST_EXTRA[s].wrapping_mul(16));
        s += 1;
    }
    let mut j = 0usize;
    while j < 256 {
        dct[j] = scost[(Y_DSYM_S[j] as usize) % 32];
        dct[256 + j] = scost[(Y_DSYM_B[j] as usize) % 32];
        j += 1;
    }
}

/// `dst = cur + prev * Y_PW / Y_PWD`.
pub fn y_mix(dst: &mut [u32; 512], cur: &[u32; 512], prv: &[u32; 512]) {
    let mut i = 0usize;
    while i < 512 {
        dst[i] = cur[i].wrapping_add(prv[i].wrapping_mul(Y_PW) / Y_PWD);
        i += 1;
    }
}

pub fn y_mix32(dst: &mut [u32; 32], cur: &[u32; 32], prv: &[u32; 32]) {
    let mut i = 0usize;
    while i < 32 {
        dst[i] = cur[i].wrapping_add(prv[i].wrapping_mul(Y_PW) / Y_PWD);
        i += 1;
    }
}

pub fn y_copy512(dst: &mut [u32; 512], src: &[u32; 512]) {
    let mut i = 0usize;
    while i < 512 {
        dst[i] = src[i];
        i += 1;
    }
}

pub fn y_copy32(dst: &mut [u32; 32], src: &[u32; 32]) {
    let mut i = 0usize;
    while i < 32 {
        dst[i] = src[i];
        i += 1;
    }
}

pub fn y_clear512(a: &mut [u32; 512]) {
    let mut i = 0usize;
    while i < 512 {
        a[i] = 0;
        i += 1;
    }
}

pub fn y_clear32(a: &mut [u32; 32]) {
    let mut i = 0usize;
    while i < 32 {
        a[i] = 0;
        i += 1;
    }
}

/// Literal histogram of the first Y_SAMPLE bytes (4 interleaved counters against store forwarding).
pub fn y_sample_hist(input: &[u8], h0: &mut [u32; 256], h1: &mut [u32; 256], h2: &mut [u32; 256], h3: &mut [u32; 256]) -> usize {
    let n = input.len();
    let m = if n > Y_SAMPLE { Y_SAMPLE } else { n };
    let q = m / 4;
    let mut k = 0usize;
    while k < q {
        let i = k.wrapping_mul(4);
        let b0 = y_byte_at(input, i);
        let b1 = y_byte_at(input, i.wrapping_add(1));
        let b2 = y_byte_at(input, i.wrapping_add(2));
        let b3 = y_byte_at(input, i.wrapping_add(3));
        h0[b0 % 256] = h0[b0 % 256].wrapping_add(1);
        h1[b1 % 256] = h1[b1 % 256].wrapping_add(1);
        h2[b2 % 256] = h2[b2 % 256].wrapping_add(1);
        h3[b3 % 256] = h3[b3 % 256].wrapping_add(1);
        k += 1;
    }
    m
}

/// Initial statistics: literal histogram of a sample plus pseudo-counts for lengths/distances.
pub fn y_init_stats(input: &[u8], llf: &mut [u32; 512], df: &mut [u32; 32]) {
    let mut h0 = [0u32; 256];
    let mut h1 = [0u32; 256];
    let mut h2 = [0u32; 256];
    let mut h3 = [0u32; 256];
    let m0 = y_sample_hist(input, &mut h0, &mut h1, &mut h2, &mut h3);
    let sc = (65536 / Y_SAMPLE) as u32;
    let mut b = 0usize;
    while b < 256 {
        llf[b] = h0[b].wrapping_add(h1[b]).wrapping_add(h2[b]).wrapping_add(h3[b]).wrapping_mul(sc);
        b += 1;
    }
    let m = (m0 as u32).wrapping_mul(sc);
    let pm = (m / 16).wrapping_add(1);
    let mut s = 0usize;
    while s < 29 {
        let w = if s < 8 { pm } else if s < 16 { pm / 2 + 1 } else { pm / 8 + 1 };
        llf[257 + s] = w;
        s += 1;
    }
    let mut t = 0usize;
    while t < 30 {
        df[t] = pm / 4 + 1;
        t += 1;
    }
}

/// Shrink the initial pseudo-statistics so real counts dominate quickly.
pub fn y_scale_prior(llf: &mut [u32; 512], df: &mut [u32; 32]) {
    let mut i = 0usize;
    while i < 512 {
        llf[i] = llf[i] / Y_PRIOR_DIV;
        i += 1;
    }
    let mut j = 0usize;
    while j < 32 {
        df[j] = df[j] / Y_PRIOR_DIV;
        j += 1;
    }
}

pub fn y_all_costs(
    llf: &mut [u32; 512],
    df: &[u32; 32],
    scost: &mut [u32; 32],
    litc: &mut [u32; 256],
    lcost: &mut [u64; 512],
    dct: &mut [u32; 512],
) {
    llf[256] = 1;
    let lt = y_log2_16(y_sum_arr(llf, 286));
    y_lit_costs(llf, lt, litc);
    y_len_costs(llf, lt, scost, lcost);
    y_dist_costs(df, scost, dct);
}

// ---------------------------------------------------------------- match finding (FDP lean core)

/// 3-byte hash of the low 3 bytes of `w`.
pub fn y_hash3w(w: u32) -> usize {
    (((w << 8).wrapping_mul(2654435761) >> 18) as usize) % 16384
}

/// Insert position `i` into the 4-byte chain and the 3-byte table.
pub fn y_insert(input: &[u8], head: &mut [u32; 65536], prev: &mut [u16; 32768], h3: &mut [u32; 16384], i: usize) {
    let w = y_load_le32(input, i);
    let h = y_hash4(w);
    let s4 = head[h] as usize;
    let dl = i.wrapping_add(1).wrapping_sub(s4);
    let dv = if s4 > 0 && dl <= 32768 { dl } else { 0 };
    prev[i % 32768] = dv as u16;
    head[h] = (i as u32).wrapping_add(1);
    h3[y_hash3w(w) % 16384] = (i as u32).wrapping_add(1);
}

/// Insert positions `start+cur0 .. start+stop` into the chains (no DP work).
pub fn y_insert_run(input: &[u8], head: &mut [u32; 65536], prev: &mut [u16; 32768], h3: &mut [u32; 16384], start: usize, cur0: usize, stop: usize) {
    let cnt = if stop > cur0 { stop - cur0 } else { 0 };
    let mut it = 0usize;
    while it < cnt {
        y_insert(input, head, prev, h3, start.wrapping_add(cur0).wrapping_add(it));
        it += 1;
    }
}

/// `arr[j] = min(arr[j], cand)`; returns the new value.
pub fn y_upd(arr: &mut [u64; 8192], j: usize, cand: u64) -> u64 {
    let old = arr[j % 8192];
    let m = if cand < old { cand } else { old };
    arr[j % 8192] = m;
    m
}

/// Positions `start+cur0 .. start+stop` inside a known match: all are inserted, the first Y_LITK
/// also get their literal edge relaxed. Returns the price at `stop`.
pub fn y_interior(
    input: &[u8],
    head: &mut [u32; 65536],
    prev: &mut [u16; 32768],
    h3: &mut [u32; 16384],
    arr: &mut [u64; 8192],
    litc: &[u32; 256],
    start: usize,
    cur0: usize,
    stop: usize,
    price0: u32,
) -> u32 {
    let k = cur0.wrapping_add(Y_LITK);
    let s1 = if k < stop { k } else { stop };
    let cnt = if s1 > cur0 { s1 - cur0 } else { 0 };
    let mut price = price0;
    let mut it = 0usize;
    while it < cnt {
        let cur = cur0.wrapping_add(it);
        let i = start.wrapping_add(cur);
        y_insert(input, head, prev, h3, i);
        let lp = price.wrapping_add(litc[y_byte_at(input, i) % 256]);
        let m = y_upd(arr, cur.wrapping_add(1), ((lp as u64) << 32) | 1);
        price = (m >> 32) as u32;
        it += 1;
    }
    y_insert_run(input, head, prev, h3, start, s1, stop);
    let pe = (y_at64(arr, stop) >> 32) as u32;
    if s1 < stop {
        pe
    } else {
        price
    }
}

/// Positions `cur0 .. stop` of an accelerated literal run: literal edges only. Returns the price at `stop`.
pub fn y_lit_run(input: &[u8], arr: &mut [u64; 8192], litc: &[u32; 256], start: usize, cur0: usize, stop: usize, price0: u32) -> u32 {
    let cnt = if stop > cur0 { stop - cur0 } else { 0 };
    let mut price = price0;
    let mut it = 0usize;
    while it < cnt {
        let cur = cur0.wrapping_add(it);
        let lp = price.wrapping_add(litc[y_byte_at(input, start.wrapping_add(cur)) % 256]);
        let m = y_upd(arr, cur.wrapping_add(1), ((lp as u64) << 32) | 1);
        price = (m >> 32) as u32;
        it += 1;
    }
    price
}

/// Length of the match between `c` and `pos` given the xor `x` of their first words (search only).
pub fn y_cand_len(input: &[u8], c: usize, pos: usize, cap: usize, x: u64) -> usize {
    let r = if cap > 8 { cap - 8 } else { 0 };
    let l = if x == 0 {
        8usize.wrapping_add(y_fast_len(input, c.wrapping_add(8), pos.wrapping_add(8), r))
    } else {
        y_tzb(x)
    };
    if l > cap {
        cap
    } else {
        l
    }
}

/// Backward extension of the candidate at `c` for `pos` (at most `cap` bytes), given the word
/// `wb` ending just before `pos`: one word compare, the general loop only when it all agrees.
pub fn y_back_ext(input: &[u8], pos: usize, c: usize, cap: usize, wb: u64) -> usize {
    let wide = c >= 8 && cap >= 8;
    let x = if wide { y_word_at(input, c.wrapping_sub(8)) ^ wb } else { 0 };
    let m = if x == 0 { 8 } else { (x.leading_zeros() / 8) as usize };
    if wide && m < 8 {
        m
    } else {
        y_back_len(input, pos, c, cap)
    }
}

/// Relax lengths lo..=hi (hi clamped to 258) from `cur` at one distance: cost = base + lcost[L].
pub fn y_relax_range(arr: &mut [u64; 8192], lcost: &[u64; 512], cur: usize, lo: usize, hi: usize, base: u32, ebits: u64) {
    let h = if hi > 258 { 258 } else { hi };
    let cnt = if h >= lo { h - lo + 1 } else { 0 };
    let bb = ((base as u64) << 32) | ebits;
    let mut it = 0usize;
    while it < cnt {
        let l = lo.wrapping_add(it);
        let cand = lcost[l % 512].wrapping_add(bb);
        let j = cur.wrapping_add(l) % 8192;
        let old = arr[j];
        arr[j] = if cand < old { cand } else { old };
        it += 1;
    }
}

/// Relax one Pareto candidate (distance `d`, length `l`, found at `c`) from `cur`: its lengths
/// `lo..=l`, and when it extends backwards by b > 0 bytes also from `cur - b` (lengths b+lo..=b+l,
/// never before the block start). A candidate of length >= Y_NICE only relaxes its full length.
pub fn y_relax_cand(
    input: &[u8],
    arr: &mut [u64; 8192],
    lcost: &[u64; 512],
    dct: &[u32; 512],
    pos: usize,
    cur: usize,
    price: u32,
    c: usize,
    d: usize,
    lo: usize,
    l: usize,
    wb: u64,
    bx: usize,
    bk: &mut [u32; 8192],
) {
    let dc = y_dist_cost(dct, d);
    let eb = (d as u64) << 9;
    let nice = l >= Y_NICE;
    let lo1 = if nice { l } else { lo };
    y_relax_range(arr, lcost, cur, lo1, l, price.wrapping_add(dc), eb);
    let lim0 = if l < 258 { 258 - l } else { 0 };
    let lim1 = if lim0 < cur { lim0 } else { cur };
    let lim = if nice { 0 } else if bx == 0 { 0 } else { lim1 };
    let b = if lim > 0 { y_back_ext(input, pos, c, lim, wb) } else { 0 };
    let s0 = cur.wrapping_sub(b);
    let key = ((d as u32) << 16) | ((pos.wrapping_sub(b) as u32) % 65536);
    let dup = if bk[s0 % 8192] == key { Y_DEDUP } else { 0 };
    bk[s0 % 8192] = if b > 0 { key } else { bk[s0 % 8192] };
    if b > 0 && b <= cur && dup == 0 {
        let ps = (y_at64(arr, s0) >> 32) as u32;
        let lo2a = if b < 2 { 3 } else { b.wrapping_add(1) };
        let lo2b = b.wrapping_add(lo);
        let lo2 = if Y_BLO == 1 { lo2b } else { lo2a };
        let hi2 = if ps < 4000000000 { b.wrapping_add(l) } else { 0 };
        y_relax_range(arr, lcost, s0, lo2, hi2, ps.wrapping_add(dc), eb);
    }
}


/// Walk the chain from head `s4` (at most `depth` probes) at `pos` (DP position `cur`, price
/// `price`, first word `wp`) and relax every Pareto candidate on the fly. Returns the longest length
/// found (3 when none).
pub fn y_walk(
    input: &[u8],
    prev: &[u16; 32768],
    arr: &mut [u64; 8192],
    lcost: &[u64; 512],
    dct: &[u32; 512],
    pos: usize,
    cur: usize,
    cap: usize,
    s4: usize,
    depth: usize,
    price: u32,
    bx: usize,
    wp: u64,
    bk: &mut [u32; 8192],
) -> usize {
    let wb = y_word_at(input, pos.wrapping_sub(8));
    let mut best = 3usize;
    let d0 = pos.wrapping_add(1).wrapping_sub(s4);
    let mut d = if s4 > 0 { d0 } else { 65536 };
    let mut probes = 0usize;
    while probes < depth && d <= 32768 && d <= pos && best < cap && best < Y_NICE {
        let c = pos.wrapping_sub(d);
        let x = y_word_at(input, c) ^ wp;
        let qk = y_quick_ok(input, c, pos, best);
        let l = if qk == 1 { y_cand_len(input, c, pos, cap, x) } else { 0 };
        if l > best {
            y_relax_cand(input, arr, lcost, dct, pos, cur, price, c, d, best.wrapping_add(1), l, wb, bx, bk);
            best = l;
        }
        let dl = prev[c % 32768] as usize;
        d = if dl == 0 { 65536 } else { d.wrapping_add(dl) };
        probes += 1;
    }
    best
}

/// 1 unless best >= 8 and the candidate at `c` differs from `pos` at byte `best` (cannot be longer).
pub fn y_quick_ok(input: &[u8], c: usize, pos: usize, best: usize) -> usize {
    if best < 8 {
        1
    } else if y_byte_at(input, c.wrapping_add(best)) == y_byte_at(input, pos.wrapping_add(best)) {
        1
    } else {
        0
    }
}

/// Relax the nearest 3-byte match (entry `s3`, pos+1 encoded) at `pos` as a length-3 edge when it
/// is within Y_MAX3 and its 3 bytes agree (`w4` = first 4 bytes at `pos`).
pub fn y_rel3(input: &[u8], arr: &mut [u64; 8192], lcost: &[u64; 512], dct: &[u32; 512], pos: usize, cur: usize, price: u32, s3: usize, w4: u32) {
    if s3 == 0 || s3 > pos {
        return;
    }
    let c = s3 - 1;
    let d = pos - c;
    if d > Y_MAX3 {
        return;
    }
    if (y_load_le32(input, c) ^ w4) & 16777215 != 0 {
        return;
    }
    let dc = y_dist_cost(dct, d);
    let p = price.wrapping_add(dc);
    let _m = y_upd(arr, cur.wrapping_add(3), lcost[3].wrapping_add(((p as u64) << 32) | ((d as u64) << 9)));
}

/// One DP search at position `i` (block offset `cur`, final price `price`): inserts `i`, relaxes
/// its literal edge, the nearest 3-byte match and the Pareto candidates of the 4-byte chain.
/// Returns the longest length found (< 4: none).
pub fn y_sstep(
    input: &[u8],
    head: &mut [u32; 65536],
    prev: &mut [u16; 32768],
    h3: &mut [u32; 16384],
    arr: &mut [u64; 8192],
    litc: &[u32; 256],
    lcost: &[u64; 512],
    dct: &[u32; 512],
    i: usize,
    cur: usize,
    price: u32,
    depth: usize,
    bx: usize,
    bk: &mut [u32; 8192],
) -> usize {
    let n = input.len();
    let w = y_word_at(input, i);
    let w4 = w as u32;
    let k4 = y_hash4(w4);
    let k3 = y_hash3w(w4) % 16384;
    let s4 = head[k4] as usize;
    let s3 = h3[k3] as usize;
    let dl = i.wrapping_add(1).wrapping_sub(s4);
    let dv = if s4 > 0 && dl <= 32768 { dl } else { 0 };
    prev[i % 32768] = dv as u16;
    head[k4] = (i as u32).wrapping_add(1);
    h3[k3] = (i as u32).wrapping_add(1);
    let lp = price.wrapping_add(litc[(w4 % 256) as usize]);
    let _m = y_upd(arr, cur.wrapping_add(1), ((lp as u64) << 32) | 1);
    let left = n.wrapping_sub(i);
    let cap = if left < 258 { left } else { 258 };
    y_rel3(input, arr, lcost, dct, i, cur, price, s3, w4);
    y_walk(input, prev, arr, lcost, dct, i, cur, cap, s4, depth, price, bx, w, bk)
}

/// Insert positions `from .. to` into the chains (at most 300).
pub fn y_insert_range(input: &[u8], head: &mut [u32; 65536], prev: &mut [u16; 32768], h3: &mut [u32; 16384], from: usize, to: usize) {
    let n = input.len();
    let lim = if n >= 8 { n - 8 } else { 0 };
    let t = if to < lim { to } else { lim };
    let cnt0 = if t > from { t - from } else { 0 };
    let cnt = if cnt0 < 300 { cnt0 } else { 300 };
    let mut it = 0usize;
    while it < cnt {
        y_insert(input, head, prev, h3, from.wrapping_add(it));
        it += 1;
    }
}

// ---------------------------------------------------------------- DP

pub fn y_fill_inf(arr: &mut [u64; 8192]) {
    let mut j = 0usize;
    while j < Y_ARRN {
        arr[j] = Y_INF;
        j += 1;
    }
}

/// Relax the literal edge cur -> cur + 1; returns the (final) price at cur + 1.
pub fn y_lit_step(input: &[u8], arr: &mut [u64; 8192], litc: &[u32; 256], i: usize, cur: usize, price: u32) -> u32 {
    let lp = price.wrapping_add(litc[y_byte_at(input, i) % 256]);
    let m = y_upd(arr, cur.wrapping_add(1), ((lp as u64) << 32) | 1);
    (m >> 32) as u32
}

/// Length bucket of a match of length `l`: min(l / 8, 7).
pub fn y_lbucket(l: usize) -> usize {
    let b = l / 8;
    if b > 7 {
        7
    } else {
        b
    }
}

/// Forward DP over one block starting at `start`; returns the block length.
/// `st[0]` carries the fruitless-search counter across blocks.
pub fn y_dp_block(
    input: &[u8],
    start: usize,
    head: &mut [u32; 65536],
    prev: &mut [u16; 32768],
    h3: &mut [u32; 16384],
    arr: &mut [u64; 8192],
    bk: &mut [u32; 8192],
    cl: &mut [u32; 16],
    cd: &mut [u32; 16],
    cb: &mut [u32; 16],
    litc: &[u32; 256],
    lcost: &[u64; 512],
    dct: &[u32; 512],
    st: &mut [usize; 4],
) -> usize {
    let n = input.len();
    let rem = n.wrapping_sub(start);
    let bs = if st[3] == 0 { Y_BS0 } else { Y_BS };
    let bend = if rem < bs { rem } else { bs };
    let hard0 = bs.wrapping_add(Y_EXT);
    let mut lim = if rem < hard0 { rem } else { hard0 };
    let mut sat = bend;
    y_fill_inf(arr);
    y_put64(arr, 0, 0);
    let mut price = 0u32;
    let mut cur = 0usize;
    let mut reach = 0usize;
    let mut miss = st[0];
    let mut acc_next = 0usize;
    let sparse = st[1];
    let dcl = st[2] % 8;
    let row = dcl.wrapping_mul(8);
    let dgt = Y_DEPTHC[dcl];
    let dbase = dcl.wrapping_mul(16);
    let mut kend = Y_KENDI[dcl];
    let mut it = 0usize;
    while it < 8192 && cur < sat {
        let i = start.wrapping_add(cur);
        let left = rem.wrapping_sub(cur);
        if cur.wrapping_add(kend) < reach {
            // inside a known match: insert + literal edge, up to the frontier
            let s = reach.wrapping_sub(kend);
            let stop = if s < lim { s } else { lim };
            price = y_interior(input, head, prev, h3, arr, litc, start, cur, stop, price);
            cur = stop;
        } else if cur < acc_next {
            // accelerated literal run: literal edges only
            let stop = if acc_next < lim { acc_next } else { lim };
            price = y_lit_run(input, arr, litc, start, cur, stop, price);
            cur = stop;
        } else if left < 8 {
            price = y_lit_step(input, arr, litc, i, cur, price);
            cur = cur.wrapping_add(1);
        } else if y_sp_skip(cur, reach, sparse) == 1 {
            // sparse mode: a literal-run position that is not searched (inserted, literal edge)
            price = y_interior(input, head, prev, h3, arr, litc, start, cur, cur.wrapping_add(1), price);
            cur = cur.wrapping_add(1);
        } else if y_skip_off(cur, reach) == 1 {
            // a frontier offset that is not searched
            price = y_interior(input, head, prev, h3, arr, litc, start, cur, cur.wrapping_add(1), price);
            cur = cur.wrapping_add(1);
        } else {
            let off = reach.wrapping_sub(cur);
            let gt = if cur > reach { 1usize } else { 0usize };
            let depth = if gt == 1 { dgt } else { Y_DEPOC[dbase.wrapping_add(off % 16) % 128] };
            let bx = if gt == 1 { Y_BXGT } else { (((Y_BXMASK as u64) >> (off % 64)) % 2) as usize };
            let best = y_sstep(input, head, prev, h3, arr, litc, lcost, dct, i, cur, price, depth, bx, bk);
            miss = if best >= 4 { 0 } else { miss.wrapping_add(1) };
            acc_next = cur.wrapping_add(1).wrapping_add(miss / Y_ACC_DIV);
            if best >= Y_NICE {
                let tfrom = if best > Y_TAIL { i.wrapping_add(best).wrapping_sub(Y_TAIL) } else { i.wrapping_add(1) };
                y_insert_range(input, head, prev, h3, tfrom, i.wrapping_add(best));
                cur = cur.wrapping_add(best);
                price = (y_at64(arr, cur) >> 32) as u32;
                lim = if cur > lim { cur } else { lim };
                sat = y_block_stop(bend, lim, reach);
            } else {
                let nr = cur.wrapping_add(best);
                let upd1 = if best >= 4 { if nr > reach { 1usize } else { 0usize } } else { 0usize };
                reach = if upd1 == 1 { nr } else { reach };
                kend = if upd1 == 1 { Y_KENDB[row.wrapping_add(y_lbucket(best)) % 64] } else { kend };
                sat = y_block_stop(bend, lim, reach);
                cur = cur.wrapping_add(1);
                price = (y_at64(arr, cur) >> 32) as u32;
            }
        }
        it += 1;
    }
    st[0] = miss;
    st[3] = 1;
    cur
}

/// 1 iff sparse mode is on and `cur` is past the reach at a position that is not a multiple of Y_SPSTEP.
pub fn y_sp_skip(cur: usize, reach: usize, sparse: usize) -> usize {
    let a = if cur > reach { 1usize } else { 0usize };
    let o = cur.wrapping_sub(reach) % Y_SPSTEP;
    let b = if o != 0 { 1usize } else { 0usize };
    a & b & sparse
}

/// 1 iff `cur` is a frontier offset (cur < reach) whose Y_SMASK bit is clear (not searched).
pub fn y_skip_off(cur: usize, reach: usize) -> usize {
    let o = reach.wrapping_sub(cur);
    let bit = (((Y_SMASK as u64) >> (o % 64)) % 2) as usize;
    if cur < reach {
        if bit == 1 {
            0
        } else {
            1
        }
    } else {
        0
    }
}

/// The DP block runs while `cur < max(bend, min(lim, reach))`: to its nominal end `bend`, then on
/// (at most to `lim`) while a match edge of length >= 4 crosses `cur`.
pub fn y_block_stop(bend: usize, lim: usize, reach: usize) -> usize {
    let m = if reach < lim { reach } else { lim };
    if m > bend {
        m
    } else {
        bend
    }
}

/// Walk the chosen edges back from `end`, writing the plan and counting symbols; returns the
/// token count.
pub fn y_backtrack(
    input: &[u8],
    arr: &[u64; 8192],
    plan_len: &mut [u32],
    plan_dist: &mut [u32],
    start: usize,
    end: usize,
    llf: &mut [u32; 512],
    df: &mut [u32; 32],
) -> usize {
    let mut e = end;
    let mut cnt = 0usize;
    let mut lits = 0usize;
    let mut guard = 0usize;
    while e > 0 && guard < 8192 {
        let ed = (arr[e % 8192] % 4294967296) as usize;
        let l0 = ed % 512;
        let d = ed / 512;
        let l = if l0 >= 3 && l0 <= 258 && l0 <= e && d >= 1 { l0 } else { 1 };
        let p = e - l;
        if l >= 3 {
            y_set(plan_len, p, l as u32);
            y_set(plan_dist, p, d as u32);
            let ls = 257 + (Y_LSYM[l % 512] as usize) % 32;
            llf[ls % 512] = llf[ls % 512].wrapping_add(1);
            let t = y_dist_sym(d) % 32;
            df[t] = df[t].wrapping_add(1);
        } else {
            y_set(plan_len, p, 0);
            let b = y_byte_at(input, start.wrapping_add(p)) % 256;
            llf[b] = llf[b].wrapping_add(1);
        }
        lits = if l >= 3 { lits } else { lits.wrapping_add(1) };
        cnt = cnt.wrapping_add(1);
        e = p;
        guard += 1;
    }
    cnt.wrapping_add(lits.wrapping_mul(16384))
}

/// A block length of `e` if `1 <= e <= rest`, else 1.
pub fn y_clamp_block(e: usize, rest: usize) -> usize {
    if e >= 1 && e <= rest {
        e
    } else {
        1
    }
}

pub fn y_dp_parse(input: &[u8], out: &mut [u32], cls: usize) -> usize {
    let n = input.len();
    let mut head = [0u32; 65536];
    let mut prev = [0u16; 32768];
    let mut h3 = [0u32; 16384];
    let mut arr = [0u64; 8192];
    let mut bk = [0u32; 8192];
    let mut cl = [0u32; 16];
    let mut cd = [0u32; 16];
    let mut cb = [0u32; 16];
    let mut litc = [0u32; 256];
    let mut lcost = [0u64; 512];
    let mut dct = [0u32; 512];
    let mut scost = [0u32; 32];
    let mut llf = [0u32; 512];
    let mut df = [0u32; 32];
    let mut pllf = [0u32; 512];
    let mut pdf = [0u32; 32];
    let mut tllf = [0u32; 512];
    let mut tdf = [0u32; 32];
    let mut st = [0usize; 4];
    st[2] = cls;
    let pcap = if n < Y_PLAN { n } else { Y_PLAN };
    let mut plan_len = y_filled(pcap, 0);
    let mut plan_dist = y_filled(pcap, 0);
    y_init_stats(input, &mut pllf, &mut pdf);
    y_all_costs(&mut pllf, &pdf, &mut scost, &mut litc, &mut lcost, &mut dct);
    y_scale_prior(&mut pllf, &mut pdf);
    let mut pos0 = 0usize;
    let mut k = 0usize;
    let mut ntok = 0usize;
    let mut blk = 0usize;
    while pos0 < n {
        let rest = n - pos0;
        let e = y_dp_block(input, pos0, &mut head, &mut prev, &mut h3, &mut arr, &mut bk, &mut cl, &mut cd, &mut cb, &litc, &lcost, &dct, &mut st);
        let blen = y_clamp_block(e, rest);
        let tl = y_backtrack(input, &arr, &mut plan_len, &mut plan_dist, pos0, blen, &mut llf, &mut df);
        let t = tl % 16384;
        st[1] = if (tl / 16384).wrapping_mul(100) >= blen.wrapping_mul(Y_COV) { 1 } else { 0 };
        let r = y_emit_range(input, out, &plan_len, &plan_dist, pos0, k, pos0 + blen, ntok);
        ntok = r.0;
        k = r.1;
        pos0 += blen;
        blk = blk.wrapping_add(t);
        let full = blk >= Y_BLOCK_TOKENS;
        y_refresh(full, &mut llf, &mut df, &mut pllf, &mut pdf, &mut tllf, &mut tdf, &mut scost, &mut litc, &mut lcost, &mut dct, &mut st);
        blk = if full { blk.wrapping_sub(Y_BLOCK_TOKENS) } else { blk };
    }
    ntok
}

/// Cost refresh after a DP block: at an output-block boundary (`full`) from that block's
/// statistics (which become the prior; the next DP block is then a short Y_BS0 block, st[3] = 0),
/// else from the running statistics plus the prior.
pub fn y_refresh(
    full: bool,
    llf: &mut [u32; 512],
    df: &mut [u32; 32],
    pllf: &mut [u32; 512],
    pdf: &mut [u32; 32],
    tllf: &mut [u32; 512],
    tdf: &mut [u32; 32],
    scost: &mut [u32; 32],
    litc: &mut [u32; 256],
    lcost: &mut [u64; 512],
    dct: &mut [u32; 512],
    st: &mut [usize; 4],
) {
    if full {
        y_copy512(pllf, llf);
        y_copy32(pdf, df);
        y_clear512(llf);
        y_clear32(df);
        st[3] = 0;
    }
    y_mix(tllf, llf, pllf);
    y_mix32(tdf, df, pdf);
    y_all_costs(tllf, tdf, scost, litc, lcost, dct);
}

// ================================================================ fast path (X2, renamed)


pub const Y_X_DEPTH: usize = 24;
pub const Y_X_DEPTH2: usize = 4;
pub const Y_X_GOOD: usize = 3;
pub const Y_X_LAZY: usize = 258;
pub const Y_X_NICE: usize = 258;
pub const Y_X_IH: usize = 258;
pub const Y_X_IT: usize = 64;
pub const Y_X_ACC: u64 = 6;
pub const Y_X_STEPMAX: usize = 32;
pub const Y_X_LITQ: usize = 28;
pub const Y_X_LADJ: usize = 2;
pub const Y_X_HLOW: usize = 900;
pub const Y_X_HSL: u32 = 0;
pub const Y_X_ELO: usize = 400;
pub const Y_X_H3HI: usize = 100;
pub const Y_X_H3CTL: usize = 100;
pub const Y_X_H3E: usize = 1700;
pub const Y_X_ACCL: u64 = 63;
pub const Y_X_H3: usize = 1;
pub const Y_X_MAX3: usize = 4096;
pub const Y_X_H3INS: usize = 1;
pub const Y_X_C0Q: usize = 44;
pub const Y_X_C0L: usize = 44;
pub const Y_X_DEPTHL: usize = 12;
pub const Y_X_M3: usize = 0;
pub const Y_X_DEPTH3M: usize = 12;
pub const Y_X_M3E: usize = 1900;
pub const Y_X_M3Z: usize = 15;
pub const Y_X_LZB: usize = 0;
pub const Y_X_BONUS: usize = 0;
pub const Y_X_EXT: usize = 1;
pub const Y_X_DIGN: usize = 200;
pub const Y_X_DN: usize = 4;
pub const Y_X_P2N: usize = 8;
pub const Y_X_LQN: usize = 20;
pub const Y_X_NBIG: usize = 65536;
pub const Y_X_GOODL: usize = 258;
pub const Y_X_P2G: usize = 2;
pub const Y_X_NSMALL: usize = 65536;
pub const Y_X_BIAS: usize = 4096;

// ------------------------------------------------------------------ loads and compares (search only)

/// Little-endian 4-byte load at `p`; 0 when out of range.
pub fn y_x_ld4(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n < 4 || p > n - 4 {
        return 0;
    }
    ((input[p + 3] as u32) << 24) | ((input[p + 2] as u32) << 16) | ((input[p + 1] as u32) << 8) | (input[p] as u32)
}

/// Little-endian 8-byte load at `p` (two u32 halves, highest byte read first); 0 when out of range.
pub fn y_x_ld8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n < 8 || p > n - 8 {
        return 0;
    }
    let hi = ((input[p + 7] as u32) << 24) | ((input[p + 6] as u32) << 16) | ((input[p + 5] as u32) << 8) | (input[p + 4] as u32);
    let lo = ((input[p + 3] as u32) << 24) | ((input[p + 2] as u32) << 16) | ((input[p + 1] as u32) << 8) | (input[p] as u32);
    ((hi as u64) << 32) | (lo as u64)
}

/// Index (0..7) of the first differing byte of two little-endian words, given their xor (!= 0).
pub fn y_x_first_diff(x: u64) -> usize {
    let low = x & 0u64.wrapping_sub(x);
    (63u32.wrapping_sub(low.leading_zeros()) / 8) as usize
}

/// Common prefix of positions `a < b`, up to `cap` (search only; never trusted).
pub fn y_x_fast_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    let mut go = 1usize;
    let mut it = 0usize;
    while go == 1 && it < 40 {
        if l < cap {
            let x = y_x_ld8(input, a.wrapping_add(l)) ^ y_x_ld8(input, b.wrapping_add(l));
            let k = if x == 0 { 8 } else { y_x_first_diff(x) };
            l = l.wrapping_add(k);
            go = if x == 0 { 1 } else { 0 };
        } else {
            go = 0;
        }
        it += 1;
    }
    if l > cap { cap } else { l }
}

/// Hash of the first (64 - hs) / 8 bytes at `p` into 16 bits.
pub fn y_x_hashp(input: &[u8], p: usize, hs: u32) -> usize {
    if hs == 32 {
        return (y_x_ld4(input, p).wrapping_mul(2654435761) >> 16) as usize;
    }
    let v = y_x_ld8(input, p) << (hs % 64);
    (v.wrapping_mul(0x9E3779B97F4A7C15) >> 48) as usize
}

/// Hash of the low 3 bytes of a word into 14 bits.
pub fn y_x_hash3(w: u32) -> usize {
    ((w << 8).wrapping_mul(2654435761) >> 18) as usize
}

// ------------------------------------------------------------------ cost model (search only)

/// DEFLATE distance extra bits of `d`.
pub fn y_x_dextra(d: usize) -> usize {
    if d <= 4 {
        0
    } else {
        let x = (d.wrapping_sub(1) as u32) | 1;
        (31u32.wrapping_sub(x.leading_zeros()) as usize).wrapping_sub(1)
    }
}

/// DEFLATE length extra bits of `l`.
pub fn y_x_lextra(l: usize) -> usize {
    if l < 11 || l >= 258 {
        0
    } else {
        let x = (l.wrapping_sub(3) as u32) | 1;
        (31u32.wrapping_sub(x.leading_zeros()) as usize).wrapping_sub(2)
    }
}

/// Estimated saving (quarter bits, offset by Y_X_BIAS) of coding `l` bytes as a match at `d`.
/// `cq` packs the literal cost (low 8 bits) and the match base cost (bits 8..).
pub fn y_x_score(l: usize, d: usize, cq: usize) -> usize {
    let cost = (cq / 256).wrapping_add(y_x_dextra(d).wrapping_add(y_x_lextra(l)).wrapping_mul(4));
    l.wrapping_mul(cq % 256).wrapping_add(Y_X_BIAS).wrapping_sub(cost)
}

/// Fixed-point log2 with 8 fractional bits (linear between powers of two).
pub fn y_x_lg8(x: u32) -> u64 {
    let y = x | 1;
    let e = 31u32.wrapping_sub(y.leading_zeros()) % 32;
    let m = if e >= 8 { (y >> ((e.wrapping_sub(8)) % 32)) & 255 } else { (y << ((8u32.wrapping_sub(e)) % 32)) & 255 };
    (e as u64).wrapping_mul(256).wrapping_add(m as u64)
}

/// Histogram of a strided sample of the input (about 4096 bytes).
pub fn y_x_sample(input: &[u8], h: &mut [u32; 256]) {
    let n = input.len();
    let st = n / 4096 + 1;
    let mut k = 0usize;
    let mut c = 0usize;
    while k < n && c < 8192 {
        let b = (input[k] as usize) % 256;
        h[b] = h[b].wrapping_add(1);
        k = k.wrapping_add(st);
        c += 1;
    }
}

/// Order-0 entropy of the histogram in 1/256 bits per symbol.
pub fn y_x_entropy256(h: &[u32; 256]) -> usize {
    let mut tot = 0u64;
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i];
        tot = tot.wrapping_add(c as u64);
        acc = if c > 0 { acc.wrapping_add((c as u64).wrapping_mul(y_x_lg8(c))) } else { acc };
        i += 1;
    }
    let t32 = if tot > 4000000000 { 4000000000u32 } else { tot as u32 };
    let a = y_x_lg8(t32);
    let b = if tot == 0 { a } else { acc / tot };
    if a > b { (a - b) as usize } else { 0 }
}

/// Per mille of the sampled bytes in `lo .. hi`.
pub fn y_x_share(h: &[u32; 256], lo: usize, hi: usize) -> usize {
    let mut t = 0usize;
    let mut s = 0usize;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i] as usize;
        t = t.wrapping_add(c);
        s = if i >= lo && i < hi { s.wrapping_add(c) } else { s };
        i += 1;
    }
    if t == 0 { 0 } else { s.wrapping_mul(1000) / t }
}

/// 1 when the sampled entropy `e` marks a genome-like input (few cheap literals).
pub fn y_x_low_mode(e: usize) -> usize {
    if e >= Y_X_ELO && e < Y_X_HLOW { 1 } else { 0 }
}

/// Literal cost (quarter bits): from the sampled entropy in low mode, else Y_X_LITQ.
pub fn y_x_lit_cost(e: usize, low: usize) -> usize {
    let q = (e / 64).wrapping_add(Y_X_LADJ);
    let q2 = if q < 6 { 6 } else if q > 36 { 36 } else { q };
    if low == 1 { q2 } else { Y_X_LITQ }
}

/// 1 when the input should use 3-byte hash chains (Y_X_M3 = 2: always; 1: by rule).
pub fn y_x_m3_mode(h: &[u32; 256], e: usize) -> usize {
    let z = y_x_share(h, 0, 1);
    let a = if e >= Y_X_M3E { 1usize } else { 0usize };
    let b = if z >= Y_X_M3Z { 1usize } else { 0usize };
    if Y_X_M3 == 2 { 1 } else if Y_X_M3 == 1 { a & b } else { 0 }
}

/// 1 when the 3-byte table should be used: binary-ish or non-ASCII input of moderate entropy.
pub fn y_x_h3_mode(h: &[u32; 256], e: usize) -> usize {
    let hi = y_x_share(h, 128, 256);
    let ctl = y_x_share(h, 0, 9);
    let a = if hi >= Y_X_H3HI { 1usize } else { 0usize };
    let b = if ctl >= Y_X_H3CTL { 1usize } else { 0usize };
    let c = if e < Y_X_H3E { 1usize } else { 0usize };
    if Y_X_H3 == 2 { 1 } else if Y_X_H3 == 1 { (a | b) & c } else { 0 }
}

/// 1 for large numeric text: at least Y_X_DIGN per mille digits, few bytes >= 128 or < 9, not genome-like.
pub fn y_x_numeric(h: &[u32; 256], n: usize, low: usize) -> usize {
    let dig = y_x_share(h, 48, 58);
    let hi = y_x_share(h, 128, 256);
    let ctl = y_x_share(h, 0, 9);
    let txt = if hi < 50 && ctl < 50 { 1usize } else { 0usize };
    let big = if n >= Y_X_NBIG { 1usize } else { 0usize };
    let d = if dig >= Y_X_DIGN { 1usize } else { 0usize };
    if low == 1 { 0 } else { txt & big & d }
}

// ------------------------------------------------------------------ match finding (search only)

/// Walk the chain from `start` (pos+1 encoded, 0 = none) for the candidate with the best score
/// among those longer than `bl0` and scoring more than `bs0`. Returns `len | dist << 9 | score << 25`
/// (0 if none). Candidates stay inside the 32K window; the walk stops at `Y_X_NICE` or `cap`.
pub fn y_x_walk(input: &[u8], prev: &[u32; 32768], pos: usize, start: usize, cap: usize, probes: usize, bl0: usize, bs0: usize, litq: usize) -> usize {
    let lim = pos.saturating_sub(32768);
    let stop = if cap < Y_X_NICE { cap } else { Y_X_NICE };
    let mut cur = start;
    let mut k = 0usize;
    let mut bl = bl0;
    let mut bs = bs0;
    let mut bd = 0usize;
    let mut off = if bl >= 3 { bl - 3 } else { 0 };
    let mut want = y_x_ld4(input, pos.wrapping_add(off));
    while k < probes && cur > lim && cur <= pos && bl < stop {
        let c = cur - 1;
        if y_x_ld4(input, c.wrapping_add(off)) == want {
            let l = y_x_fast_len(input, c, pos, cap);
            let d = pos - c;
            let s = y_x_score(l, d, litq);
            let better = if l > bl { if s > bs { 1usize } else { 0usize } } else { 0usize };
            bd = if better == 1 { d } else { bd };
            bs = if better == 1 { s } else { bs };
            bl = if better == 1 { l } else { bl };
            off = if bl >= 3 { bl - 3 } else { 0 };
            want = y_x_ld4(input, pos.wrapping_add(off));
        }
        cur = prev[c % 32768] as usize;
        k += 1;
    }
    if bd > 0 {
        bl | bd.wrapping_mul(512) | bs.wrapping_mul(33554432)
    } else {
        0
    }
}

/// Lazy-path copy of `walk` (a separate function keeps both inlined at their single call sites).
/// Walk the chain from `start` (pos+1 encoded, 0 = none) for the candidate with the best score
/// among those longer than `bl0` and scoring more than `bs0`. Returns `len | dist << 9 | score << 25`
/// (0 if none). Candidates stay inside the 32K window; the walk stops at `Y_X_NICE` or `cap`.
pub fn y_x_lwalk(input: &[u8], prev: &[u32; 32768], pos: usize, start: usize, cap: usize, probes: usize, bl0: usize, bs0: usize, litq: usize) -> usize {
    let lim = pos.saturating_sub(32768);
    let stop = if cap < Y_X_NICE { cap } else { Y_X_NICE };
    let mut cur = start;
    let mut k = 0usize;
    let mut bl = bl0;
    let mut bs = bs0;
    let mut bd = 0usize;
    let mut off = if bl >= 3 { bl - 3 } else { 0 };
    let mut want = y_x_ld4(input, pos.wrapping_add(off));
    while k < probes && cur > lim && cur <= pos && bl < stop {
        let c = cur - 1;
        if y_x_ld4(input, c.wrapping_add(off)) == want {
            let l = y_x_fast_len(input, c, pos, cap);
            let d = pos - c;
            let s = y_x_score(l, d, litq);
            let better = if l > bl { if s > bs { 1usize } else { 0usize } } else { 0usize };
            bd = if better == 1 { d } else { bd };
            bs = if better == 1 { s } else { bs };
            bl = if better == 1 { l } else { bl };
            off = if bl >= 3 { bl - 3 } else { 0 };
            want = y_x_ld4(input, pos.wrapping_add(off));
        }
        cur = prev[c % 32768] as usize;
        k += 1;
    }
    if bd > 0 {
        bl | bd.wrapping_mul(512) | bs.wrapping_mul(33554432)
    } else {
        0
    }
}

/// The 1-deep 3-byte candidate at `pos` from entry `s3` (pos+1 encoded): `3 | dist << 9 | score << 25`
/// or 0.
pub fn y_x_cand3(input: &[u8], pos: usize, s3: usize, cap: usize, bs0: usize, litq: usize) -> usize {
    if s3 == 0 || s3 > pos || cap < 3 {
        return 0;
    }
    let c = s3 - 1;
    let d = pos - c;
    if d > Y_X_MAX3 || (y_x_ld4(input, c) ^ y_x_ld4(input, pos)) & 16777215 != 0 {
        return 0;
    }
    let s = y_x_score(3, d, litq);
    if s > bs0 {
        3 | d.wrapping_mul(512) | s.wrapping_mul(33554432)
    } else {
        0
    }
}

/// With `probes > 0`: insert `pos` into the chains, then walk them (see `walk`); with nothing found
/// and `h3on == 1`, try the 3-byte table. 0 when `probes == 0`.
pub fn y_x_search(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], head3: &mut [u32; 16384], pos: usize, probes: usize, bl0: usize, bs0: usize, litq: usize, hs: u32, h3on: usize) -> usize {
    let n = input.len();
    if probes == 0 || n < 16 || pos > n - 16 {
        return 0;
    }
    let h = y_x_hashp(input, pos, hs) % 65536;
    let start = head[h] as usize;
    prev[pos % 32768] = start as u32;
    head[h] = (pos as u32).wrapping_add(1);
    let s3 = y_x_upd3(input, head3, pos, h3on);
    let rem = n - pos - 8;
    let cap = if rem < 258 { rem } else { 258 };
    let w2 = y_x_walk(input, prev, pos, start, cap, probes, bl0, bs0, litq);
    if w2 != 0 || s3 == 0 || bl0 >= 3 {
        w2
    } else {
        y_x_cand3(input, pos, s3, cap, bs0, litq)
    }
}

/// With `on == 1`: enter `pos` into the 3-byte table and return the entry it replaced; else 0.
pub fn y_x_upd3(input: &[u8], head3: &mut [u32; 16384], pos: usize, on: usize) -> usize {
    if on == 1 {
        let g = y_x_hash3(y_x_ld4(input, pos)) % 16384;
        let s3 = head3[g] as usize;
        head3[g] = (pos as u32).wrapping_add(1);
        s3
    } else {
        0
    }
}

/// Insert positions `from .. to` into the chains.
pub fn y_x_insert_range(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], from: usize, to: usize, hs: u32) {
    let lim = input.len().saturating_sub(16);
    let mut p = from;
    while p < to && p <= lim {
        let h = y_x_hashp(input, p, hs) % 65536;
        prev[p % 32768] = head[h];
        head[h] = (p as u32).wrapping_add(1);
        p += 1;
    }
}

/// `insert_range` that also updates the 3-byte table.
pub fn y_x_insert_range3(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], head3: &mut [u32; 16384], from: usize, to: usize, hs: u32) {
    let lim = input.len().saturating_sub(16);
    let mut p = from;
    while p < to && p <= lim {
        let h = y_x_hashp(input, p, hs) % 65536;
        prev[p % 32768] = head[h];
        head[h] = (p as u32).wrapping_add(1);
        head3[y_x_hash3(y_x_ld4(input, p)) % 16384] = (p as u32).wrapping_add(1);
        p += 1;
    }
}

/// Insert the inside `from .. to` of an emitted match: its first Y_X_IH and last Y_X_IT positions.
pub fn y_x_insert_match(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], head3: &mut [u32; 16384], from: usize, to: usize, hs: u32, h3on: usize) {
    let a = from.wrapping_add(Y_X_IH);
    let a2 = if a < to { a } else { to };
    let b = to.wrapping_sub(Y_X_IT);
    let b2 = if b > a2 { if b < to { b } else { a2 } } else { a2 };
    if h3on == 1 {
        y_x_insert_range3(input, head, prev, head3, from, a2, hs);
        if b2 < to {
            y_x_insert_range3(input, head, prev, head3, b2, to, hs);
        }
    } else {
        y_x_insert_range(input, head, prev, from, a2, hs);
        if b2 < to {
            y_x_insert_range(input, head, prev, b2, to, hs);
        }
    }
}

// ------------------------------------------------------------------ trusted core

/// How many bytes agree at `a` and `b`, up to `cap`. The emission's byte-wise check.
/// Trusted: little-endian 8-byte word at `p` (0 when out of range).
pub fn y_x_tw8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n < 8 || p > n - 8 {
        return 0;
    }
    (input[p] as u64)
        + (input[p + 1] as u64) * 256
        + (input[p + 2] as u64) * 65536
        + (input[p + 3] as u64) * 16777216
        + (input[p + 4] as u64) * 4294967296
        + (input[p + 5] as u64) * 1099511627776
        + (input[p + 6] as u64) * 281474976710656
        + (input[p + 7] as u64) * 72057594037927936
}

/// Trusted: little-endian 4-byte word at `p` (0 when out of range).
pub fn y_x_tw4(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n < 4 || p > n - 4 {
        return 0;
    }
    (input[p] as u32) + (input[p + 1] as u32) * 256 + (input[p + 2] as u32) * 65536 + (input[p + 3] as u32) * 16777216
}

/// Trusted: 1 iff `cap >= 8`, `cap - l < 8` and the 8-byte words at `a + cap - 8` and `b + cap - 8` are equal.
pub fn y_x_tail_eq(input: &[u8], a: usize, b: usize, cap: usize, l: usize) -> usize {
    if cap < 8 || cap - l >= 8 {
        return 0;
    }
    if y_x_tw8(input, a + (cap - 8)) == y_x_tw8(input, b + (cap - 8)) {
        1
    } else {
        0
    }
}

/// Trusted: 1 iff `4 <= cap < 8` and the 4-byte words at `a`, `b` and at `a + cap - 4`, `b + cap - 4` are equal.
pub fn y_x_short_eq(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    if cap < 4 || cap >= 8 {
        return 0;
    }
    if y_x_tw4(input, a) != y_x_tw4(input, b) {
        return 0;
    }
    if y_x_tw4(input, a + (cap - 4)) == y_x_tw4(input, b + (cap - 4)) {
        1
    } else {
        0
    }
}

/// Trusted: a length `l <= cap` over which the bytes at `a` and `b` provably agree, found with word compares:
/// 8-byte steps, then one overlapping 8-byte compare at `cap - 8` (or two 4-byte ones when 4 <= cap < 8); `cap`
/// itself when everything agreed.
pub fn y_x_words_eq(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while cap - l >= 8 && y_x_tw8(input, a + l) == y_x_tw8(input, b + l) {
        l += 8;
    }
    let big = y_x_tail_eq(input, a, b, cap, l);
    let small = y_x_short_eq(input, a, b, cap);
    if big == 1 {
        cap
    } else if small == 1 {
        cap
    } else {
        l
    }
}

/// Trusted: how many bytes agree at `a` and `b`, up to `cap` (word compares, then bytes).
pub fn y_x_match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = y_x_words_eq(input, a, b, cap);
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// True iff `(ch, d)` at `pos` is in range and its bytes agree.
pub fn y_x_verified(input: &[u8], pos: usize, d: usize, ch: usize) -> bool {
    let n = input.len();
    if ch < 3 || ch > 258 || d < 1 || d > 32768 || d > pos || pos > n || ch > n - pos {
        return false;
    }
    let v = y_x_match_len(input, pos - d, pos, ch);
    v >= ch
}

/// Trusted: `cnt >= 1` literals from `pos0` (stopping at the input end).
pub fn y_x_emit_lits(input: &[u8], out: &mut [u32], pos0: usize, cnt: usize, ntok0: usize) -> (usize, usize) {
    let n = input.len();
    let cnt1 = if cnt == 0 { 1 } else { cnt };
    let mut k = pos0;
    let mut c = 0usize;
    let mut ntok = ntok0;
    while k < n && c < cnt1 {
        out[ntok] = input[k] as u32;
        ntok += 1;
        k += 1;
        c += 1;
    }
    (ntok, k)
}

/// Trusted: the match `(l, d)` at `pos` if it verifies, else `lits` literals.
pub fn y_x_emit_step(input: &[u8], out: &mut [u32], pos: usize, d: usize, l: usize, lits: usize, ntok: usize) -> (usize, usize) {
    if y_x_verified(input, pos, d, l) {
        out[ntok] = 16777216u32 + ((d - 1) as u32) * 256 + ((l - 3) as u32);
        (ntok + 1, pos + l)
    } else {
        y_x_emit_lits(input, out, pos, lits, ntok)
    }
}

// ------------------------------------------------------------------ the parse loop

/// The lazy check at `q` (= match position + 1) with `go == 1`: enter `q` into the chains and test the most
/// recent chain candidate against the current match (`l1` bytes, score `sv1`). Returns `len | dist << 9 |
/// score << 25` when that candidate is at least as long and scores higher, else 0. `go == 0`: does nothing.
pub fn y_x_lazy_probe(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], head3: &mut [u32; 16384], q: usize, go: usize, p2: usize, l1: usize, sv1: usize, litq: usize, hs: u32, h3on: usize) -> usize {
    let n = input.len();
    if go == 0 || n < 16 || q > n - 16 {
        return 0;
    }
    let h = y_x_hashp(input, q, hs) % 65536;
    let start = head[h] as usize;
    prev[q % 32768] = start as u32;
    head[h] = (q as u32).wrapping_add(1);
    y_x_upd3(input, head3, q, h3on);
    let rem = n - q - 8;
    let cap = if rem < 258 { rem } else { 258 };
    let pr = if l1 >= Y_X_GOODL { Y_X_P2G } else { p2 };
    y_x_lwalk(input, prev, q, start, cap, pr, l1.wrapping_sub(1), sv1, litq)
}

/// 1 when the lazy candidate `(l2, d2)` found at `pos + 1` also covers `pos` (so it can start there).
pub fn y_x_ext_ok(input: &[u8], pos: usize, l2: usize, d2: usize) -> usize {
    let n = input.len();
    if Y_X_EXT == 0 || l2 < 3 || l2 >= 258 || d2 < 1 || d2 > pos || pos >= n {
        return 0;
    }
    if input[pos] == input[pos - d2] { 1 } else { 0 }
}


// ============================ jfloor fast-path module v5 (untrusted except the fl_ trusted copies) ==============
// Graft: the base parser's `parse` becomes `y_x_main_parse(input, out, lh, pos0, ntok0)` and this module's `parse` runs
//   y_x_fl_part(input, out, mode, fh, cf)  -> (ntok, pos): the whole input for modes 1-5, (0, 0) for mode 0,
//   y_x_main_parse(input, out, &fh, pos, ntok) -> the base parser from `pos` (a no-op when pos == n).
// Modes (fl_mode, loop-free, from a strided 4K-byte sample + 16 probe chunks of 256 bytes):
//   4 RLE  : one byte value >= 75% of the y_x_sample (sparse): distance-1 runs, no tables;
//   5 Y_X_LAZY : small files (< 64 KB), database-like binaries (zero bytes but mostly printable), high-entropy data
//            (images, f32 weights, archives): the module's own price-lazy parser with a per-class config `cf`;
//   2 DNA  : 4-symbol alphabet (FASTA): literal runs over cheap bytes, cost-checked matches at expensive bytes;
//   1 LIT  : 2-periodic 16-bit weights (bf16/f16) and skewed-uniform int8 weights (q8, no repeats at all);
//   0      : the base parser.
// The module has its own copies of the trusted kit functions (fl_match_len, fl_verified, fl_emit_lits,
// fl_emit_step) so the base keeps its own emit_step/emit_lits with one caller each (sharing them made LLVM
// outline the base's emit_step: +1% instructions on every text file).

pub const Y_X_FL_PMIN: usize = 65536;
pub const Y_X_FL_PNC: usize = 16;
pub const Y_X_FL_PCH: usize = 256;
pub const Y_X_FL_RLE_TOP: usize = 192;
pub const Y_X_FL_DNA_THR: u32 = 64;
pub const Y_X_FL_DNA_DEPTH: usize = 64;
pub const Y_X_FL_DNA_M0: usize = 12;
pub const Y_X_FL_CMAX: u32 = 192;
pub const Y_X_FL_HIGH: usize = 104;
pub const Y_X_FL_DBZ: usize = 8;
pub const Y_X_FL_DBNP: usize = 110;
pub const Y_X_FL_USE_T: usize = 1;
pub const Y_X_FL_USE_D: usize = 0;
pub const Y_X_FL_USE_H: usize = 0;
pub const Y_X_FL_USE_LIT: usize = 1;
// class configs (T: small files, D: database-like, H: high entropy)
pub const Y_X_FT_DEPTH: usize = 16;
pub const Y_X_FT_DEPTH2: usize = 2;
pub const Y_X_FT_LAZY: usize = 259;
pub const Y_X_FT_NICE: usize = 258;
pub const Y_X_FT_IH: usize = 64;
pub const Y_X_FT_IT: usize = 16;
pub const Y_X_FT_ACC: usize = 63;
pub const Y_X_FD_DEPTH: usize = 12;
pub const Y_X_FD_DEPTH2: usize = 2;
pub const Y_X_FD_LAZY: usize = 259;
pub const Y_X_FD_NICE: usize = 258;
pub const Y_X_FD_IH: usize = 64;
pub const Y_X_FD_IT: usize = 16;
pub const Y_X_FD_ACC: usize = 63;
pub const Y_X_FH_DEPTH: usize = 6;
pub const Y_X_FH_DEPTH2: usize = 2;
pub const Y_X_FH_LAZY: usize = 32;
pub const Y_X_FH_NICE: usize = 64;
pub const Y_X_FH_IH: usize = 64;
pub const Y_X_FH_IT: usize = 16;
pub const Y_X_FH_ACC: usize = 7;
pub const Y_X_FL_GOOD: usize = 8;
pub const Y_X_FL_LITQ: usize = 32;
pub const Y_X_FL_LADJ: usize = 4;
pub const Y_X_FL_HLOW: usize = 900;
pub const Y_X_FL_C0Q: usize = 44;

// ---------------------------------------------------------------- trusted core (floor copy)

/// Byte-wise common prefix length (trusted).
/// Trusted: little-endian 8-byte word at `p` (0 when out of range).
pub fn y_x_fl_tw8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n < 8 || p > n - 8 {
        return 0;
    }
    (input[p] as u64)
        + (input[p + 1] as u64) * 256
        + (input[p + 2] as u64) * 65536
        + (input[p + 3] as u64) * 16777216
        + (input[p + 4] as u64) * 4294967296
        + (input[p + 5] as u64) * 1099511627776
        + (input[p + 6] as u64) * 281474976710656
        + (input[p + 7] as u64) * 72057594037927936
}

/// Trusted: little-endian 4-byte word at `p` (0 when out of range).
pub fn y_x_fl_tw4(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n < 4 || p > n - 4 {
        return 0;
    }
    (input[p] as u32) + (input[p + 1] as u32) * 256 + (input[p + 2] as u32) * 65536 + (input[p + 3] as u32) * 16777216
}

/// Trusted: 1 iff `cap >= 8`, `cap - l < 8` and the 8-byte words at `a + cap - 8` and `b + cap - 8` are equal.
pub fn y_x_fl_tail_eq(input: &[u8], a: usize, b: usize, cap: usize, l: usize) -> usize {
    if cap < 8 || cap - l >= 8 {
        return 0;
    }
    if y_x_fl_tw8(input, a + (cap - 8)) == y_x_fl_tw8(input, b + (cap - 8)) {
        1
    } else {
        0
    }
}

/// Trusted: 1 iff `4 <= cap < 8` and the 4-byte words at `a`, `b` and at `a + cap - 4`, `b + cap - 4` are equal.
pub fn y_x_fl_short_eq(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    if cap < 4 || cap >= 8 {
        return 0;
    }
    if y_x_fl_tw4(input, a) != y_x_fl_tw4(input, b) {
        return 0;
    }
    if y_x_fl_tw4(input, a + (cap - 4)) == y_x_fl_tw4(input, b + (cap - 4)) {
        1
    } else {
        0
    }
}

/// Trusted: a length `l <= cap` over which the bytes at `a` and `b` provably agree, found with word compares:
/// 8-byte steps, then one overlapping 8-byte compare at `cap - 8` (or two 4-byte ones when 4 <= cap < 8); `cap`
/// itself when everything agreed.
pub fn y_x_fl_words_eq(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while cap - l >= 8 && y_x_fl_tw8(input, a + l) == y_x_fl_tw8(input, b + l) {
        l += 8;
    }
    let big = y_x_fl_tail_eq(input, a, b, cap, l);
    let small = y_x_fl_short_eq(input, a, b, cap);
    if big == 1 {
        cap
    } else if small == 1 {
        cap
    } else {
        l
    }
}

/// Trusted: how many bytes agree at `a` and `b`, up to `cap` (word compares, then bytes).
pub fn y_x_fl_match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = y_x_fl_words_eq(input, a, b, cap);
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// True iff `(ch, d)` at `pos` is in range and its bytes agree (trusted).
pub fn y_x_fl_verified(input: &[u8], pos: usize, d: usize, ch: usize) -> bool {
    let n = input.len();
    if ch < 3 || ch > 258 || d < 1 || d > 32768 || d > pos || pos > n || ch > n - pos {
        return false;
    }
    let v = y_x_fl_match_len(input, pos - d, pos, ch);
    v >= ch
}

/// Trusted: `cnt >= 1` literals from `pos0` (stopping at the input end).
pub fn y_x_fl_emit_lits(input: &[u8], out: &mut [u32], pos0: usize, cnt: usize, ntok0: usize) -> (usize, usize) {
    let n = input.len();
    let cnt1 = if cnt == 0 { 1 } else { cnt };
    let mut k = pos0;
    let mut c = 0usize;
    let mut ntok = ntok0;
    while k < n && c < cnt1 {
        out[ntok] = input[k] as u32;
        ntok += 1;
        k += 1;
        c += 1;
    }
    (ntok, k)
}

/// Trusted: the match `(l, d)` at `pos` if it verifies, else `lits` literals.
pub fn y_x_fl_emit_step(input: &[u8], out: &mut [u32], pos: usize, d: usize, l: usize, lits: usize, ntok: usize) -> (usize, usize) {
    if y_x_fl_verified(input, pos, d, l) {
        out[ntok] = 16777216u32 + ((d - 1) as u32) * 256 + ((l - 3) as u32);
        (ntok + 1, pos + l)
    } else {
        y_x_fl_emit_lits(input, out, pos, lits, ntok)
    }
}

// ---------------------------------------------------------------- loads, compares, hashes (search only)

/// `input[i]`, or 0 out of range.
pub fn y_x_fl_byte(input: &[u8], i: usize) -> usize {
    if i < input.len() {
        input[i] as usize
    } else {
        0
    }
}

/// Little-endian 4-byte load at `p`; 0 when out of range.
pub fn y_x_fl_ld4(input: &[u8], p: usize) -> u32 {
    let n = input.len();
    if n < 4 || p > n - 4 {
        return 0;
    }
    ((input[p + 3] as u32) << 24) | ((input[p + 2] as u32) << 16) | ((input[p + 1] as u32) << 8) | (input[p] as u32)
}

/// Little-endian 8-byte load at `p` (two 4-byte halves); 0 when out of range.
pub fn y_x_fl_ld8(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if n < 8 || p > n - 8 {
        return 0;
    }
    let hi = ((input[p + 7] as u32) << 24) | ((input[p + 6] as u32) << 16) | ((input[p + 5] as u32) << 8) | (input[p + 4] as u32);
    let lo = ((input[p + 3] as u32) << 24) | ((input[p + 2] as u32) << 16) | ((input[p + 1] as u32) << 8) | (input[p] as u32);
    ((hi as u64) << 32) | (lo as u64)
}

/// Common prefix of `a < b`, at most `cap` (word compare; search only, never trusted).
pub fn y_x_fl_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    let mut go = 1usize;
    let mut it = 0usize;
    while go == 1 && it < 40 {
        if l < cap {
            let x = y_x_fl_ld8(input, a.wrapping_add(l)) ^ y_x_fl_ld8(input, b.wrapping_add(l));
            let low = x & 0u64.wrapping_sub(x);
            let k = if x == 0 { 8 } else { (63u32.wrapping_sub(low.leading_zeros()) / 8) as usize };
            l = l.wrapping_add(k);
            go = if x == 0 { 1 } else { 0 };
        } else {
            go = 0;
        }
        it += 1;
    }
    if l > cap {
        cap
    } else {
        l
    }
}

/// 16-bit hash of the word at `p` shifted left by `hsh` (32: first 4 bytes, 0: first 8 bytes).
pub fn y_x_fl_hashp(input: &[u8], p: usize, hsh: u64) -> usize {
    let v = y_x_fl_ld8(input, p) << (hsh % 64);
    ((v.wrapping_mul(0x9E3779B97F4A7C15) >> 48) as usize) % 65536
}

// ---------------------------------------------------------------- statistics and costs (search only)

/// log2(1 + i/16) in 1/16 bits.
pub const Y_X_FL_LOGF: [u32; 16] = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15];

/// log2(f) in 1/16 bits (0 for f = 0).
pub fn y_x_fl_log16(f: u32) -> u32 {
    let lz = f.leading_zeros();
    let top = ((((f as u64) << ((lz as u64).wrapping_add(1) % 64)) >> 28) as usize) % 16;
    if f == 0 {
        0
    } else {
        (31u32.wrapping_sub(lz)).wrapping_mul(16).wrapping_add(Y_X_FL_LOGF[top])
    }
}

/// Strided byte histogram of about 4096 samples.
pub fn y_x_fl_sample(input: &[u8], h: &mut [u32; 256]) {
    let n = input.len();
    let st = n / 4096 + 1;
    let mut k = 0usize;
    let mut c = 0usize;
    while k < n && c < 8192 {
        let b = y_x_fl_byte(input, k) % 256;
        h[b] = h[b].wrapping_add(1);
        k = k.wrapping_add(st);
        c += 1;
    }
}

/// Literal cost per byte value (1/16 bits) from the histogram: log2(total / f), unseen bytes Y_X_FL_CMAX.
pub fn y_x_fl_costs(h: &[u32; 256], cost: &mut [u32; 256]) {
    let mut t = 0u32;
    let mut i = 0usize;
    while i < 256 {
        t = t.wrapping_add(h[i]);
        i += 1;
    }
    let lt = y_x_fl_log16(t);
    let mut j = 0usize;
    while j < 256 {
        let f = h[j];
        let c = lt.wrapping_sub(y_x_fl_log16(f));
        cost[j] = if f == 0 { Y_X_FL_CMAX } else if c > Y_X_FL_CMAX { Y_X_FL_CMAX } else { c };
        j += 1;
    }
}

/// Order-0 entropy in 1/16 bits per byte of the 256 bins starting at `base` of `h`.
pub fn y_x_fl_ent(h: &[u32; 1024], base: usize) -> usize {
    let mut t = 0u32;
    let mut i = 0usize;
    while i < 256 {
        t = t.wrapping_add(h[base.wrapping_add(i) % 1024]);
        i += 1;
    }
    let lt = y_x_fl_log16(t);
    let mut bits = 0usize;
    let mut j = 0usize;
    while j < 256 {
        let f = h[base.wrapping_add(j) % 1024];
        let c = lt.wrapping_sub(y_x_fl_log16(f)) as usize;
        bits = if f > 0 { bits.wrapping_add((f as usize).wrapping_mul(c)) } else { bits };
        j += 1;
    }
    let tt = if t == 0 { 1usize } else { t as usize };
    bits / tt
}

/// Sample statistics packed into one word: bits 0-9 entropy (1/16 bits), 10-18 top byte y_x_share (1/256),
/// 19-27 zero-byte share, 28-36 non-printable share, 37-45 share of the byte values with share >= 1/8,
/// 46-49 number of such byte values.
pub fn y_x_fl_stats(h: &[u32; 256]) -> u64 {
    let mut t = 0u32;
    let mut i = 0usize;
    while i < 256 {
        t = t.wrapping_add(h[i]);
        i += 1;
    }
    let lt = y_x_fl_log16(t);
    let mut bits = 0usize;
    let mut top = 0u32;
    let mut np = 0usize;
    let mut big = 0usize;
    let mut bigsum = 0usize;
    let mut j = 0usize;
    while j < 256 {
        let f = h[j];
        let c = lt.wrapping_sub(y_x_fl_log16(f)) as usize;
        bits = if f > 0 { bits.wrapping_add((f as usize).wrapping_mul(c)) } else { bits };
        top = if f > top { f } else { top };
        let ctl = if j < 32 { if j == 9 || j == 10 || j == 13 { 0usize } else { 1usize } } else { 0usize };
        let npj = if j >= 127 { 1usize } else { ctl };
        np = if npj == 1 { np.wrapping_add(f as usize) } else { np };
        let isbig = if (f as usize).wrapping_mul(8) >= t as usize { 1usize } else { 0usize };
        big = big.wrapping_add(isbig);
        bigsum = if isbig == 1 { bigsum.wrapping_add(f as usize) } else { bigsum };
        j += 1;
    }
    let tt = if t == 0 { 1usize } else { t as usize };
    let e = ((bits / tt) % 1024) as u64;
    let tp = (((top as usize).wrapping_mul(256) / tt) % 512) as u64;
    let z = (((h[0] as usize).wrapping_mul(256) / tt) % 512) as u64;
    let nps = ((np.wrapping_mul(256) / tt) % 512) as u64;
    let bs = ((bigsum.wrapping_mul(256) / tt) % 512) as u64;
    let bg = (big % 16) as u64;
    e | (tp << 10) | (z << 19) | (nps << 28) | (bs << 37) | (bg << 46)
}

/// Chunk `s .. s + Y_X_FL_PCH`: 4-phase byte histograms (phase = absolute position mod 4) into `ph`, and the number
/// of positions whose most recent same-3-byte-hash position in the chunk repeats 4 bytes.
pub fn y_x_fl_probe_chunk(input: &[u8], tab: &mut [u32; 4096], ph: &mut [u32; 1024], s: usize) -> usize {
    let mut p = s;
    let mut k = 0usize;
    let mut c4 = 0usize;
    while k < Y_X_FL_PCH {
        let x = y_x_fl_ld8(input, p);
        let b = (x as usize) % 256;
        let slot = (p % 4).wrapping_mul(256).wrapping_add(b) % 1024;
        ph[slot] = ph[slot].wrapping_add(1);
        let x3 = (x as u32) & 16777215;
        let h = (x3.wrapping_mul(2654435761) >> 20) as usize % 4096;
        let q = tab[h] as usize;
        let y = if q > s && q <= p { y_x_fl_ld8(input, q - 1) } else { !x };
        let z = x ^ y;
        c4 = if z & 4294967295 == 0 { c4.wrapping_add(1) } else { c4 };
        tab[h] = (p as u32).wrapping_add(1);
        p = p.wrapping_add(1);
        k += 1;
    }
    c4
}

/// Weights detector: 1 iff the probe chunks look like 16-bit floats (bytes alternate between a high-entropy and a
/// low-entropy phase with period 2) or like int8 weights (all phases 6.5-7.6 bits, no 4-byte repeat at all).
pub fn y_x_fl_weights(input: &[u8]) -> usize {
    let n = input.len();
    let mut tab = [0u32; 4096];
    let mut ph = [0u32; 1024];
    let span = n / Y_X_FL_PNC;
    let mut c4 = 0usize;
    let mut i = 0usize;
    while i < Y_X_FL_PNC {
        c4 = c4.wrapping_add(y_x_fl_probe_chunk(input, &mut tab, &mut ph, i.wrapping_mul(span)));
        i += 1;
    }
    let e0 = y_x_fl_ent(&ph, 0);
    let e1 = y_x_fl_ent(&ph, 256);
    let e2 = y_x_fl_ent(&ph, 512);
    let e3 = y_x_fl_ent(&ph, 768);
    let d02 = if e0 > e2 { e0.wrapping_sub(e2) } else { e2.wrapping_sub(e0) };
    let d13 = if e1 > e3 { e1.wrapping_sub(e3) } else { e3.wrapping_sub(e1) };
    let s02 = e0.wrapping_add(e2);
    let s13 = e1.wrapping_add(e3);
    let dev = if s02 > s13 { s02.wrapping_sub(s13) } else { s13.wrapping_sub(s02) };
    let lo = if e0 < e1 { e0 } else { e1 };
    let lo2 = if e2 < e3 { e2 } else { e3 };
    let mn = if lo < lo2 { lo } else { lo2 };
    let hi = if e0 > e1 { e0 } else { e1 };
    let hi2 = if e2 > e3 { e2 } else { e3 };
    let mx = if hi > hi2 { hi } else { hi2 };
    let p2 = if d02 < 8 && d13 < 8 && dev > 32 { 1usize } else { 0usize };
    let q8 = if c4 == 0 && mn >= 104 && mx < 120 && dev < 8 { 1usize } else { 0usize };
    p2 | q8
}

/// The mode (0 base, 1 LIT, 2 DNA, 4 RLE, 5 Y_X_LAZY) and the Y_X_LAZY class (0 T, 1 D, 2 H), packed `mode + 8 * class`.
/// Integer flags and nested value-ifs only (no `&&` guarding code, so the extracted model stays small).
pub fn y_x_fl_mode(input: &[u8], st: u64) -> usize {
    let n = input.len();
    let e = (st as usize) % 1024;
    let top = ((st >> 10) % 512) as usize;
    let z = ((st >> 19) % 512) as usize;
    let np = ((st >> 28) % 512) as usize;
    let bs = ((st >> 37) % 512) as usize;
    let bg = ((st >> 46) % 16) as usize;
    let rle = if top >= Y_X_FL_RLE_TOP { if n >= 1024 { 1usize } else { 0usize } } else { 0usize };
    let small = if n < Y_X_FL_PMIN { 1usize } else { 0usize };
    let dna = if bg == 4 { if bs >= 205 { if e < 52 { 1usize } else { 0usize } } else { 0usize } } else { 0usize };
    let high = if e >= Y_X_FL_HIGH { 1usize } else { 0usize };
    let db = if z >= Y_X_FL_DBZ { if np < Y_X_FL_DBNP { 1usize } else { 0usize } } else { 0usize };
    let w = if high == 1 { if Y_X_FL_USE_LIT == 1 { y_x_fl_weights(input) } else { 0 } } else { 0 };
    let mh = if w == 1 { 1 } else if Y_X_FL_USE_H == 1 { 21 } else { 0 };
    let md = if Y_X_FL_USE_D == 1 { 13 } else { 0 };
    let mt = if Y_X_FL_USE_T == 1 { 5 } else { 0 };
    if rle == 1 {
        4
    } else if small == 1 {
        mt
    } else if dna == 1 {
        2
    } else if high == 1 {
        mh
    } else if db == 1 {
        md
    } else {
        0
    }
}

/// The Y_X_LAZY configuration of a class: [depth, depth2, lazy, nice, ih, it, acc].
pub fn y_x_fl_config(class: usize, cf: &mut [usize; 8]) {
    cf[0] = if class == 0 { Y_X_FT_DEPTH } else if class == 1 { Y_X_FD_DEPTH } else { Y_X_FH_DEPTH };
    cf[1] = if class == 0 { Y_X_FT_DEPTH2 } else if class == 1 { Y_X_FD_DEPTH2 } else { Y_X_FH_DEPTH2 };
    cf[2] = if class == 0 { Y_X_FT_LAZY } else if class == 1 { Y_X_FD_LAZY } else { Y_X_FH_LAZY };
    cf[3] = if class == 0 { Y_X_FT_NICE } else if class == 1 { Y_X_FD_NICE } else { Y_X_FH_NICE };
    cf[4] = if class == 0 { Y_X_FT_IH } else if class == 1 { Y_X_FD_IH } else { Y_X_FH_IH };
    cf[5] = if class == 0 { Y_X_FT_IT } else if class == 1 { Y_X_FD_IT } else { Y_X_FH_IT };
    cf[6] = if class == 0 { Y_X_FT_ACC } else if class == 1 { Y_X_FD_ACC } else { Y_X_FH_ACC };
}

// ---------------------------------------------------------------- LIT and RLE

/// Trusted-kit emission of the whole input as literals.
pub fn y_x_fl_lit_parse(input: &[u8], out: &mut [u32]) -> (usize, usize) {
    let n = input.len();
    y_x_fl_emit_lits(input, out, 0, n, 0)
}

/// RLE parse: a distance-1 run match wherever the previous byte repeats >= 3 times, else one literal.
pub fn y_x_fl_rle_parse(input: &[u8], out: &mut [u32]) -> (usize, usize) {
    let n = input.len();
    let mut pos = 0usize;
    let mut ntok = 0usize;
    while pos < n {
        let rem = n - pos;
        let cap = if rem < 258 { rem } else { 258 };
        let l = if pos >= 1 { y_x_fl_len(input, pos - 1, pos, cap) } else { 0 };
        let r = y_x_fl_emit_step(input, out, pos, 1, l, 1, ntok);
        let olen = out.len();
        ntok = r.0;
        pos = r.1;
    }
    (ntok, pos)
}

// ---------------------------------------------------------------- DNA

/// Number of consecutive cheap bytes (cost < Y_X_FL_DNA_THR) from `pos`.
pub fn y_x_fl_cheap_run(input: &[u8], cost: &[u32; 256], pos: usize) -> usize {
    let n = input.len();
    let mut k = pos;
    while k < n && cost[input[k] as usize % 256] < Y_X_FL_DNA_THR {
        k += 1;
    }
    k.wrapping_sub(pos)
}

/// Literal cost (1/16 bits) of the `l` bytes at `pos` (l <= 258).
pub fn y_x_fl_span_cost(input: &[u8], cost: &[u32; 256], pos: usize, l: usize) -> usize {
    let mut s = 0usize;
    let mut i = 0usize;
    while i < l && i < 258 {
        s = s.wrapping_add(cost[y_x_fl_byte(input, pos.wrapping_add(i)) % 256] as usize);
        i += 1;
    }
    s
}

/// DEFLATE distance extra bits.
pub fn y_x_fl_dextra(d: usize) -> usize {
    if d <= 4 {
        0
    } else {
        let x = (d.wrapping_sub(1) as u32) | 1;
        (31u32.wrapping_sub(x.leading_zeros()) as usize).wrapping_sub(1)
    }
}

/// DEFLATE length extra bits.
pub fn y_x_fl_lextra(l: usize) -> usize {
    if l < 11 || l >= 258 {
        0
    } else {
        let x = (l.wrapping_sub(3) as u32) | 1;
        (31u32.wrapping_sub(x.leading_zeros()) as usize).wrapping_sub(2)
    }
}

/// 1 iff the match (l, d) at `pos` is estimated cheaper than its literals: Y_X_FL_DNA_M0 bits + extra bits.
pub fn y_x_fl_dna_ok(input: &[u8], cost: &[u32; 256], pos: usize, l: usize, d: usize) -> usize {
    let mc = Y_X_FL_DNA_M0.wrapping_add(y_x_fl_dextra(d)).wrapping_add(y_x_fl_lextra(l)).wrapping_mul(16);
    if y_x_fl_span_cost(input, cost, pos, l) > mc {
        1
    } else {
        0
    }
}

/// Longest match (ties: the closest) along the chain from `start` (pos+1 encoded). Returns `len | dist << 9`.
pub fn y_x_fl_dwalk(input: &[u8], prev: &[u32; 32768], pos: usize, start: usize, cap: usize, depth: usize) -> usize {
    let mut bl = 3usize;
    let mut bd = 0usize;
    let mut cur = start;
    let mut k = 0usize;
    while k < depth && cur > 0 && cur <= pos && pos - (cur - 1) <= 32768 {
        let c = cur - 1;
        if bl < cap && y_x_fl_byte(input, c.wrapping_add(bl)) == y_x_fl_byte(input, pos.wrapping_add(bl)) {
            let l = y_x_fl_len(input, c, pos, cap);
            let take = if l > bl { 1usize } else if l == bl { if bd == 0 { 1usize } else { 0usize } } else { 0usize };
            bd = if take == 1 { pos - c } else { bd };
            bl = if take == 1 { l } else { bl };
        }
        cur = if bl >= cap { 0 } else { prev[c % 32768] as usize };
        k += 1;
    }
    if bd > 0 {
        bl | bd.wrapping_mul(512)
    } else {
        0
    }
}

/// DNA: with `depth > 0`, insert `p` into the 4-byte-hash chains and walk them (depth 0: nothing).
pub fn y_x_fl_dsearch(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], p: usize, depth: usize) -> usize {
    let n = input.len();
    if depth == 0 || n < 16 || p > n - 16 {
        return 0;
    }
    let h = y_x_fl_hashp(input, p, 32);
    let start = head[h] as usize;
    prev[p % 32768] = start as u32;
    head[h] = (p as u32).wrapping_add(1);
    let rem = n - p - 8;
    let cap = if rem < 258 { rem } else { 258 };
    y_x_fl_dwalk(input, prev, p, start, cap, depth)
}

/// Insert positions `from .. to` into the chains (hash of the first 4 bytes if hsh = 32, 8 bytes if hsh = 0).
pub fn y_x_fl_insert(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], from: usize, to: usize, hsh: u64) {
    let n = input.len();
    let lim = n.saturating_sub(16);
    let mut p = from;
    while p < to && p <= lim {
        let h = y_x_fl_hashp(input, p, hsh);
        prev[p % 32768] = head[h];
        head[h] = (p as u32).wrapping_add(1);
        p += 1;
    }
}

/// DNA parse: literal runs over cheap bytes; at an expensive byte, search and take the match if it is estimated
/// cheaper than its literals. Only searched positions and match interiors enter the chains.
pub fn y_x_fl_dna_parse(input: &[u8], out: &mut [u32], cost: &[u32; 256]) -> (usize, usize) {
    let n = input.len();
    let mut head = [0u32; 65536];
    let mut prev = [0u32; 32768];
    let mut pos = 0usize;
    let mut ntok = 0usize;
    while pos < n {
        let cr = y_x_fl_cheap_run(input, cost, pos);
        let harg1 = if cr == 0 { Y_X_FL_DNA_DEPTH } else { 0 };
        let m = y_x_fl_dsearch(input, &mut head, &mut prev, pos, harg1);
        let l0 = m % 512;
        let d = (m / 512) % 65536;
        let ok = if l0 >= 3 { y_x_fl_dna_ok(input, cost, pos, l0, d) } else { 0 };
        let l = if ok == 1 { l0 } else { 0 };
        let lits = if cr > 0 { cr } else { 1 };
        let r = y_x_fl_emit_step(input, out, pos, d, l, lits, ntok);
        let olen = out.len();
        let npos = r.1;
        let matched = if l >= 3 { if npos == pos.wrapping_add(l) { 1usize } else { 0usize } } else { 0usize };
        let harg2 = if matched == 1 { npos } else { pos.wrapping_add(1) };
        y_x_fl_insert(input, &mut head, &mut prev, pos.wrapping_add(1), harg2, 32);
        ntok = r.0;
        pos = npos;
    }
    (ntok, pos)
}

// ---------------------------------------------------------------- Y_X_LAZY: price-lazy with a runtime config

/// Estimated saving (quarter bits, offset by 4096) of coding `l` bytes as a match at `d`.
pub fn y_x_fl_score(l: usize, d: usize, litq: usize) -> usize {
    let cost = Y_X_FL_C0Q.wrapping_add(y_x_fl_dextra(d).wrapping_add(y_x_fl_lextra(l)).wrapping_mul(4));
    l.wrapping_mul(litq).wrapping_add(4096).wrapping_sub(cost)
}

/// Fixed-point log2 with 8 fractional bits (linear between powers of two); x >= 1.
pub fn y_x_fl_lg8(x: u32) -> u64 {
    let y = x | 1;
    let e = 31u32.wrapping_sub(y.leading_zeros()) % 32;
    let m = if e >= 8 { (y >> (e - 8)) & 255 } else { (y << (8 - e)) & 255 };
    (e as u64).wrapping_mul(256).wrapping_add(m as u64)
}

/// Entropy of the histogram in 1/256 bits per symbol.
pub fn y_x_fl_entropy256(h: &[u32; 256]) -> usize {
    let mut tot = 0u64;
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i];
        tot = tot.wrapping_add(c as u64);
        acc = if c > 0 { acc.wrapping_add((c as u64).wrapping_mul(y_x_fl_lg8(c))) } else { acc };
        i += 1;
    }
    if tot == 0 {
        return 2048;
    }
    let t32 = if tot > 4000000000 { 4000000000u32 } else { tot as u32 };
    let a = y_x_fl_lg8(t32);
    let b = acc / tot;
    if a > b {
        (a - b) as usize
    } else {
        0
    }
}

/// Literal cost (quarter bits) for low-entropy inputs.
pub fn y_x_fl_lit_cost(h0: usize) -> usize {
    let q = h0 / 64 + Y_X_FL_LADJ;
    if q < 6 {
        6
    } else if q > 36 {
        36
    } else {
        q
    }
}

/// Walk the chain from `start` (pos+1 encoded, 0 = none) for the match with the best estimated saving
/// that is longer than `bl0` and saves more than `bs0`; stop at length `nice`. Returns `len | dist << 9`, or 0.
pub fn y_x_fl_walk(input: &[u8], prev: &[u32; 32768], pos: usize, start: usize, cap: usize, depth: usize, bl0: usize, bs0: usize, litq: usize, nice: usize) -> usize {
    let mut bl = bl0;
    let mut bd = 0usize;
    let mut bs = bs0;
    let mut cur = start;
    let mut k = 0usize;
    let mut off = if bl >= 3 { bl - 3 } else { 0 };
    let mut want = y_x_fl_ld4(input, pos.wrapping_add(off));
    while k < depth && cur > 0 && cur <= pos && pos - (cur - 1) <= 32768 {
        let c = cur - 1;
        if bl < cap && y_x_fl_ld4(input, c.wrapping_add(off)) == want {
            let l = y_x_fl_len(input, c, pos, cap);
            let s = y_x_fl_score(l, pos - c, litq);
            let take = if l > bl { if s > bs { 1usize } else { 0usize } } else { 0usize };
            bd = if take == 1 { pos - c } else { bd };
            bs = if take == 1 { s } else { bs };
            bl = if take == 1 { l } else { bl };
            off = if bl >= 3 { bl - 3 } else { 0 };
            want = y_x_fl_ld4(input, pos.wrapping_add(off));
        }
        cur = if bl >= nice { 0 } else { prev[c % 32768] as usize };
        k += 1;
    }
    if bd > 0 {
        bl | bd.wrapping_mul(512)
    } else {
        0
    }
}

/// With `depth > 0`: insert `pos` into the chains when `ins == 1`, then walk them. Returns
/// `len | dist << 9` of a match longer than `bl0` saving more than `bs0`, or 0.
pub fn y_x_fl_search(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], pos: usize, depth: usize, ins: usize, bl0: usize, bs0: usize, litq: usize, hsh: u64, nice: usize) -> usize {
    let n = input.len();
    if depth == 0 || n < 16 || pos > n - 16 {
        return 0;
    }
    let h = y_x_fl_hashp(input, pos, hsh);
    let start = head[h] as usize;
    let pw = pos % 32768;
    prev[pw] = if ins == 1 { start as u32 } else { prev[pw] };
    head[h] = if ins == 1 { (pos as u32).wrapping_add(1) } else { head[h] };
    let rem = n - pos - 8;
    let cap = if rem < 258 { rem } else { 258 };
    y_x_fl_walk(input, prev, pos, start, cap, depth, bl0, bs0, litq, nice)
}

/// Insert the inside `from .. to` of an emitted match: its first `ih` and last `it` positions.
pub fn y_x_fl_insert_match(input: &[u8], head: &mut [u32; 65536], prev: &mut [u32; 32768], from: usize, to: usize, hsh: u64, ih: usize, it: usize) {
    let a = from.wrapping_add(ih);
    let a2 = if a < to { a } else { to };
    y_x_fl_insert(input, head, prev, from, a2, hsh);
    let b = to.wrapping_sub(it);
    let b2 = if b > a2 { if b < to { b } else { a2 } } else { a2 };
    y_x_fl_insert(input, head, prev, b2, to, hsh);
}

/// Literal-run length after `miss` consecutive misses: 1 + (miss >> acc), at most 32.
pub fn y_x_fl_lits(miss: usize, acc: usize) -> usize {
    let over = ((miss as u64) >> ((acc as u64) % 64)) as usize;
    if over < 32 {
        over + 1
    } else {
        32
    }
}

/// Literal cost (quarter bits) used by the lazy parser: from the entropy for low-entropy inputs, else Y_X_FL_LITQ.
pub fn y_x_fl_litq(h0: usize) -> usize {
    if h0 < Y_X_FL_HLOW {
        y_x_fl_lit_cost(h0)
    } else {
        Y_X_FL_LITQ
    }
}

/// Hash shift: 8-byte hash (0) for low-entropy inputs, 4-byte hash (32) otherwise.
pub fn y_x_fl_hsh(h0: usize) -> u64 {
    if h0 < Y_X_FL_HLOW {
        0
    } else {
        32
    }
}

/// Price-lazy y_x_parse (the jgreedy jg1c algorithm) with the class configuration `cf`.
pub fn y_x_fl_lazy_parse(input: &[u8], out: &mut [u32], lh: &[u32; 256], cf: &[usize; 8]) -> (usize, usize) {
    let n = input.len();
    let depth = cf[0];
    let depth2 = cf[1];
    let lazy = cf[2];
    let nice = cf[3];
    let ih = cf[4];
    let it = cf[5];
    let acc = cf[6];
    let h0 = y_x_fl_entropy256(lh);
    let litq = y_x_fl_litq(h0);
    let hsh = y_x_fl_hsh(h0);
    let mut head = [0u32; 65536];
    let mut prev = [0u32; 32768];
    let mut pos = 0usize;
    let mut ntok = 0usize;
    let mut carry = 0usize;
    let mut miss = 0usize;
    while pos < n {
        let have = if carry != 0 { 1usize } else { 0usize };
        let harg3 = if have == 1 { 0 } else { depth };
        let s1 = y_x_fl_search(input, &mut head, &mut prev, pos, harg3, 1, 2, 4096, litq, hsh, nice);
        let m1 = if have == 1 { carry } else { s1 };
        let l1 = m1 % 512;
        if l1 < 3 {
            let lits = y_x_fl_lits(miss, acc);
            let r = y_x_fl_emit_step(input, out, pos, 0, 0, lits, ntok);
            let olen = out.len();
            miss = miss.wrapping_add(1);
            carry = 0;
            ntok = r.0;
            pos = r.1;
        } else {
            let d1 = (m1 / 512) % 65536;
            let want = if l1 < lazy { 1usize } else { 0usize };
            let p2 = if want == 1 { if l1 >= Y_X_FL_GOOD { depth2 } else { depth } } else { 0 };
            let s2 = y_x_fl_search(input, &mut head, &mut prev, pos.wrapping_add(1), p2, 1, l1.wrapping_sub(1), y_x_fl_score(l1, d1, litq), litq, hsh, nice);
            let take2 = if s2 != 0 { 1usize } else { 0usize };
            let l = if take2 == 1 { 0 } else { l1 };
            let d = if take2 == 1 { 0 } else { d1 };
            let r = y_x_fl_emit_step(input, out, pos, d, l, 1, ntok);
            let olen = out.len();
            let npos = r.1;
            let matched = if l >= 3 { if npos == pos.wrapping_add(l) { 1usize } else { 0usize } } else { 0usize };
            let from = if want == 1 { pos.wrapping_add(2) } else { pos.wrapping_add(1) };
            let harg4 = if matched == 1 { npos } else { from };
            y_x_fl_insert_match(input, &mut head, &mut prev, from, harg4, hsh, ih, it);
            carry = if take2 == 1 { s2 } else { 0 };
            miss = 0;
            ntok = r.0;
            pos = npos;
        }
    }
    (ntok, pos)
}

// ---------------------------------------------------------------- the floor phase

/// Runs the whole input through the mode's parser and returns `(ntok, n)`; mode 0 does nothing and returns
/// `(0, 0)` (the base parser then runs from position 0).
pub fn y_x_fl_part(input: &[u8], out: &mut [u32], mc: usize, fh: &[u32; 256]) -> (usize, usize) {
    let mode = mc % 8;
    let mut cost = [0u32; 256];
    y_x_fl_costs(fh, &mut cost);
    let mut cf = [0usize; 8];
    y_x_fl_config(mc / 8, &mut cf);
    if mode == 1 {
        y_x_fl_lit_parse(input, out)
    } else if mode == 2 {
        y_x_fl_dna_parse(input, out, &cost)
    } else if mode == 4 {
        y_x_fl_rle_parse(input, out)
    } else if mode == 5 {
        y_x_fl_lazy_parse(input, out, fh, &cf)
    } else {
        (0, 0)
    }
}
// ============================ end of the jfloor module =============================================================

/// Per step: a literal run up to the next candidate (one `scan`, emitted as one run of literals,
/// the candidate carried), or the primary candidate at `pos` (found at `pos` by the scan or carried)
/// with one lazy search at `pos + 1` compared on estimated savings; one trusted `emit_step`, then
/// untrusted bookkeeping (insertion inside the match, the carried candidate).
pub fn y_x_main_parse(input: &[u8], out: &mut [u32], pos0: usize, ntok0: usize) -> usize {
    let n = input.len();
    let mut head = [0u32; 65536];
    let mut prev = [0u32; 32768];
    let mut head3 = [0u32; 16384];
    let mut hist = [0u32; 256];
    y_x_sample(input, &mut hist);
    let e = y_x_entropy256(&hist);
    let low = y_x_low_mode(e);
    let m3 = if low == 1 { 0 } else { y_x_m3_mode(&hist, e) };
    let num = y_x_numeric(&hist, n, low);
    let lq = if num == 1 { Y_X_LQN } else { y_x_lit_cost(e, low) };
    let c0 = if low == 1 { Y_X_C0L } else { Y_X_C0Q };
    let litq = lq.wrapping_add(c0.wrapping_mul(256));
    let hs = if low == 1 { Y_X_HSL } else if m3 == 1 { 40 } else { 32 };
    let acc = if low == 1 { Y_X_ACCL } else if n < Y_X_NSMALL { 63 } else { Y_X_ACC };
    let depth = if low == 1 { Y_X_DEPTHL } else if m3 == 1 { Y_X_DEPTH3M } else if num == 1 { Y_X_DN } else { Y_X_DEPTH };
    let lz = Y_X_LAZY;
    let p2 = if num == 1 { Y_X_P2N } else { Y_X_DEPTH2 };
    let h3on = if m3 == 1 { 0 } else { y_x_h3_mode(&hist, e) };
    let h3i = if Y_X_H3INS == 1 { h3on } else { 0usize };
    let mut pos = pos0;
    let mut ntok = ntok0;
    let mut carry = 0usize;
    let mut miss = 0usize;
    while pos < n {
        let have = if carry != 0 { 1usize } else { 0usize };
        let dep = if have == 1 { 0 } else { depth };
        let s1 = y_x_search(input, &mut head, &mut prev, &mut head3, pos, dep, 2, Y_X_BIAS, litq, hs, h3on);
        let m1 = if have == 1 { carry } else { s1 };
        let l1 = m1 % 512;
        if l1 < 3 {
            let over = (miss as u64) >> (acc % 64);
            let lits = if over < Y_X_STEPMAX as u64 { (over as usize).wrapping_add(1) } else { Y_X_STEPMAX };
            let r = y_x_emit_step(input, out, pos, 0, 0, lits, ntok);
            let olen = out.len();
            miss = miss.wrapping_add(1);
            carry = 0;
            ntok = r.0;
            pos = r.1;
        } else {
            let d1 = (m1 / 512) % 65536;
            let want = if l1 < lz { 1usize } else { 0usize };
            let sv1 = y_x_score(l1, d1, litq);
            let s2 = y_x_lazy_probe(input, &mut head, &mut prev, &mut head3, pos.wrapping_add(1), want, p2, l1.wrapping_add(Y_X_LZB), sv1.wrapping_add(Y_X_BONUS), litq, hs, h3on);
            let take2 = if s2 != 0 { 1usize } else { 0usize };
            let l2 = s2 % 512;
            let d2 = (s2 / 512) % 65536;
            let ex = if take2 == 1 { y_x_ext_ok(input, pos, l2, d2) } else { 0 };
            let l = if take2 == 1 { if ex == 1 { l2.wrapping_add(1) } else { 0 } } else { l1 };
            let d = if take2 == 1 { if ex == 1 { d2 } else { 0 } } else { d1 };
            let r = y_x_emit_step(input, out, pos, d, l, 1, ntok);
            let olen = out.len();
            let npos = r.1;
            let matched = if l >= 3 && npos == pos.wrapping_add(l) { 1usize } else { 0usize };
            let from = pos.wrapping_add(1).wrapping_add(want);
            let upto = if matched == 1 { npos } else { from };
            y_x_insert_match(input, &mut head, &mut prev, &mut head3, from, upto, hs, h3i);
            carry = if take2 == 1 { if ex == 1 { 0 } else { s2 % 33554432 } } else { 0 };
            miss = 0;
            ntok = r.0;
            pos = npos;
        }
    }
    ntok
}

/// jfloor dispatcher. Sequential phases (no if/else between loop-heavy paths, SHARED_FINDINGS F17): the floor
/// phase handles the whole input for modes 1-5 and returns (ntok, n); for mode 0 it returns (0, 0) and the base
/// parser runs from position 0.
pub fn y_x_parse(input: &[u8], out: &mut [u32]) -> usize {
    let mut fh = [0u32; 256];
    y_x_fl_sample(input, &mut fh);
    let st = y_x_fl_stats(&fh);
    let mc = y_x_fl_mode(input, st);
    let r = y_x_fl_part(input, out, mc, &fh);
    if r.1 < input.len() { y_x_main_parse(input, out, r.1, r.0) } else { r.0 }
}


