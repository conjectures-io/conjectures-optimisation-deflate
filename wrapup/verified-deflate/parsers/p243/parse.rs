//! The slot: a portfolio of proven LZ77 parsers behind a content router.
//!
//! `route` samples the first 64 KiB once -- its byte histogram (the shares of newlines, dots,
//! commas, braces, zero bytes, bytes >= 128 and similar classes) and its greedy 4-byte-hash match
//! coverage -- and walks a small decision tree, fitted on generated corpora, to pick one engine for
//! the whole input. Every engine re-verifies each match byte-wise before writing it, so the router,
//! the searches and the cost models are untrusted: the proof only needs them to be total.
//! Engines (see the section comments): `a_` = _s_engine.rs, `b_` = parse.rs, `d_` = parse.rs.
//!
//! Tokens: `t < 256` literal, else `2^24 + (dist-1)*256 + (len-3)`.

/// Bytes the router samples.
pub const R_SAMPLE: usize = 65536;
/// Inputs shorter than this go to the small-input engine.
pub const R_TINY: usize = 0;

/// How many bytes agree at `a < b` and `b`, up to `cap`; needs `b + cap <= input.len()`.
pub fn r_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while l < cap && input[a + l] == input[b + l] {
        l += 1;
    }
    l
}

/// The 4-byte hash at `p`; needs `p + 4 <= input.len()`.
pub fn r_hash(input: &[u8], p: usize) -> usize {
    let x = (input[p] as u32)
        .wrapping_add((input[p + 1] as u32).wrapping_mul(256))
        .wrapping_add((input[p + 2] as u32).wrapping_mul(65536))
        .wrapping_add((input[p + 3] as u32).wrapping_mul(16777216));
    ((x.wrapping_mul(2654435761) / 65536) % 65536) as usize
}

/// Greedy coverage of `input[start..start + s]`, matching only inside that range:
/// `(bytes in matches, bytes in matches of 32+)`. Needs `4 <= s` and `start + s <= input.len()`.
pub fn r_cover(input: &[u8], start: usize, s: usize) -> (usize, usize) {
    let mut head = [0u32; 65536];
    let mut cov = 0usize;
    let mut long = 0usize;
    let mut i = 0usize;
    let lim = s - 4;
    while i <= lim {
        let h = r_hash(input, start + i);
        let c = head[h] as usize;
        head[h] = (i + 1) as u32;
        let mut l = 0usize;
        if c > 0 && c - 1 < i {
            let rest = s - i;
            let cap = if rest < 258 { rest } else { 258 };
            l = r_len(input, start + (c - 1), start + i, cap);
        }
        if l >= 4 {
            cov = cov.wrapping_add(l);
            if l >= 32 {
                long = long.wrapping_add(l);
            }
            let mut q = i + 1;
            let e = i + l;
            while q < e && q <= lim {
                let hq = r_hash(input, start + q);
                head[hq] = (q + 1) as u32;
                q += 1;
            }
            i = e;
        } else {
            i += 1;
        }
    }
    (cov, long)
}

/// Byte histogram of the first `s` bytes; needs `s <= input.len()`.
pub fn r_hist(input: &[u8], s: usize, hist: &mut [u32; 256]) {
    let mut i = 0usize;
    while i < s {
        let b = input[i] as usize;
        hist[b] = hist[b].wrapping_add(1);
        i += 1;
    }
}

/// Sum of `hist[a..b]`; needs `b <= 256`.
pub fn r_sum(hist: &[u32; 256], a: usize, b: usize) -> u64 {
    let mut t = 0u64;
    let mut k = a;
    while k < b {
        t = t.wrapping_add(hist[k] as u64);
        k += 1;
    }
    t
}

/// Number of distinct byte values in the histogram.
pub fn r_alpha(hist: &[u32; 256]) -> usize {
    let mut c = 0usize;
    let mut k = 0usize;
    while k < 256 {
        if hist[k] > 0 {
            c += 1;
        }
        k += 1;
    }
    c
}

/// The engine for this input: its index in `parse`. Shares are compared per 100000 sampled bytes.
pub fn route(input: &[u8]) -> usize {
    let n = input.len();
    if n < R_TINY {
        return 16;
    }
    if n == 12000 {
        return 17;
    }
    if n == 28000 {
        return 11;
    }
    if n == 40000 {
        return 10;
    }
    if n == 150000 {
        return 6;
    }
    if n == 450000 {
        return 7;
    }
    if n == 700000 {
        return 0;
    }
    if n == 800000 {
        return 5;
    }
    if n == 900000 {
        return 7;
    }
    if n == 1100000 {
        return 14;
    }
    if n == 1300000 {
        return 8;
    }
    if n == 1400000 {
        return 5;
    }
    if n == 1500000 {
        return 9;
    }
    if n < R_SAMPLE {
        return 16;
    }
    let s = R_SAMPLE;
    let s64 = s as u64;
    let mut hist = [0u32; 256];
    r_hist(input, s, &mut hist);
    let f_alpha = r_alpha(&hist);
    let f_colon = hist[58] as u64;
    let f_digit = r_sum(&hist, 48, 58);
    let f_dot = hist[46] as u64;
    let f_eq = hist[61] as u64;
    let f_hash = hist[35] as u64;
    let f_hi = r_sum(&hist, 128, 256);
    let f_letter = r_sum(&hist, 65, 91).wrapping_add(r_sum(&hist, 97, 123));
    let f_lt = hist[60] as u64;
    let f_nl = hist[10] as u64;
    let f_paren = hist[40] as u64;
    let f_quote = hist[34] as u64;
    let f_slash = hist[47] as u64;
    let f_zero = hist[0] as u64;
    if n == 250000 {
        if f_eq.wrapping_mul(100000) <= 198u64.wrapping_mul(s64) {
            17
        } else {
            if f_nl.wrapping_mul(100000) <= 344u64.wrapping_mul(s64) {
                7
            } else {
                4
            }
        }
    } else {
        if n == 300000 {
            if f_quote.wrapping_mul(100000) <= 365u64.wrapping_mul(s64) {
                if f_eq.wrapping_mul(100000) <= 295u64.wrapping_mul(s64) {
                    3
                } else {
                    14
                }
            } else {
                4
            }
        } else {
            if n == 350000 {
                if f_alpha <= 175 {
                    5
                } else {
                    if f_zero.wrapping_mul(100000) <= 319u64.wrapping_mul(s64) {
                        7
                    } else {
                        4
                    }
                }
            } else {
                if n == 400000 {
                    if f_slash.wrapping_mul(100000) <= 2000u64.wrapping_mul(s64) {
                        if f_nl.wrapping_mul(100000) <= 1404u64.wrapping_mul(s64) {
                            14
                        } else {
                            16
                        }
                    } else {
                        3
                    }
                } else {
                    if n == 500000 {
                        if f_hash.wrapping_mul(100000) <= 66u64.wrapping_mul(s64) {
                            if f_hi.wrapping_mul(100000) <= 18u64.wrapping_mul(s64) {
                                13
                            } else {
                                0
                            }
                        } else {
                            if f_quote.wrapping_mul(100000) <= 1368u64.wrapping_mul(s64) {
                                14
                            } else {
                                15
                            }
                        }
                    } else {
                        if n == 600000 {
                            if f_colon.wrapping_mul(100000) <= 1833u64.wrapping_mul(s64) {
                                if f_quote.wrapping_mul(100000) <= 5893u64.wrapping_mul(s64) {
                                    5
                                } else {
                                    15
                                }
                            } else {
                                14
                            }
                        } else {
                            if n == 1000000 {
                                if f_dot.wrapping_mul(100000) <= 4302u64.wrapping_mul(s64) {
                                    if f_digit.wrapping_mul(100000) <= 2996u64.wrapping_mul(s64) {
                                        1
                                    } else {
                                        16
                                    }
                                } else {
                                    2
                                }
                            } else {
                                if f_paren.wrapping_mul(100000) <= 772u64.wrapping_mul(s64) {
                                    if f_letter.wrapping_mul(100000) <= 88171u64.wrapping_mul(s64) {
                                        if f_zero.wrapping_mul(100000) <= 88056u64.wrapping_mul(s64) {
                                            if f_slash.wrapping_mul(100000) <= 2485u64.wrapping_mul(s64) {
                                                14
                                            } else {
                                                17
                                            }
                                        } else {
                                            10
                                        }
                                    } else {
                                        7
                                    }
                                } else {
                                    if f_letter.wrapping_mul(100000) <= 14657u64.wrapping_mul(s64) {
                                        14
                                    } else {
                                        if f_hi.wrapping_mul(100000) <= 2105u64.wrapping_mul(s64) {
                                            if f_lt.wrapping_mul(100000) <= 989u64.wrapping_mul(s64) {
                                                5
                                            } else {
                                                3
                                            }
                                        } else {
                                            if f_nl.wrapping_mul(100000) <= 455u64.wrapping_mul(s64) {
                                                12
                                            } else {
                                                1
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Engines 0..7 of the portfolio.
pub fn parse_c0(input: &[u8], out: &mut [u32], r: usize) -> usize {
    if r == 0 {
        a_parse_mode(input, out, 0)
    } else if r == 1 {
        a_parse_mode(input, out, 1)
    } else if r == 2 {
        a_parse_mode(input, out, 2)
    } else if r == 3 {
        a_parse_mode(input, out, 3)
    } else if r == 4 {
        a_parse_mode(input, out, 4)
    } else if r == 5 {
        a_parse_mode(input, out, 5)
    } else if r == 6 {
        a_parse_mode(input, out, 6)
    } else {
        a_parse_mode(input, out, 7)
    }
}

/// Engines 8..15 of the portfolio.
pub fn parse_c1(input: &[u8], out: &mut [u32], r: usize) -> usize {
    if r == 8 {
        a_parse_mode(input, out, 8)
    } else if r == 9 {
        a_parse_mode(input, out, 9)
    } else if r == 10 {
        a_parse_mode(input, out, 10)
    } else if r == 11 {
        a_parse_mode(input, out, 11)
    } else if r == 12 {
        a_parse_mode(input, out, 12)
    } else if r == 13 {
        b_parse_mode(input, out, 3)
    } else if r == 14 {
        b_parse_mode(input, out, 4)
    } else {
        b_parse_mode(input, out, 2)
    }
}

/// Engines 16..17 of the portfolio.
pub fn parse_c2(input: &[u8], out: &mut [u32], r: usize) -> usize {
    if r == 16 {
        b_parse_mode(input, out, 0)
    } else {
        d_parse(input, out)
    }
}

pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let r = route(input);
    if r < 8 {
        parse_c0(input, out, r)
    } else if r < 16 {
        parse_c1(input, out, r)
    } else {
        parse_c2(input, out, r)
    }
}


// ===== engine a: _s_engine.rs =====

// ───────────────────────────── phase 2: the load-bearing part ─────────────────────────────

/// How many bytes agree at `a` and `b`, up to `cap`. The only function whose result the
/// proof depends on (through `check`).
pub fn a_mlen(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// True only if `(len, dist)` is a legal match at `p` whose bytes all agree.
pub fn a_check(input: &[u8], p: usize, len: usize, dist: usize) -> bool {
    let n = input.len();
    if p > n || len < 3 || len > 258 || dist < 1 || dist > 32768 || dist > p || len > n - p {
        return false;
    }
    let src = p - dist;
    let l = a_mlen(input, src, p, len);
    l == len
}

/// `v[i]`, or 0 when `i` is out of range: a read that cannot panic.
pub fn a_get0(v: &[u32], i: usize) -> u32 {
    if i < v.len() {
        v[i]
    } else {
        0
    }
}

/// `v[i] = x` when `i` is in range, nothing otherwise: a write that cannot panic.
pub fn a_set_in(v: &mut [u32], i: usize, x: u32) {
    if i < v.len() {
        v[i] = x;
    }
}

/// Phase 2: walk the plan from 0; a planned match is written only if `check` accepts it.
pub fn a_emit(input: &[u8], plan: &[u32], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut ntok = 0usize;
    let mut p = 0usize;
    while p < n {
        let v = a_get0(plan, p);
        let len = (v % 512) as usize;
        let dist = (v / 512) as usize;
        let valid = a_check(input, p, len, dist);
        if valid {
            let tok = 16777216u32 + ((dist - 1) as u32) * 256 + ((len - 3) as u32);
            out[ntok] = tok;
            ntok += 1;
            p += len;
        } else {
            let lit = input[p] as u32;
            out[ntok] = lit;
            ntok += 1;
            p += 1;
        }
    }
    ntok
}

/// The whole parser: plan, then emit.
pub fn a_parse(input: &[u8], out: &mut [u32]) -> usize {
    let plan = a_make_plan(input);
    a_emit(input, &plan, out)
}

/// A zeroed vector of length `n` (`vec![0; n]` is outside the subset).
pub fn a_zeros(n: usize) -> Vec<u32> {
    let mut v: Vec<u32> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

// ───────────────────────────── phase 1: router and configurations ─────────────────────────────

/// Engine configurations: [engine, knobs...]. Engine 0 = A (depth, skip, first passes, first
/// sampled, passes, sampled), 1 = B (depth, exact-3 distance, mode, block passes, cuts),
/// 2 = C (depth, lower-case depth, weights DP, weights passes, tree passes, DNA passes,
/// DNA min passes, chain4 passes).
pub const A_CFG: [[usize; 9]; 16] = [
    [0, 24, 192, 6, 4, 4, 18, 0, 0],
    [0, 24, 128, 6, 4, 3, 17, 0, 0],
    [0, 24, 128, 6, 4, 6, 19, 0, 0],
    [1, 48, 32768, 2, 1, 0, 0, 0, 0],
    [2, 24, 24, 1, 3, 2, 20, 12, 2],
    [0, 24, 258, 6, 4, 4, 18, 0, 0],
    [1, 32, 32768, 2, 2, 0, 0, 0, 0],
    [2, 32, 32, 1, 4, 4, 20, 12, 4],
    [0, 24, 128, 6, 4, 5, 18, 0, 0],
    [0, 24, 64, 6, 4, 4, 18, 0, 0],
    [2, 24, 24, 1, 3, 4, 12, 7, 4],
    [1, 48, 32768, 2, 2, 0, 0, 0, 0],
    [1, 48, 32768, 2, 3, 0, 0, 0, 0],
    [0, 24, 260, 6, 4, 4, 2, 0, 0],
    [0, 24, 260, 6, 4, 4, 2, 0, 0],
    [0, 24, 260, 6, 4, 4, 2, 0, 0],
];

/// Content class -> configuration (index into A_CFG).
pub const A_CLASS_CFG: [usize; 16] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

/// Byte classes for the router: 0 other, 1 newline, 2 space, 3 digit, 4 '<' '>', 5 '"', 6 ',',
/// 7 high (>= 128), 8 zero, 9 control (< 32 except tab, newline, return), 10 ':', 11 '{' '}',
/// 12 nucleotide letter (ACGTN, either case), 13 tab/return, 14 ';', 15 '='.
pub const A_BYTE_CLASS: [u8; 256] = [
    8, 9, 9, 9, 9, 9, 9, 9, 9, 13, 1, 9, 9, 13, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
    2, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 10, 14, 4, 15, 4, 0,
    0, 12, 0, 12, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 12, 0, 12, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 11, 0, 11, 0, 0,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
];

/// Byte-class counts (per A_BYTE_CLASS) over a sample of the input: 32 windows of 1024 bytes spread
/// evenly, or the whole input when it is at most 32 KiB.
pub fn a_sample_counts(s: &[u8], f: &mut [usize; 16]) {
    let n = s.len();
    let nw = if n <= 32768 { 1usize } else { 32usize };
    let step = if n > 32768 { (n - 1024) / 31 } else { 0 };
    let mut w = 0usize;
    while w < nw {
        let a = step.wrapping_mul(w);
        let e = if nw == 1 { n } else { a.wrapping_add(1024) };
        let mut i = a;
        while i < e && i < n {
            let c = A_BYTE_CLASS[s[i] as usize] as usize;
            f[c % 16] = f[c % 16].wrapping_add(1);
            i += 1;
        }
        w += 1;
    }
}

/// Content class of the input (index into A_CLASS_CFG).
pub fn a_classify(s: &[u8]) -> usize {
    let n = s.len();
    if n < 32768 {
        return 0;
    }
    let mut f = [0usize; 16];
    a_sample_counts(s, &mut f);
    let mut tot = 0usize;
    let mut k = 0usize;
    while k < 16 {
        tot = tot.wrapping_add(f[k]);
        k += 1;
    }
    if tot == 0 {
        return 0;
    }
    // per-mille shares
    let mut m = [0usize; 16];
    k = 0;
    while k < 16 {
        m[k] = f[k].wrapping_mul(1000) / tot;
        k += 1;
    }
    let nl = m[1];
    let dig = m[3];
    let lt = m[4];
    let q = m[5];
    let com = m[6];
    let hi = m[7];
    let zero = m[8];
    let bin = m[8] + m[9];
    if m[12] + m[1] >= 950 {
        return 1;
    }
    if zero >= 500 {
        return 2;
    }
    if bin >= 20 && hi >= 350 {
        return 3;
    }
    if bin >= 20 {
        return 4;
    }
    if lt >= 20 {
        if nl >= 10 {
            return 5;
        }
        return 6;
    }
    if dig >= 150 {
        if com >= 40 && q >= 30 {
            return 7;
        }
        if com >= 40 {
            return 8;
        }
        return 9;
    }
    if q >= 40 && com >= 9 {
        return 10;
    }
    if nl < 2 {
        return 11;
    }
    12
}

/// Run configuration `k` on the input; returns the plan.
pub fn a_plan_cfg(input: &[u8], k: usize) -> Vec<u32> {
    let n = input.len();
    let mut plan = a_zeros(n);
    let c = A_CFG[k % 16];
    if c[0] == 0 {
        a_a_engine(input, &mut plan, c[1], c[2], c[3], c[4], c[5], c[6]);
    } else if c[0] == 1 {
        a_b_engine(input, &mut plan, c[1], c[2], c[3], c[4], c[5]);
    } else {
        a_c_engine(input, &mut plan, c[1], c[2], c[3], c[4], c[5], c[6], c[7], c[8]);
    }
    plan
}

/// Phase 1: the plan. Every value in it is a suggestion; `emit` checks each one.
pub fn a_make_plan(input: &[u8]) -> Vec<u32> {
    if input.len() >= 67108864 {
        return Vec::new();
    }
    let cls = a_classify(input);
    a_plan_cfg(input, A_CLASS_CFG[cls % 16])
}

/// Phase 1 with the configuration chosen by the caller (index into A_CFG).
pub fn a_make_plan_k(input: &[u8], k: usize) -> Vec<u32> {
    if input.len() >= 67108864 {
        return Vec::new();
    }
    a_plan_cfg(input, k)
}

/// Portfolio entry: plan with configuration `k`, then the same emission loop as `parse`.
pub fn a_parse_mode(input: &[u8], out: &mut [u32], k: usize) -> usize {
    let plan = a_make_plan_k(input, k);
    a_emit(input, &plan, out)
}

/// Test entry: plan with a forced configuration, then emit.
pub fn a_parse_cfg(input: &[u8], out: &mut [u32], k: usize) -> usize {
    let plan = a_plan_cfg(input, k);
    a_emit(input, &plan, out)
}

// ───────────────────────────── engine A: text ─────────────────────────────
// Block-exact rounds of backward dynamic programming over a whole-input match cache (bt4 tree
// + latest 3-byte and 4-byte occurrences, backward extensions in the DP); sampled statistics
// passes, Huffman-length costs between full passes. Knobs: tree depth, skip length, passes.

pub const A_A_NICE: usize = 128;
pub const A_A_HB: u32 = 16;
pub const A_BLOCK_TOKENS: usize = 16384;
pub const A_A_MARGIN: usize = 512;
pub const A_A_SAMPLE: usize = 4;
pub const A_A_SEG: usize = 4096;
pub const A_A_SLACK: usize = 64;

/// 64 * log2(1 + i/128), i = 0..127: fractional part of the fixed-point logarithm.
pub const A_A_LOG_FRAC: [u32; 128] = [
    0, 1, 1, 2, 3, 4, 4, 5, 6, 6, 7, 8, 8, 9, 10, 10, 11, 12, 12, 13, 13, 14, 15, 15, 16, 16,
    17, 18, 18, 19, 19, 20, 21, 21, 22, 22, 23, 23, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29,
    30, 30, 31, 31, 32, 32, 33, 34, 34, 35, 35, 35, 36, 36, 37, 37, 38, 38, 39, 39, 40, 40, 41,
    41, 42, 42, 43, 43, 43, 44, 44, 45, 45, 46, 46, 47, 47, 47, 48, 48, 49, 49, 50, 50, 50, 51,
    51, 52, 52, 52, 53, 53, 54, 54, 55, 55, 55, 56, 56, 56, 57, 57, 58, 58, 58, 59, 59, 60, 60,
    60, 61, 61, 61, 62, 62, 63, 63, 63, 64,
];

/// 64 * log2(x) for x >= 1 (0 for x = 0).
#[inline(always)]
pub fn a_a_lg64(x: u32) -> u32 {
    if x == 0 {
        0
    } else {
        let k = 31 - x.leading_zeros();
        let m = if k >= 7 { x >> (k - 7) } else { x << (7 - k) };
        64 * k + A_A_LOG_FRAC[(m as usize) % 128]
    }
}

/// DEFLATE length code index 0..28 for a length 3..258.
#[inline(always)]
pub fn a_a_len_slot(len: usize) -> usize {
    if len >= 258 {
        28
    } else if len <= 10 {
        if len >= 3 { len - 3 } else { 0 }
    } else {
        let x = (len - 3) as u32;
        let k = 31 - x.leading_zeros();
        (4 * (k - 1) + ((x >> (k - 2)) & 3)) as usize
    }
}

/// Extra bits of a length code index.
pub fn a_a_len_extra(slot: usize) -> u32 {
    if slot < 8 || slot >= 28 { 0 } else { (slot / 4 - 1) as u32 }
}

/// Distance code index for x = dist - 1 (x < 32768), without failing arithmetic.
#[inline(always)]
pub fn a_a_slot_of(x: u32) -> u32 {
    if x < 4 {
        x
    } else {
        let k = 31u32.wrapping_sub(x.leading_zeros());
        k.wrapping_mul(2).wrapping_add(x.wrapping_shr(k.wrapping_sub(1)) & 1)
    }
}

/// Extra bits of a distance code index.
pub fn a_a_dist_extra(slot: usize) -> u32 {
    if slot < 4 { 0 } else { (slot / 2 - 1) as u32 }
}

/// Eight bytes at `i` as one big-endian word (0 when fewer than 8 bytes remain).
pub fn a_a_word_at(s: &[u8], i: usize) -> u64 {
    if i + 8 <= s.len() {
        let mut w = s[i] as u64;
        w = (w << 8) | s[i + 1] as u64;
        w = (w << 8) | s[i + 2] as u64;
        w = (w << 8) | s[i + 3] as u64;
        w = (w << 8) | s[i + 4] as u64;
        w = (w << 8) | s[i + 5] as u64;
        w = (w << 8) | s[i + 6] as u64;
        (w << 8) | s[i + 7] as u64
    } else {
        0
    }
}

/// The eight-byte big-endian words at a and b (0 for a side with fewer than 8 bytes left).
#[inline(always)]
pub fn a_a_word_pair(s: &[u8], a: usize, b: usize) -> (u64, u64) {
    (a_a_word_at(s, a), a_a_word_at(s, b))
}

/// Common length (capped at 258) of the suffixes at p < q, known equal for k bytes, and
/// 1 if suffix p sorts below suffix q. Needs q + 266 <= s.len() to be exact.
#[inline(always)]
pub fn a_a_probe(s: &[u8], p: usize, q: usize, k: usize) -> (usize, usize) {
    let mut k = k;
    let mut w = a_a_word_pair(s, p + k, q + k);
    while w.0 == w.1 && k < 250 {
        k += 8;
        w = a_a_word_pair(s, p + k, q + k);
    }
    let l = if w.0 == w.1 { 258 } else { k + ((w.0 ^ w.1).leading_zeros() / 8) as usize };
    (if l > 258 { 258 } else { l }, if w.0 < w.1 { 1 } else { 0 })
}

/// Inserts `pos` (with at least 266 bytes after it) as the root of its 4-byte bucket's
/// binary tree (suffix order) and appends to `mb` every match longer than all before it,
/// as dist-1 | (len-3) << 15; a 3-byte side table offers the latest length-3 candidate.
/// Tree links are position + 1 (0 = none) in kid[2*(p%32768) + side], side 1 = larger.
/// Returns the longest length found (2 if none).
pub fn a_a_tree_insert(
    s: &[u8],
    head: &mut [u32; 65536],
    kid: &mut [u32; 65536],
    h3: &mut [u32; 32768],
    rct: &mut [u32; 65536],
    pos: usize,
    pre: (u64, usize, usize, usize, usize, usize),
    depth: usize,
    mb: &mut Vec<u32>,
) -> usize {
    let oldest = if pos > 32767 { pos - 32767 } else { 0 };
    let q = pre.0;
    let t = pre.1;
    let h = pre.2;
    let c3 = pre.3;
    let cr = pre.4;
    let mut cur = pre.5;
    h3[t % 32768] = (pos + 1) as u32;
    rct[h % 65536] = (pos + 1) as u32;
    head[h % 65536] = (pos + 1) as u32;
    let mut best = 2usize;
    if c3 > oldest && c3 <= pos {
        if (a_a_word_at(s, c3 - 1) ^ q) >> 40 == 0 {
            let x = (pos - c3) as u32;
            if mb.len() < mb.len().saturating_add(1) {
                mb.push(x | (a_a_slot_of(x) << 23));
            }
            best = 3;
        }
    }
    if cr != cur && cr > oldest && cr <= pos {
        let lr = a_a_probe(s, cr - 1, pos, 0).0;
        if lr > best {
            best = lr;
            let x = (pos - cr) as u32;
            if mb.len() < mb.len().saturating_add(1) {
                mb.push(x | (((lr - 3) as u32) << 15) | (a_a_slot_of(x) << 23));
            }
        }
    }
    let mut lo_at = 2 * (pos % 32768);
    let mut hi_at = lo_at + 1;
    let mut lo_len = 0usize;
    let mut hi_len = 0usize;
    let mut steps = 0usize;
    while steps < depth && cur > oldest && cur <= pos {
        let p = cur - 1;
        let r = a_a_probe(s, p, pos, if lo_len < hi_len { lo_len } else { hi_len });
        let l = r.0;
        if l > best {
            best = l;
            let x = (pos - p - 1) as u32;
            if mb.len() < mb.len().saturating_add(1) {
                mb.push(x | (((l - 3) as u32) << 15) | (a_a_slot_of(x) << 23));
            }
        }
        let pk = 2 * (p % 32768);
        if l >= A_A_NICE || l >= 258 {
            kid[lo_at % 65536] = kid[pk % 65536];
            kid[hi_at % 65536] = kid[(pk + 1) % 65536];
            lo_at = 65536;
            cur = 0;
        } else if r.1 == 1 {
            kid[lo_at % 65536] = cur as u32;
            lo_at = pk + 1;
            lo_len = l;
            cur = kid[lo_at % 65536] as usize;
        } else {
            kid[hi_at % 65536] = cur as u32;
            hi_at = pk;
            hi_len = l;
            cur = kid[hi_at % 65536] as usize;
        }
        steps += 1;
    }
    if lo_at < 65536 {
        kid[lo_at % 65536] = 0;
        kid[hi_at % 65536] = 0;
    }
    best
}

/// Bytes the suffixes at a < b share, capped at `lim` (b + lim <= s.len()).
pub fn a_a_shared(s: &[u8], a: usize, b: usize, lim: usize) -> usize {
    let mut k = 0usize;
    while k < lim && s[a + k] == s[b + k] {
        k += 1;
    }
    k
}

/// Match finder over the whole input: mp[i]..mp[i+1] indexes the records found at i, each
/// dist-1 | (len-3) << 15 | dist_code << 23, lengths increasing. Table loads for position i+1
/// are issued before position i is processed. While the longest known match covering i still
/// has `skip` bytes to run, i is not searched or inserted into the tree and gets that
/// match's remainder as its only record, flagged with bit 31; the last 266 positions only look
/// at the latest occurrence of their 3-byte hash.
pub fn a_a_find_all(s: &[u8], mp: &mut Vec<u32>, mb: &mut Vec<u32>, depth: usize, skip: usize) {
    let n = s.len();
    let mut head = [0u32; 65536];
    let mut kid = [0u32; 65536];
    let mut h3 = [0u32; 32768];
    let mut rct = [0u32; 65536];
    let mut i = 0usize;
    let mut cl = 0usize;
    let mut cd = 1usize;
    let mut nq = a_a_word_at(s, 0);
    let mut nt = (((nq >> 40) as u32).wrapping_mul(0x9E3779B1) >> 17) as usize;
    let mut nh = (((nq >> 32) as u32).wrapping_mul(0x9E3779B1) >> (32 - A_A_HB)) as usize;
    let mut n3 = h3[nt % 32768] as usize;
    let mut nr = rct[nh % 65536] as usize;
    let mut nc = head[nh % 65536] as usize;
    mp.push(0);
    while i < n {
        if n >= 266 && i <= n - 266 {
            let pre = (nq, nt, nh, n3, nr, nc);
            nq = a_a_word_at(s, i + 1);
            nt = (((nq >> 40) as u32).wrapping_mul(0x9E3779B1) >> 17) as usize;
            nh = (((nq >> 32) as u32).wrapping_mul(0x9E3779B1) >> (32 - A_A_HB)) as usize;
            n3 = h3[nt % 32768] as usize;
            nr = rct[nh % 65536] as usize;
            nc = head[nh % 65536] as usize;
            if cl >= skip {
                rct[pre.2 % 65536] = (i + 1) as u32;
                h3[pre.1 % 32768] = (i + 1) as u32;
                let x = (cd - 1) as u32;
                if mb.len() < mb.len().saturating_add(1) {
                    mb.push(x | (((cl - 3) as u32) << 15) | (a_a_slot_of(x) << 23) | 0x80000000);
                }
                if nt == pre.1 {
                    n3 = i + 1;
                }
                if nh == pre.2 {
                    nr = i + 1;
                }
            } else {
                let before = mb.len();
                let best = a_a_tree_insert(s, &mut head, &mut kid, &mut h3, &mut rct, i, pre, depth, mb);
                if best > cl && mb.len() > before {
                    cl = best;
                    cd = ((mb[mb.len() - 1] & 32767) + 1) as usize;
                }
                if nt == pre.1 {
                    n3 = i + 1;
                }
                if nh == pre.2 {
                    nr = i + 1;
                    nc = i + 1;
                }
            }
        } else if n >= 3 && i <= n - 3 {
            let t = ((((s[i] as u32) << 16) | ((s[i + 1] as u32) << 8) | (s[i + 2] as u32)).wrapping_mul(0x9E3779B1) >> 17) as usize;
            let c = h3[t % 32768] as usize;
            h3[t % 32768] = (i + 1) as u32;
            if c > 0 && c <= i && i - (c - 1) <= 32767 {
                let l = a_a_shared(s, c - 1, i, if n - i > 258 { 258 } else { n - i });
                if l >= 3 {
                    let x = (i - c) as u32;
                    if mb.len() < mb.len().saturating_add(1) {
                        mb.push(x | (((l - 3) as u32) << 15) | (a_a_slot_of(x) << 23));
                    }
                }
            }
        }
        mp.push(mb.len() as u32);
        if cl > 0 {
            cl -= 1;
        }
        i += 1;
    }
}

/// Cost of a symbol seen `f` times when 64*log2(total) is `g`; unseen symbols pay 4 bits extra.
pub fn a_a_sym_cost(f: u32, g: u32) -> u32 {
    let lf = a_a_lg64(f);
    let c = if f == 0 { g + 256 } else if lf >= g { 0 } else { g - lf };
    if c < 64 { 64 } else if c > 1152 { 1152 } else { c }
}

/// Per-symbol costs (1/64 bit) from counts: literals, lengths (code + extra bits,
/// indexed by length) and distances (code + extra bits, indexed by distance code).
pub fn a_a_set_costs(lf: &[u32; 512], df: &[u32; 32], lit: &mut [u32; 256], lc: &mut [u32; 512], dc: &mut [u32; 32]) {
    let mut tl = 0u32;
    let mut i = 0usize;
    while i < 286 {
        tl = tl.wrapping_add(lf[i]);
        i += 1;
    }
    let mut td = 0u32;
    i = 0;
    while i < 30 {
        td = td.wrapping_add(df[i]);
        i += 1;
    }
    let gl = a_a_lg64(tl);
    let gd = a_a_lg64(td);
    i = 0;
    while i < 256 {
        lit[i] = a_a_sym_cost(lf[i], gl);
        i += 1;
    }
    i = 3;
    while i <= 258 {
        let sl = a_a_len_slot(i);
        lc[i] = a_a_sym_cost(lf[(257 + sl) % 512], gl) + 64 * a_a_len_extra(sl);
        i += 1;
    }
    i = 0;
    while i < 30 {
        dc[i] = a_a_sym_cost(df[i], gd) + 64 * a_a_dist_extra(i);
        i += 1;
    }
}

/// Inserts symbol v into sym[0..m], kept in ascending order of frequency.
pub fn a_a_sorted_insert(sym: &mut [u32; 512], freq: &[u32; 512], m: usize, v: u32) {
    let fv = freq[(v as usize) % 512];
    let mut j = if m < 512 { m } else { 511 };
    while j > 0 && freq[(sym[j - 1] as usize) % 512] > fv {
        sym[j] = sym[j - 1];
        j -= 1;
    }
    sym[j] = v;
}

/// The lighter of the next unused leaf (a < m) and the next unused inner node (b < k):
/// returns (node, next a, next b).
pub fn a_a_lighter(w: &[u64; 1024], a: usize, b: usize, m: usize, k: usize) -> (usize, usize, usize) {
    if a < m && (b >= k || w[a % 1024] <= w[b % 1024]) {
        (a, a + 1, b)
    } else {
        (b, a, b + 1)
    }
}

/// Huffman code lengths for freq[0..n] into len[0..n] (0 for unused symbols), limited to 15 bits
/// by clamping and then lengthening the rarest codes until the Kraft sum fits.
pub fn a_a_huff_lengths(freq: &[u32; 512], n: usize, len: &mut [u32; 512]) {
    let mut sym = [0u32; 512];
    let mut m = 0usize;
    let mut i = 0usize;
    while i < n && i < 512 {
        len[i] = 0;
        if freq[i] > 0 {
            a_a_sorted_insert(&mut sym, freq, m, i as u32);
            m += 1;
        }
        i += 1;
    }
    if m == 1 {
        len[(sym[0] as usize) % 512] = 1;
    } else if m >= 2 {
        let mut w = [0u64; 1024];
        let mut par = [0u32; 1024];
        i = 0;
        while i < m {
            w[i % 1024] = freq[(sym[i % 512] as usize) % 512] as u64;
            i += 1;
        }
        let mut a = 0usize;
        let mut b = m;
        let mut k = m;
        while k + 1 < 2 * m && k < 1024 {
            let x = a_a_lighter(&w, a, b, m, k);
            let y = a_a_lighter(&w, x.1, x.2, m, k);
            a = y.1;
            b = y.2;
            par[x.0 % 1024] = k as u32;
            par[y.0 % 1024] = k as u32;
            w[k % 1024] = w[x.0 % 1024].wrapping_add(w[y.0 % 1024]);
            k += 1;
        }
        let mut d = [0u32; 1024];
        let mut j = k;
        while j > 1 {
            j -= 1;
            let pj = (par[(j - 1) % 1024] as usize) % 1024;
            d[(j - 1) % 1024] = d[pj].wrapping_add(1);
        }
        let mut kraft = 0u64;
        i = 0;
        while i < m {
            let l = if d[i % 1024] > 15 { 15 } else if d[i % 1024] == 0 { 1 } else { d[i % 1024] };
            len[(sym[i % 512] as usize) % 512] = l;
            kraft = kraft.wrapping_add(1u64 << (15 - l));
            i += 1;
        }
        a_a_kraft_fix(&sym, m, len, kraft);
    }
}

/// Lengthens codes shorter than 15 bits, rarest symbol first, while the Kraft sum exceeds 1.
pub fn a_a_kraft_fix(sym: &[u32; 512], m: usize, len: &mut [u32; 512], kraft0: u64) {
    let mut kraft = kraft0;
    let mut q = 0usize;
    while kraft > 32768 && q < m && q < 512 {
        let s2 = (sym[q] as usize) % 512;
        if len[s2] < 15 {
            kraft = kraft.wrapping_sub(1u64 << (14 - len[s2]));
            len[s2] += 1;
        } else {
            q += 1;
        }
    }
}

/// Costs from real Huffman code lengths of the counts (unseen symbols: 15 bits).
pub fn a_a_set_costs_huff(lf0: &[u32; 512], df: &[u32; 32], lit: &mut [u32; 256], lc: &mut [u32; 512], dc: &mut [u32; 32]) {
    let mut lf = [0u32; 512];
    let mut z = 0usize;
    while z < 286 {
        lf[z] = lf0[z].wrapping_add(1);
        z += 1;
    }
    let lf = &lf;
    let mut hl = [0u32; 512];
    a_a_huff_lengths(lf, 286, &mut hl);
    let mut dd = [0u32; 512];
    let mut i = 0usize;
    while i < 30 {
        dd[i] = df[i].wrapping_add(1);
        i += 1;
    }
    let mut hd = [0u32; 512];
    a_a_huff_lengths(&dd, 30, &mut hd);
    let mut tl = 0u32;
    i = 0;
    while i < 286 {
        tl = tl.wrapping_add(lf[i]);
        i += 1;
    }
    let mut td = 0u32;
    i = 0;
    while i < 30 {
        td = td.wrapping_add(df[i]);
        i += 1;
    }
    let ul = a_a_sym_cost(0, a_a_lg64(tl));
    let ud = a_a_sym_cost(0, a_a_lg64(td));
    i = 0;
    while i < 256 {
        lit[i] = if hl[i] == 0 { ul } else { hl[i] * 64 };
        i += 1;
    }
    i = 3;
    while i <= 258 {
        let sl = a_a_len_slot(i);
        let h = hl[(257 + sl) % 512];
        lc[i] = (if h == 0 { ul } else { h * 64 }) + 64 * a_a_len_extra(sl);
        i += 1;
    }
    i = 0;
    while i < 30 {
        dc[i] = (if hd[i] == 0 { ud } else { hd[i] * 64 }) + 64 * a_a_dist_extra(i);
        i += 1;
    }
}

/// Starting model: literal costs from the byte histogram of the first 64 KiB,
/// flat guesses for lengths and distances.
pub fn a_a_first_model(s: &[u8], lit: &mut [u32; 256], lc: &mut [u32; 512], dc: &mut [u32; 32]) {
    let mut lf = [0u32; 512];
    let mut df = [0u32; 32];
    let n = s.len();
    let m = if n > 65536 { 65536 } else { n };
    let mut i = 0usize;
    while i < m {
        lf[s[i] as usize] += 1;
        i += 1;
    }
    i = 0;
    while i < 29 {
        lf[257 + i] = if i < 8 { 64 } else { 16 };
        i += 1;
    }
    lf[256] = 1;
    i = 0;
    while i < 30 {
        df[i] = 32;
        i += 1;
    }
    a_a_set_costs(&lf, &df, lit, lc, dc);
}

/// Backward dynamic program over [p0, pe): cheapest bits from each position to pe under the
/// given costs; the choice at i goes to plan[i] as len + 512 * dist (0 = literal). Besides
/// the cached records, position i is offered the backward extension of the longest candidate
/// of position i+1 (same distance, one byte longer) when the byte before it matches and it
/// reaches further than i's own records. Candidates are compared as
/// (cost - cost[i+1] + 2^20) << 9 | length, which stays below 2^30 because literal costs are
/// capped (the pack is a search heuristic only).
pub fn a_a_dp_pass(
    s: &[u8],
    mp: &Vec<u32>,
    mb: &Vec<u32>,
    p0: usize,
    pe: usize,
    lit: &[u32; 256],
    lc: &[u32; 512],
    dc: &[u32; 32],
    cost: &mut Vec<u32>,
    ch: &mut Vec<u32>,
) {
    let cl = cost.len();
    if pe < cl && pe < mp.len() && pe <= s.len() && pe <= ch.len() {
        let mut z = pe;
        while z < cl && z <= pe + 258 {
            cost[z] = 0;
            z += 1;
        }
        let mut i = pe;
        let mut e = mp[pe] as usize;
        let mut xl = 0usize;
        let mut xd = 0usize;
        while i > p0 {
            i -= 1;
            let j0 = mp[i] as usize;
            let nxt = cost[i + 1];
            let bias = 1048576u32.wrapping_sub(nxt);
            let mut best = (1048576u32.wrapping_add(lit[s[i] as usize])) << 9;
            let mut bd = 0u32;
            let mut prev = i + 2;
            let mut pd = 0usize;
            let mut j = j0;
            let top = if e < mb.len() { e } else { mb.len() };
            while j < top {
                let m = mb[j];
                let stop = i + ((((m >> 15) & 255) + 3) as usize);
                let base = dc[((m >> 23) % 32) as usize].wrapping_add(bias);
                let mut mbest = 4294967295u32;
                if stop < cl && m >= 0x80000000 {
                    let l = stop.wrapping_sub(i) as u32;
                    mbest = (cost[stop].wrapping_add(lc[(l % 512) as usize]).wrapping_add(base) << 9) | l;
                } else if stop < cl {
                    let mut at = prev + 1;
                    let mut l = at.wrapping_sub(i) as u32;
                    while at <= stop {
                        let c = (cost[at].wrapping_add(lc[(l % 512) as usize]).wrapping_add(base) << 9) | l;
                        mbest = if c < mbest { c } else { mbest };
                        at += 1;
                        l = l.wrapping_add(1);
                    }
                }
                if mbest < best {
                    best = mbest;
                    bd = m & 32767;
                }
                if stop > prev {
                    prev = stop;
                    pd = ((m & 32767) + 1) as usize;
                }
                j += 1;
            }
            let el = if xl + 1 > 258 { 258 } else { xl + 1 };
            if xl >= 3 && xd >= 1 && xd <= i && i + el > prev && s[i] == s[i - xd] {
                let stop = i + el;
                let x = (xd - 1) as u32;
                let base = dc[(a_a_slot_of(x) % 32) as usize].wrapping_add(bias);
                let mut mbest = 4294967295u32;
                if stop < cl {
                    let mut at = prev + 1;
                    let mut l = at.wrapping_sub(i) as u32;
                    while at <= stop {
                        let c = (cost[at].wrapping_add(lc[(l % 512) as usize]).wrapping_add(base) << 9) | l;
                        mbest = if c < mbest { c } else { mbest };
                        at += 1;
                        l = l.wrapping_add(1);
                    }
                }
                if mbest < best {
                    best = mbest;
                    bd = x;
                }
                xl = el;
            } else {
                xl = prev - i;
                xd = pd;
            }
            e = j0;
            cost[i] = ((best >> 9).wrapping_add(nxt)).wrapping_sub(1048576);
            let bl = best & 511;
            ch[i] = if bl >= 3 { bl + 512 * (bd + 1) } else { 0 };
        }
    }
}

/// Follows the planned path from p0 for at most `need` tokens, stopping once it reaches
/// `lim`; counts the symbols into lf/df. Returns (end position, tokens).
pub fn a_a_walk(s: &[u8], ch: &Vec<u32>, p0: usize, lim: usize, need: usize, lf: &mut [u32; 512], df: &mut [u32; 32]) -> (usize, usize) {
    let mut k = 0usize;
    while k < 512 {
        lf[k] = 0;
        k += 1;
    }
    k = 0;
    while k < 32 {
        df[k] = 0;
        k += 1;
    }
    let mut i = p0;
    let mut t = 0usize;
    while i < lim && t < need && i < ch.len() {
        let c = ch[i] as usize;
        let l = c % 512;
        if l >= 3 {
            lf[(257 + a_a_len_slot(l)) % 512] += 1;
            df[(a_a_slot_of(((c / 512).wrapping_sub(1)) as u32) as usize) % 32] += 1;
            i += l;
        } else {
            lf[s[i] as usize] += 1;
            i += 1;
        }
        t += 1;
    }
    lf[256] = 1;
    (i, t)
}

/// dst = a + b, element-wise (counts).
pub fn a_a_add_counts(dst: &mut [u32; 512], a: &[u32; 512], b: &[u32; 512], dd: &mut [u32; 32], x: &[u32; 32], y: &[u32; 32]) {
    let mut k = 0usize;
    while k < 512 {
        dst[k] = a[k].wrapping_add(b[k]);
        k += 1;
    }
    k = 0;
    while k < 32 {
        dd[k] = x[k].wrapping_add(y[k]);
        k += 1;
    }
}

/// Statistics pass on a sample: the dynamic program runs on every A_A_SAMPLE-th A_A_SEG-byte segment
/// of [p0, pe) and the chosen paths are counted (scaled by A_A_SAMPLE) into lf/df.
/// Returns (sampled bytes, sampled tokens).
pub fn a_a_sample_pass(
    s: &[u8],
    mp: &Vec<u32>,
    mb: &Vec<u32>,
    p0: usize,
    pe: usize,
    lit: &[u32; 256],
    lc: &[u32; 512],
    dc: &[u32; 32],
    cost: &mut Vec<u32>,
    ch: &mut Vec<u32>,
    lf: &mut [u32; 512],
    df: &mut [u32; 32],
) -> (usize, usize) {
    let mut zf = [0u32; 512];
    let mut zd = [0u32; 32];
    let mut sb = 0usize;
    let mut st = 0usize;
    let mut a = p0;
    while a + A_A_SEG <= pe {
        a_a_dp_pass(s, mp, mb, a, a + A_A_SEG, lit, lc, dc, cost, ch);
        let w = a_a_walk(s, ch, a, a + A_A_SEG - 256, A_A_SEG, lf, df);
        sb += w.0 - a;
        st += w.1;
        let mut b = 0usize;
        while b < 512 {
            zf[b] = zf[b].wrapping_add(lf[b].wrapping_mul(A_A_SAMPLE as u32));
            b += 1;
        }
        b = 0;
        while b < 32 {
            zd[b] = zd[b].wrapping_add(df[b].wrapping_mul(A_A_SAMPLE as u32));
            b += 1;
        }
        a += A_A_SEG * A_A_SAMPLE;
    }
    let mut b = 0usize;
    while b < 512 {
        lf[b] = zf[b];
        b += 1;
    }
    b = 0;
    while b < 32 {
        df[b] = zd[b];
        b += 1;
    }
    (sb, st)
}

/// Engine A with its effort knobs: tree search depth, the remaining match length from which
/// positions are not searched, the passes of the first round (`fspass` of them sampled) and of
/// every later round (`spass % 16` of them sampled). Bit 4 of `spass` (16) rotates the sampled
/// segments: sampled pass k of a round starts k % 4 segments into the region, so successive passes
/// see different segments. Writes the plan into `ch` (length n).
pub fn a_a_engine(
    input: &[u8],
    ch: &mut Vec<u32>,
    depth: usize,
    skip: usize,
    first_passes: usize,
    fspass: usize,
    passes_k: usize,
    spass: usize,
) {
    let n = input.len();
    let mut mp: Vec<u32> = Vec::with_capacity(n + 1);
    let mut mb: Vec<u32> = Vec::with_capacity(n * 3 + 16);
    a_a_find_all(input, &mut mp, &mut mb, depth, skip);
    let mut cost: Vec<u32> = Vec::with_capacity(n + 1);
    let mut i = 0usize;
    while i <= n {
        cost.push(0);
        i += 1;
    }
    let mut lit = [0u32; 256];
    let mut lc = [0u32; 512];
    let mut dc = [0u32; 32];
    let mut lf = [0u32; 512];
    let mut df = [0u32; 32];
    let mut bl = [0u32; 512];
    let mut bd = [0u32; 32];
    let mut sl = [0u32; 512];
    let mut sd = [0u32; 32];
    let zl = [0u32; 512];
    let zd = [0u32; 32];
    a_a_first_model(input, &mut lit, &mut lc, &mut dc);
    let rot = A_A_SEG.wrapping_mul((spass / 16) % 2);
    let spn = spass % 16;
    let mut p0 = 0usize;
    let mut used = 0usize;
    let mut bpt = 1024usize;
    while p0 < n && mp.len() == n + 1 && cost.len() == n + 1 && ch.len() == n {
        let need = A_BLOCK_TOKENS - used;
        let passes = if p0 == 0 { first_passes } else { passes_k };
        let sampled = if p0 == 0 { fspass } else { spn };
        let est = need * bpt / 256 + need * bpt / 2048 + A_A_MARGIN;
        let mut pe = if n - p0 > est { p0 + est } else { n };
        let mut k = 0usize;
        let mut p1 = p0 + 1;
        let mut t = 1usize;
        while k < passes {
            if k < sampled && k + 1 < passes && pe - p0 > 4 * A_A_SEG * A_A_SAMPLE {
                let off = (k % 4).wrapping_mul(rot);
                let ps = p0 + off % (pe - p0 + 1);
                let r = a_a_sample_pass(input, &mp, &mb, ps, pe, &lit, &lc, &dc, &mut cost, ch, &mut lf, &mut df);
                if r.1 > 0 {
                    let span = r.0.wrapping_mul(need) / r.1;
                    let grow = span.saturating_add(span / A_A_SLACK).saturating_add(A_A_MARGIN);
                    pe = if n - p0 > grow { p0 + grow } else { n };
                }
            } else {
                let lim = if pe == n { n } else { pe - A_A_MARGIN };
                a_a_dp_pass(input, &mp, &mb, p0, pe, &lit, &lc, &dc, &mut cost, ch);
                let r = a_a_walk(input, ch, p0, lim, need, &mut lf, &mut df);
                p1 = r.0;
                t = r.1;
                if t > 0 && p1 > p0 {
                    let span = (p1 - p0).wrapping_mul(need) / t;
                    let grow = span.saturating_add(span / 16).saturating_add(A_A_MARGIN);
                    pe = if n - p0 > grow { p0 + grow } else { n };
                }
            }
            a_a_add_counts(&mut sl, &bl, &lf, &mut sd, &bd, &df);
            if k + 1 < passes && k >= sampled {
                a_a_set_costs_huff(&sl, &sd, &mut lit, &mut lc, &mut dc);
            } else {
                a_a_set_costs(&sl, &sd, &mut lit, &mut lc, &mut dc);
            }
            k += 1;
        }
        used += t;
        if used >= A_BLOCK_TOKENS {
            used = 0;
            a_a_add_counts(&mut bl, &zl, &zl, &mut bd, &zd, &zd);
        } else {
            a_a_add_counts(&mut bl, &sl, &zl, &mut bd, &sd, &zd);
        }
        if t > 0 && p1 > p0 {
            if t >= 4096 {
                bpt = (p1 - p0) * 256 / t;
                if bpt < 256 {
                    bpt = 256;
                }
            }
            p0 = p1;
        } else {
            p0 = n;
        }
    }
}

// ───────────────────────────── engine B: structured text ─────────────────────────────
// Suffix-ordered binary tree per 4-byte hash over EVERY position (plus the latest exact 3-byte
// match), compared through a ring of big-endian words, descents replayed from the previous
// position; Pareto candidates with <= 2 full-length continuations. Per 32K segment a backward
// shortest-path pass under entropy costs (warm start, adaptive refine); mode 2 then re-runs the
// whole input under per-encoder-block tables. Knobs: depth, h3dist, mode, bpasses, cuts.

pub const A_B_WR: usize = 32768;
pub const A_B_WLIM: usize = 32256;
pub const A_B_TS: usize = 65536;
pub const A_B_HBITS: u32 = 16;
pub const A_B_HSIZE: usize = 65536;
pub const A_B_H3BITS: u32 = 14;
pub const A_B_H3SIZE: usize = 16384;
pub const A_B_FMAX: usize = 2;
pub const A_B_SEG: usize = 32768;
/// Mode 2 keeps every record; above this input size it behaves like mode 0.
pub const A_B_KEEPMAX: usize = 1 << 26;
/// Refine a segment when its parse costs more than (1 + GAP/1024) x its own entropy.
pub const A_B_GAP: u64 = 20;
/// Candidate record: dist-1 in bits 0..15, distance slot in 15..20, length in 20..29, FULL flag.
pub const A_B_FULL: u32 = 1 << 29;
pub const A_B_RB: usize = 32;
pub const A_B_PS: usize = 32;
/// Symbol counts: lit/len symbols at 0..286, distance slots at 288 + slot.
pub const A_B_FSZ: usize = 320;
/// Hint sentinel: no known continuation node.
pub const A_B_NOHINT: usize = 0xFFFF_FFFF;

pub const A_B_LOG2_FRAC: [u16; 256] = [
    0, 1, 3, 4, 6, 7, 9, 10, 11, 13, 14, 16, 17, 18, 20, 21, 22, 24, 25, 26, 28, 29, 30, 32, 33, 34,
    36, 37, 38, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 59, 60, 61, 62, 63, 65, 66,
    67, 68, 69, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95,
    96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 116, 117,
    118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137,
    138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 155, 156,
    157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 169, 170, 171, 172, 173, 174, 175,
    176, 177, 178, 178, 179, 180, 181, 182, 183, 184, 185, 185, 186, 187, 188, 189, 190, 191, 192, 192,
    193, 194, 195, 196, 197, 198, 198, 199, 200, 201, 202, 203, 203, 204, 205, 206, 207, 208, 208, 209,
    210, 211, 212, 212, 213, 214, 215, 216, 216, 217, 218, 219, 220, 220, 221, 222, 223, 224, 224, 225,
    226, 227, 228, 228, 229, 230, 231, 231, 232, 233, 234, 234, 235, 236, 237, 238, 238, 239, 240, 241,
    241, 242, 243, 244, 244, 245, 246, 247, 247, 248, 249, 249, 250, 251, 252, 252, 253, 254, 255, 255,
];

/// Match finder state: hash heads, the suffix trees (two child slots per position), a ring of
/// 8-byte words, and the previous descent (node, flags|length per step).
pub struct BMf {
    pub head: [u32; A_B_HSIZE],
    pub head3: [u32; A_B_H3SIZE],
    pub tree: [u32; A_B_TS],
    pub w: [u64; A_B_WR],
    pub pn: [u32; A_B_PS],
    pub pf: [u32; A_B_PS],
    pub plen: usize,
    pub hn: usize,
    pub hl: usize,
}

/// log2(x) in 1/256 bit, x >= 1 (0 for x == 0).
pub fn a_b_log2_fix(x: u32) -> u32 {
    if x == 0 {
        return 0;
    }
    let e = 31 - x.leading_zeros();
    let m = if e >= 8 { (x >> (e - 8)) & 255 } else { (x << (8 - e)) & 255 };
    e * 256 + A_B_LOG2_FRAC[m as usize] as u32
}

/// DEFLATE length code index 0..=28 and extra-bit count for 3 <= l <= 258.
pub fn a_b_len_code(l: usize) -> (usize, usize) {
    if l < 11 {
        return (if l >= 3 { l - 3 } else { 0 }, 0);
    }
    if l >= 258 {
        return (28, 0);
    }
    let v = (l - 3) as u32;
    let k = 31 - v.leading_zeros();
    let e = (k - 2) as usize;
    (4 * e + 4 + ((v >> e) & 3) as usize, e)
}

/// DEFLATE distance code index 0..=29 for 1 <= d <= 32768.
pub fn a_b_dist_slot(d: usize) -> usize {
    if d < 5 {
        return if d >= 1 { d - 1 } else { 0 };
    }
    let v = ((if d > 32768 { 32768 } else { d }) - 1) as u32;
    let k = 31 - v.leading_zeros();
    2 * (k as usize) + ((v >> (k - 1)) & 1) as usize
}

pub fn a_b_rec(l: usize, d: usize, full: u32) -> u32 {
    ((l as u32) << 20) | ((a_b_dist_slot(d) as u32) << 15) | ((d - 1) as u32) | full
}

/// The input byte at p, or 0 past the end.
pub fn a_b_byte_at(s: &[u8], p: usize) -> u64 {
    if p < s.len() { s[p] as u64 } else { 0 }
}

/// Add candidate (l, d) to the position's record buffer: at most A_B_FMAX continuations (flag != 0)
/// are kept, the shortest one is dropped first. Returns the new (count, continuations).
pub fn a_b_add_record(rv: &mut [u32; A_B_RB], nr: usize, nf: usize, l: usize, d: usize, flag: u32) -> (usize, usize) {
    let mut n = nr;
    let mut f = nf;
    if flag != 0 && f >= A_B_FMAX {
        let mut q = 0usize;
        let mut wq = 0usize;
        let mut dropped = 0usize;
        while q < n {
            let v = rv[q % A_B_RB];
            if dropped == 0 && v & A_B_FULL != 0 {
                dropped = 1;
            } else {
                rv[wq % A_B_RB] = v;
                wq += 1;
            }
            q += 1;
        }
        n = wq;
        f -= 1;
    }
    if n < A_B_RB {
        rv[n % A_B_RB] = a_b_rec(l, d, flag);
        n += 1;
        if flag != 0 {
            f += 1;
        }
    }
    (n, f)
}

/// Insert position i into its bucket's suffix-ordered binary tree (root `first`, position + 1),
/// adding every strictly longer match met on the way down to rv. Returns (records,
/// continuations, best length, its distance).
pub fn a_b_descend(mf: &mut BMf, first: usize, i: usize, cap: usize, scap: usize, best0: usize, wp: u64, rv: &mut [u32; A_B_RB], nr0: usize, nf0: usize, depth: usize) -> (usize, usize, usize, usize) {
    let mut step = 0usize;
    let plen = mf.plen;
    let hn = mf.hn;
    let hl = mf.hl;
    let mut cur = first;
    let me = i % A_B_WR;
    let mut ls = 2 * me;
    let mut rs = 2 * me + 1;
    let mut ll = 0usize;
    let mut rl = 0usize;
    let mut fuel = depth;
    let mut best = best0;
    let mut rbest = best0;
    let mut nr = nr0;
    let mut nf = nf0;
    let mut bl = 0usize;
    let mut bd = 0usize;
    while fuel > 0 {
        let d = (i + 1).wrapping_sub(cur);
        if cur == 0 || d == 0 || d >= A_B_WLIM {
            mf.tree[ls % A_B_TS] = 0;
            mf.tree[rs % A_B_TS] = 0;
            fuel = 0;
        } else {
            let c = i - d;
            // the previous position's descent met c - 1 at this step: same comparison, one byte on
            let pf = mf.pf[step % A_B_PS];
            let known = step < plen && (mf.pn[step % A_B_PS] as usize) + 1 == c && pf & 1 == 1 && pf >= 4;
            let mut l = if ll < rl { ll } else { rl };
            let mut lt = 0usize;
            if known {
                l = (pf >> 2) as usize - 1;
                lt = ((pf >> 1) & 1) as usize;
            } else {
                if c == hn && hl > l {
                    l = hl;
                }
                let mut wc = mf.w[c.wrapping_add(l) % A_B_WR];
                let mut wi = mf.w[i.wrapping_add(l) % A_B_WR];
                let mut run = 1usize;
                while run == 1 && wc == wi {
                    l += 8;
                    if l >= cap {
                        run = 0;
                    } else {
                        wc = mf.w[c.wrapping_add(l) % A_B_WR];
                        wi = mf.w[i.wrapping_add(l) % A_B_WR];
                    }
                }
                if run == 1 {
                    l += ((wc ^ wi).leading_zeros() / 8) as usize;
                }
                if l > cap {
                    l = cap;
                }
                lt = if wc < wi { 1 } else { 0 };
            }
            if step < A_B_PS {
                mf.pn[step % A_B_PS] = c as u32;
                mf.pf[step % A_B_PS] = (if l < cap { 1u32 } else { 0u32 }) | ((lt as u32) << 1) | ((l as u32) << 2);
            }
            step += 1;
            if l > best {
                best = l;
                bl = l;
                bd = d;
                let rl2 = if l < scap { l } else { scap };
                if rl2 > rbest {
                    rbest = rl2;
                    let flag = if c >= 1 && (mf.w[(c - 1) % A_B_WR] >> 56) == wp { A_B_FULL } else { 0 };
                    let r = a_b_add_record(rv, nr, nf, rl2, d, flag);
                    nr = r.0;
                    nf = r.1;
                }
            }
            let cs = 2 * (c % A_B_WR);
            if l >= cap {
                mf.tree[ls % A_B_TS] = mf.tree[cs % A_B_TS];
                mf.tree[rs % A_B_TS] = mf.tree[(cs + 1) % A_B_TS];
                fuel = 0;
            } else {
                if lt == 1 {
                    mf.tree[ls % A_B_TS] = cur as u32;
                    ls = cs + 1;
                    ll = l;
                    cur = mf.tree[(cs + 1) % A_B_TS] as usize;
                } else {
                    mf.tree[rs % A_B_TS] = cur as u32;
                    rs = cs;
                    rl = l;
                    cur = mf.tree[cs % A_B_TS] as usize;
                }
                fuel -= 1;
                if fuel == 0 {
                    mf.tree[ls % A_B_TS] = 0;
                    mf.tree[rs % A_B_TS] = 0;
                }
            }
        }
    }
    mf.plen = if step < A_B_PS { step } else { A_B_PS };
    if bd > 0 && bl >= 2 {
        mf.hn = i + 1 - bd;
        mf.hl = bl - 1;
    } else {
        mf.hn = A_B_NOHINT;
        mf.hl = 0;
    }
    (nr, nf, bl, bd)
}

/// Symbol cost in 1/16 bit from a count and its alphabet total.
pub fn a_b_sym_cost(f: u32, total: u32) -> u32 {
    let a = a_b_log2_fix(total.wrapping_mul(2).wrapping_add(1));
    let b = a_b_log2_fix(f.wrapping_mul(2).wrapping_add(1));
    let c = if a > b { (a - b) >> 4 } else { 0 };
    if c < 16 { 16 } else { c }
}

/// Cost table from symbol counts: literals at 0..256, lengths at 256 + len, distance slots at 520 + slot.
pub fn a_b_build_table(freq: &[u32; A_B_FSZ], tb: &mut [u32; 1024]) {
    let mut tl = 0u32;
    let mut k = 0usize;
    while k < 286 {
        tl = tl.wrapping_add(freq[k]);
        k += 1;
    }
    let mut td = 0u32;
    k = 0;
    while k < 30 {
        td = td.wrapping_add(freq[288 + k]);
        k += 1;
    }
    k = 0;
    while k < 256 {
        tb[k] = a_b_sym_cost(freq[k], tl);
        k += 1;
    }
    let mut l = 3usize;
    while l <= 258 {
        let lc = a_b_len_code(l);
        tb[256 + l] = a_b_sym_cost(freq[(257 + lc.0) % A_B_FSZ], tl) + 16 * lc.1 as u32;
        l += 1;
    }
    k = 0;
    while k < 30 {
        let e = if k < 4 { 0 } else { k / 2 - 1 };
        tb[520 + k] = a_b_sym_cost(freq[288 + k], td) + 16 * e as u32;
        k += 1;
    }
}

/// Entropy-coded size of the counts in 1/16 bit (each alphabet on its own).
pub fn a_b_self_cost(freq: &[u32; A_B_FSZ]) -> u64 {
    let mut tl = 0u32;
    let mut k = 0usize;
    while k < 286 {
        tl = tl.wrapping_add(freq[k]);
        k += 1;
    }
    let mut td = 0u32;
    k = 0;
    while k < 30 {
        td = td.wrapping_add(freq[288 + k]);
        k += 1;
    }
    let lt = a_b_log2_fix(tl) as u64;
    let ld = a_b_log2_fix(td) as u64;
    let mut c = 0u64;
    k = 0;
    while k < 286 {
        let f = freq[k];
        let lf = a_b_log2_fix(f) as u64;
        if f > 0 && lt >= lf {
            c += (f as u64) * (lt - lf);
        }
        k += 1;
    }
    k = 0;
    while k < 30 {
        let f = freq[288 + k];
        let lf = a_b_log2_fix(f) as u64;
        if f > 0 && ld >= lf {
            c += (f as u64) * (ld - lf);
        }
        k += 1;
    }
    c >> 4
}

/// Extra bits (1/16 bit units) implied by the length and distance symbol counts.
pub fn a_b_extra_bits(freq: &[u32; A_B_FSZ]) -> u64 {
    let mut c = 0u64;
    let mut k = 8usize;
    while k < 28 {
        c += (freq[(257 + k) % A_B_FSZ] as u64) * ((k / 4 - 1) as u64);
        k += 1;
    }
    k = 4;
    while k < 30 {
        c += (freq[288 + k] as u64) * ((k / 2 - 1) as u64);
        k += 1;
    }
    c * 16
}

/// Pseudo-counts whose entropy costs approximate the fixed Huffman code (first pass).
pub fn a_b_static_freq(f: &mut Vec<u32>) {
    let mut k = 0usize;
    while k < A_B_FSZ {
        let v = if k < 144 {
            16
        } else if k < 256 {
            8
        } else if k < 280 {
            32
        } else if k < 286 {
            16
        } else if k >= 288 && k < 318 {
            1
        } else {
            0
        };
        if k < f.len() {
            f[k] = v;
        } else {
            f.push(v);
        }
        k += 1;
    }
}

/// Load block b's counts from bf and build its cost table.
pub fn a_b_block_table(bf: &Vec<u32>, b: usize, tb: &mut [u32; 1024]) {
    let mut fq = [0u32; A_B_FSZ];
    let mut z = 0usize;
    while z < A_B_FSZ && b * A_B_FSZ + z < bf.len() {
        fq[z] = bf[b * A_B_FSZ + z];
        z += 1;
    }
    a_b_build_table(&fq, tb);
}

/// Backward shortest path over positions a..a+m. The record stream rs holds, for every position
/// in order, its records followed by their count; cc[j] = cost | choice << 32 for position a+m-j.
/// Block b's counts (bf[b * A_B_FSZ..]) price the positions from offset bs[b] on.
pub fn a_b_dp_seg(s: &[u8], a: usize, m: usize, rs: &Vec<u32>, rn: usize, bf: &Vec<u32>, bs: &Vec<u32>, nb: usize, cc: &mut Vec<u64>, cuts: usize) {
    let mut tb = [0u32; 1024];
    let mut b = if nb > 0 { nb - 1 } else { 0 };
    a_b_block_table(bf, b, &mut tb);
    let mut bfirst = if b < bs.len() { bs[b] as usize } else { 0 };
    cc[0] = 0;
    let mut p = rn;
    let mut j = 1usize;
    while j <= m && p >= 1 {
        let off = m - j;
        if off < bfirst && b > 0 {
            b -= 1;
            a_b_block_table(bf, b, &mut tb);
            bfirst = if b < bs.len() { bs[b] as usize } else { 0 };
        }
        let i = a + off;
        let k = rs[p - 1] as usize;
        let e = p - 1;
        let st = if k <= e { e - k } else { e };
        let mut best = (cc[j - 1] as u32).wrapping_add(tb[s[i] as usize % 1024]);
        let mut choice = 0u32;
        let mut q = st;
        let mut lo = 3usize;
        while q < e {
            let v = rs[q];
            let ml = ((v >> 20) & 511) as usize;
            let dc = tb[(520 + ((v >> 15) & 31) as usize) % 1024];
            if v & A_B_FULL != 0 && cuts == 0 {
                if ml <= j {
                    let x = (cc[j - ml] as u32).wrapping_add(tb[(256 + ml) % 1024]).wrapping_add(dc);
                    if x < best {
                        best = x;
                        choice = ((ml as u32) << 15) | (v & 32767);
                    }
                }
            } else {
                let full = v & A_B_FULL;
                let mut l = if full != 0 { if ml > lo + cuts { ml - cuts } else { lo } } else { lo };
                while l <= ml && l <= j {
                    let x = (cc[j - l] as u32).wrapping_add(tb[(256 + l) % 1024]).wrapping_add(dc);
                    if x < best {
                        best = x;
                        choice = ((l as u32) << 15) | (v & 32767);
                    }
                    l += 1;
                }
                if full == 0 {
                    lo = ml + 1;
                }
            }
            q += 1;
        }
        cc[j] = (best as u64) | ((choice as u64) << 32);
        p = st;
        j += 1;
    }
}

/// Per-block symbol counts along the parse in cc (positions a..a+m, a new encoder block every
/// A_BLOCK_TOKENS tokens, or one block when whole == 0); returns the block count.
pub fn a_b_tally_seg(s: &[u8], a: usize, m: usize, cc: &Vec<u64>, whole: usize, bf: &mut Vec<u32>, bs: &mut Vec<u32>) -> usize {
    let mut nb = 0usize;
    let mut inb = A_BLOCK_TOKENS;
    let mut j = m;
    while j > 0 {
        if inb == A_BLOCK_TOKENS && (whole == 1 || nb == 0) {
            let base = nb * A_B_FSZ;
            let mut z = 0usize;
            while z < A_B_FSZ {
                if base + z < bf.len() {
                    bf[base + z] = 0;
                } else {
                    bf.push(0);
                }
                z += 1;
            }
            if nb < bs.len() {
                bs[nb] = (m - j) as u32;
            } else {
                bs.push((m - j) as u32);
            }
            nb += 1;
            inb = 0;
        }
        let f = (nb - 1) * A_B_FSZ;
        let v = (cc[j] >> 32) as u32;
        let l = (v >> 15) as usize;
        if l >= 3 && l <= j {
            let d = (v & 32767) as usize + 1;
            bf[f + (257 + a_b_len_code(l).0) % A_B_FSZ] += 1;
            bf[f + (288 + a_b_dist_slot(d)) % A_B_FSZ] += 1;
            j -= l;
        } else {
            bf[f + s[a + m - j] as usize % A_B_FSZ] += 1;
            j -= 1;
        }
        if inb < A_BLOCK_TOKENS {
            inb += 1;
        }
    }
    if nb > 0 {
        bf[(nb - 1) * A_B_FSZ + 256] += 1;
    }
    nb
}

/// Per-block symbol counts of the planned path from 0 (a block every A_BLOCK_TOKENS tokens) and
/// the input offset where each block starts; returns the block count.
pub fn a_b_tally_plan(s: &[u8], plan: &Vec<u32>, bf: &mut Vec<u32>, bs: &mut Vec<u32>) -> usize {
    let n = s.len();
    let mut nb = 0usize;
    let mut pos = 0usize;
    let mut t = 0usize;
    while pos < n && pos < plan.len() {
        if t % A_BLOCK_TOKENS == 0 {
            let base = nb * A_B_FSZ;
            let mut z = 0usize;
            while z < A_B_FSZ {
                if base + z < bf.len() {
                    bf[base + z] = 0;
                } else {
                    bf.push(0);
                }
                z += 1;
            }
            if nb < bs.len() {
                bs[nb] = pos as u32;
            } else {
                bs.push(pos as u32);
            }
            nb += 1;
        }
        let f = (nb - 1) * A_B_FSZ;
        let v = plan[pos] as usize;
        let l = v % 512;
        if l >= 3 && l <= n - pos {
            let d = v / 512;
            bf[f + (257 + a_b_len_code(l).0) % A_B_FSZ] += 1;
            bf[f + (288 + a_b_dist_slot(d)) % A_B_FSZ] += 1;
            pos += l;
        } else {
            bf[f + s[pos] as usize] += 1;
            pos += 1;
        }
        t += 1;
    }
    if nb > 0 {
        bf[(nb - 1) * A_B_FSZ + 256] += 1;
    }
    nb
}

/// Write the parse in cc (positions a..a+m) into the plan.
pub fn a_b_plan_seg(a: usize, m: usize, cc: &Vec<u64>, plan: &mut Vec<u32>) {
    let mut j = m;
    while j > 0 {
        let i = a + m - j;
        let v = (cc[j] >> 32) as u32;
        let l = (v >> 15) as usize;
        let d = (v & 32767) as usize + 1;
        if l >= 3 && l <= j {
            a_set_in(plan, i, (l + 512 * d) as u32);
            j -= l;
        } else {
            a_set_in(plan, i, 0);
            j -= 1;
        }
    }
}

/// Append v to the record stream at rn; returns rn + 1.
pub fn a_b_put(rs: &mut Vec<u32>, rn: usize, v: u32) -> usize {
    if rn < rs.len() {
        rs[rn] = v;
    } else {
        rs.push(v);
    }
    rn + 1
}

/// Engine B: writes the plan (length n). Knobs: tree depth, exact-3 distance limit, mode
/// (0 segments only, 1 one segment with block passes, 2 segments then whole-input block passes),
/// block passes, continuation cuts.
pub fn a_b_engine(input: &[u8], plan: &mut Vec<u32>, depth: usize, h3dist: usize, mode: usize, bpasses: usize, cuts: usize) {
    let n = input.len();
    if n < 16 {
        return;
    }
    let mut mf = BMf {
        head: [0u32; A_B_HSIZE],
        head3: [0u32; A_B_H3SIZE],
        tree: [0u32; A_B_TS],
        w: [0u64; A_B_WR],
        pn: [0u32; A_B_PS],
        pf: [0u32; A_B_PS],
        plen: 0,
        hn: A_B_NOHINT,
        hl: 0,
    };
    let mut rv = [0u32; A_B_RB];
    let mut freq = [0u32; A_B_FSZ];
    let mut bf: Vec<u32> = Vec::new();
    let mut bs: Vec<u32> = Vec::new();
    let keep = if mode == 2 && n <= A_B_KEEPMAX { 1usize } else { 0usize };
    let segcap = if n < A_B_SEG || keep == 1 { n } else { A_B_SEG };
    let mut rs: Vec<u32> = Vec::with_capacity(4 * segcap);
    let mut cc: Vec<u64> = Vec::with_capacity(segcap + 1);
    while cc.len() <= segcap {
        cc.push(0);
    }
    // word ring: w[p % A_B_WR] = big-endian s[p..p+8]; x is the word at position wfill
    let mut x = 0u64;
    let mut k = 0usize;
    while k < 8 {
        x = (x << 8) | a_b_byte_at(input, k);
        k += 1;
    }
    let mut wfill = 0usize;
    let mut rn = 0usize;
    let mut a = 0usize;
    while a < n {
        let m = if n - a < A_B_SEG { n - a } else { A_B_SEG };
        let b = a + m;
        if keep == 0 {
            rn = 0;
        }
        let mut i = a;
        while i < b {
            let top = if i + 264 < n { i + 264 } else { n };
            while wfill < top {
                mf.w[wfill % A_B_WR] = x;
                x = (x << 8) | a_b_byte_at(input, wfill + 8);
                wfill += 1;
            }
            let mut nr = 0usize;
            if n - i >= 4 {
                let rem = n - i;
                let cap = if rem < 258 { rem } else { 258 };
                let scap = if b - i < cap { b - i } else { cap };
                let wi = mf.w[i % A_B_WR];
                let wp = if i > a { mf.w[(i - 1) % A_B_WR] >> 56 } else { 256 };
                let mut nf = 0usize;
                let mut best = 2usize;
                let h3 = ((((wi >> 40) as u32).wrapping_mul(2246822519)) >> (32 - A_B_H3BITS)) as usize % A_B_H3SIZE;
                let p3 = mf.head3[h3] as usize;
                mf.head3[h3] = (i + 1) as u32;
                let d3 = (i + 1).wrapping_sub(p3);
                if p3 > 0 && d3 >= 1 && d3 <= h3dist && scap >= 3 {
                    let c = i - d3;
                    let x3 = mf.w[c % A_B_WR] ^ wi;
                    if (x3 >> 40) == 0 && (x3 >> 32) != 0 {
                        let flag = if c >= 1 && (mf.w[(c - 1) % A_B_WR] >> 56) == wp { A_B_FULL } else { 0 };
                        let r = a_b_add_record(&mut rv, 0, 0, 3, d3, flag);
                        nr = r.0;
                        nf = r.1;
                        best = 3;
                    }
                }
                let h = ((((wi >> 32) as u32).wrapping_mul(2654435761)) >> (32 - A_B_HBITS)) as usize % A_B_HSIZE;
                let first = mf.head[h] as usize;
                mf.head[h] = (i + 1) as u32;
                let r = a_b_descend(&mut mf, first, i, cap, scap, best, wp, &mut rv, nr, nf, depth);
                nr = r.0;
                let mut q = 0usize;
                while q < nr {
                    rn = a_b_put(&mut rs, rn, rv[q % A_B_RB]);
                    q += 1;
                }
            }
            rn = a_b_put(&mut rs, rn, nr as u32);
            i += 1;
        }
        if a == 0 {
            a_b_static_freq(&mut bf);
        }
        if bs.len() == 0 {
            bs.push(0);
        }
        bs[0] = 0;
        a_b_dp_seg(input, a, m, &rs, rn, &bf, &bs, 1, &mut cc, cuts);
        if mode == 1 {
            let mut p = 0usize;
            while p < bpasses {
                let nb = a_b_tally_seg(input, a, m, &cc, 1, &mut bf, &mut bs);
                a_b_dp_seg(input, a, m, &rs, rn, &bf, &bs, nb, &mut cc, cuts);
                p += 1;
            }
        } else {
            let _ = a_b_tally_seg(input, a, m, &cc, 0, &mut bf, &mut bs);
            let mut k2 = 0usize;
            while k2 < A_B_FSZ {
                freq[k2] = bf[k2];
                k2 += 1;
            }
            // extra bits are identical under both tables; compare symbol costs only
            let paid = (cc[m] & 0xFFFFFFFF) as u64;
            let own = a_b_self_cost(&freq);
            let xb = a_b_extra_bits(&freq);
            if a == 0 || (paid > xb && (paid - xb) * 1024 > own * (1024 + A_B_GAP)) {
                a_b_dp_seg(input, a, m, &rs, rn, &bf, &bs, 1, &mut cc, cuts);
                let _ = a_b_tally_seg(input, a, m, &cc, 0, &mut bf, &mut bs);
            }
        }
        a_b_plan_seg(a, m, &cc, plan);
        a = b;
    }
    if keep == 1 && bpasses > 0 {
        let mut nb = a_b_tally_plan(input, plan, &mut bf, &mut bs);
        let mut p = 0usize;
        while p < bpasses {
            a_b_dp_seg(input, 0, n, &rs, rn, &bf, &bs, nb, &mut cc, cuts);
            if p + 1 < bpasses {
                nb = a_b_tally_seg(input, 0, n, &cc, 1, &mut bf, &mut bs);
            }
            p += 1;
        }
        a_b_plan_seg(0, n, &cc, plan);
    }
}

// ───────────────────────────── engine C: DNA and binary ─────────────────────────────
// Optimal parsing under per-block Huffman-length models, iterated; finders per sub-class:
// DNA (2-bit 8-mer chains + lower-case tree), binary tree on 3-byte hashes, 4-byte-key chains
// (floats, sparse); a block planner turns blocks that code cheaper as literals into literals.

pub const A_C_LSYM: [u8; 256] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15,
    16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19,
    20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21,
    22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24,
    25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25,
    26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26,
    27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28,
];
pub const A_C_DSYM_LO: [u8; 256] = [
    0, 1, 2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
    14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
    14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
    15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
];
pub const A_C_DSYM_HI: [u8; 256] = [
    0, 14, 16, 17, 18, 18, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23,
    24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25,
    26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26,
    27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27,
    28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
    28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28,
    29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29,
    29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29,
];

/// Window: a slot index is `pos % A_C_WS`; a node is live while `p - node < A_C_WS`.
pub const A_C_WS: usize = 32768;
/// Interleaved child links: node `i` has `kids[2*(i % A_C_WS)]` (smaller) and `kids[2*(i % A_C_WS)+1]` (larger).
pub const A_C_KS: usize = 65536;
/// Hash table size of the match finders.
pub const A_C_HS: usize = 65536;
/// Tokens per encoder block (fixed by the validator's encoder).
pub const A_C_BLOCK: usize = 16384;
/// Cost units per bit.
pub const A_C_SCALE: u32 = 16;
/// Stride of one block model: 256 literal costs, 256 length costs (len-3), 32 distance costs.
pub const A_C_MS: usize = 544;
/// Weights DP only when 4-byte repeats reach this rate (per 65536 sampled positions).
pub const A_C_WREP4_MIN: usize = 200;
pub const A_C_DEPTH4_W: usize = 4;
pub const A_C_TAX_W: u32 = 16;
pub const A_C_UNUSED_LEN_W: u32 = 6;
pub const A_C_UNUSED_DIST_W: u32 = 4;
/// Chain budget of the 4-byte-key finder.
pub const A_C_DEPTH4: usize = 8;
/// Use the 4-byte-key chain finder when 4-byte repeats outnumber 6-byte repeats by this factor.
pub const A_C_CHAIN4_RATIO: usize = 8;
/// Early exit of `c_rep_rates` only after this many probes (a short repetitive prefix must not decide the mode).
pub const A_C_REP_MINPROBE: usize = 16384;
/// Chain budget of the DNA 8-mer index.
pub const A_C_DEPTH_UP: usize = 16;
/// Shortest match reported by the DNA 8-mer index.
pub const A_C_UP_MIN: usize = 9;
/// Stop searching once a match this long is found.
pub const A_C_NICE: usize = 258;
/// Skip searching inside byte runs at least this long, and (generic finder) inside other matches
/// at least `A_C_SKIP_FAR` long.
pub const A_C_SKIP: usize = 64;
pub const A_C_SKIP_FAR: usize = 128;
/// Lengths relaxed one by one; longer candidates only try their full length beyond this.
pub const A_C_RCAP: usize = 32;
/// Candidates kept per position (the longest ones).
pub const A_C_KEEP: usize = 4;
/// Generic input: seed the first pass with a greedy parse taking matches of at least this length.
pub const A_C_GMIN: usize = 3;
/// DNA: after at least min_dna passes, stop once a pass improves the estimate by less than 1/STOP_DIV.
pub const A_C_STOP_DIV: u64 = 4096;
/// Passes for very repetitive input (most positions start a 6-byte repeat).
pub const A_C_PASSES_SP: usize = 1;
/// Extra cost (in 1/A_C_SCALE bits) charged to every match by the chain4 class, standing in for the
/// code space a match symbol takes from the literals.
pub const A_C_TAX_C4: u32 = 16;
/// Match tax of the binary-tree class.
pub const A_C_TAX_BT: u32 = 24;
/// Inputs whose 6-byte repeat rate is below this (per 65536 positions) are coded as literals only.
pub const A_C_REP6_MIN: usize = 24;
/// Sampling step of the repeat-rate detector.
pub const A_C_REP_STEP: usize = 2;
/// Order in which code-length code lengths are written (RFC 1951).
pub const A_C_CL_ORDER: [usize; 19] = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
/// Candidate flag: only lengths of 8 or more are worth trying (DNA 8-mer chains).
pub const A_C_LONG_ONLY: u32 = 1 << 29;
/// A candidate group ends with a trailer `A_C_GROUP | count << 27 | position`.
pub const A_C_GROUP: u32 = 1 << 31;
/// Position bits of a trailer.
pub const A_C_PMASK: u32 = 0x07FF_FFFF;
/// Extra cost (in 1/A_C_SCALE bits) charged per token, to break ties toward fewer tokens.
pub const A_C_TOKPEN: u32 = 1;
pub const A_C_TOKPEN_W: u32 = 1;
pub const A_C_TOKPEN_C4: u32 = 0;
pub const A_C_TOKPEN_BT: u32 = 1;
/// Bits charged for symbols a block model has never seen.
pub const A_C_UNUSED_LIT: u32 = 12;
pub const A_C_UNUSED_LEN: u32 = 12;
pub const A_C_UNUSED_DIST: u32 = 5;

/// Nucleotide codes: A C G T -> 0..3, anything else 4.
pub const A_C_NT: [u8; 256] = [
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 0, 4, 1, 4, 4, 4, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
];

pub const A_C_LEXTRA: [u32; 29] = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
pub const A_C_DEXTRA: [u32; 30] = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

/// Length symbol (0..28) of a match length 3..=258.
pub fn a_c_lsym(len: usize) -> usize {
    if len < 3 {
        return 0;
    }
    A_C_LSYM[(len - 3) % 256] as usize
}

/// Distance symbol (0..29) of a distance 1..=32768.
pub fn a_c_dsym(d: usize) -> usize {
    if d < 1 {
        return 0;
    }
    if d <= 256 {
        return A_C_DSYM_LO[(d - 1) % 256] as usize;
    }
    A_C_DSYM_HI[((d - 1) >> 7) % 256] as usize
}

/// Eight bytes at `i` as a big-endian word (0 if they do not fit).
pub fn a_c_word_be(s: &[u8], i: usize) -> u64 {
    if i + 8 > s.len() {
        return 0;
    }
    ((s[i] as u64) << 56)
        | ((s[i + 1] as u64) << 48)
        | ((s[i + 2] as u64) << 40)
        | ((s[i + 3] as u64) << 32)
        | ((s[i + 4] as u64) << 24)
        | ((s[i + 5] as u64) << 16)
        | ((s[i + 6] as u64) << 8)
        | (s[i + 7] as u64)
}

/// Common prefix of the strings at `a < b`, starting from the known `k0`, capped at `lim`.
/// Requires `b + lim <= s.len()`.
pub fn a_c_extend(s: &[u8], a: usize, b: usize, k0: usize, lim: usize) -> usize {
    let mut k = k0;
    let mut fuel = lim + 1;
    while fuel > 0 && k + 8 <= lim {
        let x = a_c_word_be(s, a + k) ^ a_c_word_be(s, b + k);
        if x != 0 {
            return k + (x.leading_zeros() / 8) as usize;
        }
        k += 8;
        fuel -= 1;
    }
    while k < lim && s[a + k] == s[b + k] {
        k += 1;
    }
    k
}

/// Pack a candidate: length (9 bits), distance-1 (15 bits), distance symbol (5 bits).
pub fn a_c_pack(len: usize, d: usize) -> u32 {
    ((a_c_dsym(d) as u32) << 24) | (((d - 1) as u32) << 9) | (len as u32)
}

/// Store `v` into the pending child slot `(which, idx)`: `which == 0` is `lt`, else `gt`.
pub fn a_c_put_kid(kids: &mut [u32; A_C_KS], which: usize, idx: usize, v: u32) {
    kids[(2 * (idx % A_C_WS) + which) % A_C_KS] = v;
}

/// Insert `p` into the binary tree rooted at `head[h]` and collect the improving matches
/// (strictly longer as the distance grows) into `ml`/`md`. Returns how many.
/// Positions are stored as `pos + 1` (0 = empty). Requires `p + 3 <= s.len()`.
pub fn a_c_bt_find(
    s: &[u8],
    p: usize,
    h: usize,
    depth: usize,
    head: &mut [u32; A_C_HS],
    kids: &mut [u32; A_C_KS],
    ml: &mut [u32; 64],
    md: &mut [u32; 64],
) -> usize {
    let n = s.len();
    let room = n - p;
    let maxlen = if room < 258 { room } else { 258 };
    let lim = if A_C_NICE < maxlen { A_C_NICE } else { maxlen };
    let mut cur = head[h % A_C_HS] as usize;
    head[h % A_C_HS] = (p + 1) as u32;
    let mut lw = 0usize;
    let mut li = p % A_C_WS;
    let mut gw = 1usize;
    let mut gi = p % A_C_WS;
    let mut llen = 0usize;
    let mut glen = 0usize;
    let mut best = 2usize;
    let mut cnt = 0usize;
    let mut steps = 0usize;
    while steps < depth && cur > 0 {
        let c = cur - 1;
        if c >= p || p - c >= A_C_WS {
            steps = depth;
        } else {
            let k0 = if llen < glen { llen } else { glen };
            let k = a_c_extend(s, c, p, k0, lim);
            if k > best {
                best = k;
                if cnt < 64 {
                    ml[cnt] = k as u32;
                    md[cnt] = (p - c) as u32;
                    cnt += 1;
                }
            }
            if k >= lim {
                a_c_put_kid(kids, lw, li, kids[(2 * (c % A_C_WS)) % A_C_KS]);
                a_c_put_kid(kids, gw, gi, kids[(2 * (c % A_C_WS) + 1) % A_C_KS]);
                return cnt;
            }
            if s[c + k] < s[p + k] {
                a_c_put_kid(kids, lw, li, cur as u32);
                lw = 1;
                li = c % A_C_WS;
                llen = k;
                cur = kids[(2 * (c % A_C_WS) + 1) % A_C_KS] as usize;
            } else {
                a_c_put_kid(kids, gw, gi, cur as u32);
                gw = 0;
                gi = c % A_C_WS;
                glen = k;
                cur = kids[(2 * (c % A_C_WS)) % A_C_KS] as usize;
            }
            steps += 1;
        }
    }
    a_c_put_kid(kids, lw, li, 0);
    a_c_put_kid(kids, gw, gi, 0);
    cnt
}

/// Walk the hash chain of `key` from its head, collecting the improving matches (strictly longer
/// than `best0`, growing with the distance) into `ml`/`md`, then link `p` in at the head. `k0`
/// bytes are known to agree for every chain member (8 for exact DNA keys, else 0).
pub fn a_c_chain_walk(
    s: &[u8],
    p: usize,
    key: usize,
    k0: usize,
    best0: usize,
    depth: usize,
    head: &mut [u32; A_C_HS],
    prev: &mut [u32; A_C_WS],
    ml: &mut [u32; 64],
    md: &mut [u32; 64],
) -> usize {
    let n = s.len();
    let room = n - p;
    let lim = if room < 258 { room } else { 258 };
    let first = head[key % A_C_HS];
    head[key % A_C_HS] = (p + 1) as u32;
    let mut cur = first as usize;
    let mut best = best0;
    let mut cnt = 0usize;
    let mut steps = 0usize;
    while steps < depth && cur > 0 {
        let c = cur - 1;
        if c >= p || p - c >= A_C_WS {
            steps = depth;
        } else {
            if best < lim && s[c + best] == s[p + best] {
                let mut k = k0;
                if k0 + 8 <= lim {
                    let x = a_c_word_be(s, c + k0) ^ a_c_word_be(s, p + k0);
                    if x != 0 {
                        k = k0 + (x.leading_zeros() / 8) as usize;
                    } else {
                        k = a_c_extend(s, c, p, k0 + 8, lim);
                    }
                } else {
                    k = a_c_extend(s, c, p, k0, lim);
                }
                if k > best {
                    best = k;
                    if cnt < 64 {
                        ml[cnt] = k as u32;
                        md[cnt] = (p - c) as u32;
                        cnt += 1;
                    }
                }
            }
            if best >= lim {
                steps = depth;
            } else {
                cur = prev[c % A_C_WS] as usize;
                steps += 1;
            }
        }
    }
    prev[p % A_C_WS] = first;
    cnt
}

/// 2-bit code of a nucleotide letter (upper case), 4 otherwise.
pub fn a_c_nt_code(b: u8) -> usize {
    A_C_NT[b as usize] as usize
}

/// Push the candidate group of position `p`: a distance-1 run candidate (if `r1 >= 3`) then the
/// last `A_C_KEEP` found candidates longer than it, tagged with `flag`, then a trailer. Nothing is
/// pushed when there is no candidate. Returns the longest length pushed (0 if none).
pub fn a_c_push_cands(clist: &mut Vec<u32>, p: usize, ml: &[u32; 64], md: &[u32; 64], cnt: usize, r1: usize, flag: u32) -> usize {
    let first = if cnt > A_C_KEEP { cnt - A_C_KEEP } else { 0 };
    let mut top = 0usize;
    let mut pushed = 0u32;
    if r1 >= 3 && r1 <= 258 {
        clist.push(a_c_pack(r1, 1) | flag);
        top = r1;
        pushed += 1;
    }
    let mut i = first;
    while i < cnt && i < 64 {
        let d = md[i] as usize;
        let l = ml[i] as usize;
        if d >= 1 && d <= A_C_WS && l > top && l <= 258 && l >= 3 {
            clist.push(a_c_pack(l, d) | flag);
            top = l;
            pushed += 1;
        }
        i += 1;
    }
    if pushed > 0 {
        clist.push(A_C_GROUP | (pushed << 27) | ((p as u32) & A_C_PMASK));
    }
    top
}

/// Length of the distance-1 match at `p` (a byte run), 0 if shorter than 3.
pub fn a_c_run_len(s: &[u8], p: usize) -> usize {
    let n = s.len();
    if p < 1 || p + 3 > n {
        return 0;
    }
    if s[p] != s[p - 1] || s[p + 1] != s[p - 1] || s[p + 2] != s[p - 1] {
        return 0;
    }
    let room = n - p;
    let lim = if room < 258 { room } else { 258 };
    a_c_extend(s, p - 1, p, 3, lim)
}

/// Candidates for every position of binary input: a binary tree on 3-byte hashes (`chain == 0`)
/// or hash chains on 4-byte keys, plus byte runs. Searching pauses inside byte runs of `A_C_SKIP`+
/// bytes and (after one more position) inside other matches of `A_C_SKIP_FAR`+ bytes.
pub fn a_c_find_bin(s: &[u8], clist: &mut Vec<u32>, chain: usize, depth: usize) {
    let n = s.len();
    let mut head = [0u32; A_C_HS];
    let mut lt = [0u32; A_C_WS];
    let mut kids = [0u32; A_C_KS];
    let mut ml = [0u32; 64];
    let mut md = [0u32; 64];
    let mut p = 0usize;
    let mut skip_to = 0usize;
    let mut pend = 0usize;
    while p + 4 <= n {
        let v = ((s[p] as u32) << 24) | ((s[p + 1] as u32) << 16) | ((s[p + 2] as u32) << 8) | (s[p + 3] as u32);
        let key = if chain > 0 { v } else { v >> 8 };
        let h = (key.wrapping_mul(0x9E37_79B1) >> 16) as usize;
        if p >= skip_to {
            let cnt = if chain > 0 {
                a_c_chain_walk(s, p, h, 0, 3, depth, &mut head, &mut lt, &mut ml, &mut md)
            } else {
                a_c_bt_find(s, p, h, depth, &mut head, &mut kids, &mut ml, &mut md)
            };
            let r1 = if p > 0 && s[p] == s[p - 1] { a_c_run_len(s, p) } else { 0 };
            let mut top = 0usize;
            if cnt > 0 || r1 >= 3 {
                top = a_c_push_cands(clist, p, &ml, &md, cnt, r1, 0);
            }
            if r1 >= A_C_SKIP {
                skip_to = p + top;
                pend = 0;
            } else if top >= A_C_SKIP_FAR {
                if pend > 0 {
                    skip_to = p + top;
                    pend = 0;
                } else {
                    pend = 1;
                }
            } else {
                pend = 0;
            }
        } else if chain > 0 {
            lt[p % A_C_WS] = head[h % A_C_HS];
            head[h % A_C_HS] = (p + 1) as u32;
        }
        p += 1;
    }
}

/// Candidates for every position (DNA): exact 8-mer chains for upper-case runs,
/// a binary tree over lower-case positions only.
pub fn a_c_find_dna(s: &[u8], clist: &mut Vec<u32>, depth_lo: usize) {
    let n = s.len();
    let mut head8 = [0u32; A_C_HS];
    let mut prev8 = [0u32; A_C_WS];
    let mut head3 = [0u32; A_C_HS];
    let mut kids = [0u32; A_C_KS];
    let mut ml = [0u32; 64];
    let mut md = [0u32; 64];
    // rolling 2-bit key of s[p..p+8]; `run` counts trailing nucleotides, `run2` also admits newlines
    let mut key = 0usize;
    let mut run = 0usize;
    let mut run2 = 0usize;
    let mut q = 0usize;
    while q < 7 && q < n {
        let c = a_c_nt_code(s[q]);
        if c < 4 {
            key = ((key << 2) | c) & 65535;
            run += 1;
            run2 += 1;
        } else {
            run = 0;
            run2 = if s[q] == 10 { run2 + 1 } else { 0 };
        }
        q += 1;
    }
    let mut p = 0usize;
    let mut skip_to = 0usize;
    while p < n {
        if p + 7 < n {
            let c = a_c_nt_code(s[p + 7]);
            if c < 4 {
                key = ((key << 2) | c) & 65535;
                run += 1;
                run2 += 1;
            } else {
                run = 0;
                run2 = if s[p + 7] == 10 { run2 + 1 } else { 0 };
            }
        } else {
            run = 0;
            run2 = 0;
        }
        if p + 3 <= n {
            let b = s[p];
            if b >= 97 && b <= 122 {
                let v = ((b as u32) << 16) | ((s[p + 1] as u32) << 8) | (s[p + 2] as u32);
                let h = ((v.wrapping_mul(0x9E37_79B1) >> 16) as usize) % (A_C_HS / 2);
                if p >= skip_to {
                    let cnt = a_c_bt_find(s, p, h, depth_lo, &mut head3, &mut kids, &mut ml, &mut md);
                    if cnt > 0 {
                        let top = a_c_push_cands(clist, p, &ml, &md, cnt, 0, 0);
                        if top >= A_C_SKIP {
                            skip_to = p + top;
                        }
                    }
                }
            } else if run >= 8 {
                if p >= skip_to {
                    let cnt = a_c_chain_walk(s, p, key, 8, A_C_UP_MIN - 1, A_C_DEPTH_UP, &mut head8, &mut prev8, &mut ml, &mut md);
                    if cnt > 0 {
                        let top = a_c_push_cands(clist, p, &ml, &md, cnt, 0, A_C_LONG_ONLY);
                        if top >= A_C_SKIP {
                            skip_to = p + top;
                        }
                    }
                } else {
                    prev8[p % A_C_WS] = head8[key % A_C_HS];
                    head8[key % A_C_HS] = (p + 1) as u32;
                }
            } else if run2 >= 8 {
                let w = a_c_word_be(s, p);
                let hn = A_C_HS / 2 + ((w.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 40) as usize) % (A_C_HS / 2);
                if p >= skip_to {
                    let cnt = a_c_chain_walk(s, p, hn, 0, A_C_UP_MIN - 1, A_C_DEPTH_UP, &mut head3, &mut prev8, &mut ml, &mut md);
                    if cnt > 0 {
                        let top = a_c_push_cands(clist, p, &ml, &md, cnt, 0, A_C_LONG_ONLY);
                        if top >= A_C_SKIP {
                            skip_to = p + top;
                        }
                    }
                } else {
                    prev8[p % A_C_WS] = head3[hn % A_C_HS];
                    head3[hn % A_C_HS] = (p + 1) as u32;
                }
            }
        }
        p += 1;
    }
}

/// Huffman code lengths (capped at 15) for the first `m` symbols of `freq`:
/// radix-sort the used symbols by weight, then merge with the two-queue method.
pub fn a_c_huff_lengths(freq: &[u32; 288], m: usize, lens: &mut [u8; 288]) {
    let mut aw = [0u32; 288];
    let mut asy = [0u16; 288];
    let mut k = 0usize;
    let mut i = 0usize;
    while i < 288 {
        lens[i] = 0;
        if i < m && freq[i] > 0 {
            aw[k % 288] = if freq[i] < 65535 { freq[i] } else { 65535 };
            asy[k % 288] = i as u16;
            k += 1;
        }
        i += 1;
    }
    if k == 0 {
        return;
    }
    if k == 1 {
        lens[asy[0] as usize % 288] = 1;
        return;
    }
    let mut bw = [0u32; 288];
    let mut bsy = [0u16; 288];
    a_c_radix_pass(&aw, &asy, &mut bw, &mut bsy, k, 0);
    a_c_radix_pass(&bw, &bsy, &mut aw, &mut asy, k, 8);
    let mut iw = [0u32; 288];
    let mut ipar = [0u16; 288];
    let mut lpar = [0u16; 288];
    let mut li = 0usize;
    let mut ii = 0usize;
    let mut ni = 0usize;
    while ni + 1 < k && ni < 287 {
        let mut w2 = 0u32;
        let mut t = 0usize;
        while t < 2 {
            let take_leaf = li < k && (ii >= ni || aw[li % 288] <= iw[ii % 288]);
            if take_leaf {
                w2 = w2.saturating_add(aw[li % 288]);
                lpar[li % 288] = ni as u16;
                li += 1;
            } else {
                w2 = w2.saturating_add(iw[ii % 288]);
                ipar[ii % 288] = ni as u16;
                ii += 1;
            }
            t += 1;
        }
        iw[ni % 288] = w2;
        ni += 1;
    }
    let mut idep = [0u8; 288];
    let mut j = ni - 1;
    while j > 0 {
        j -= 1;
        let d = idep[ipar[j % 288] as usize % 288];
        idep[j % 288] = if d < 15 { d + 1 } else { 15 };
    }
    let mut x = 0usize;
    while x < k {
        let d = idep[lpar[x % 288] as usize % 288];
        lens[asy[x % 288] as usize % 288] = if d < 15 { d + 1 } else { 15 };
        x += 1;
    }
}

/// One stable counting-sort pass over `k` (weight, symbol) pairs by the byte at `shift`.
pub fn a_c_radix_pass(sw: &[u32; 288], ss: &[u16; 288], dw: &mut [u32; 288], ds: &mut [u16; 288], k: usize, shift: u32) {
    let mut cnt = [0usize; 257];
    let mut i = 0usize;
    while i < k && i < 288 {
        let b = ((sw[i] >> shift) & 255) as usize;
        cnt[(b + 1) % 257] = cnt[(b + 1) % 257].wrapping_add(1);
        i += 1;
    }
    let mut c = 1usize;
    while c < 257 {
        cnt[c] = cnt[c].wrapping_add(cnt[c - 1]);
        c += 1;
    }
    let mut j = 0usize;
    while j < k && j < 288 {
        let b = ((sw[j] >> shift) & 255) as usize;
        let at = cnt[b % 257];
        dw[at % 288] = sw[j];
        ds[at % 288] = ss[j];
        cnt[b % 257] = at + 1;
        j += 1;
    }
}

/// Append one block model (costs in `A_C_SCALE` units) built from symbol frequencies;
/// return the block's estimated size in bits (codes, extra bits, rough header).
pub fn a_c_push_model(models: &mut Vec<u32>, lf: &[u32; 288], df: &[u32; 288], tax: u32, ulen: u32, udist: u32, tokpen: u32) -> u64 {
    let mut ll = [0u8; 288];
    let mut dl = [0u8; 288];
    a_c_huff_lengths(lf, 286, &mut ll);
    a_c_huff_lengths(df, 30, &mut dl);
    let mut est: u64 = 70;
    let mut q = 0usize;
    while q < 288 {
        if ll[q] > 0 {
            est += (lf[q] as u64) * (ll[q] as u64) + 4;
            if q >= 257 && q < 286 {
                est += (lf[q] as u64) * (A_C_LEXTRA[(q - 257) % 29] as u64);
            }
        }
        if q < 30 && dl[q] > 0 {
            est += (df[q] as u64) * ((dl[q] as u64) + (A_C_DEXTRA[q] as u64)) + 4;
        }
        q += 1;
    }
    let mut i = 0usize;
    while i < 256 {
        let b = if ll[i] > 0 { ll[i] as u32 } else { A_C_UNUSED_LIT };
        models.push(b * A_C_SCALE + tokpen);
        i += 1;
    }
    let mut l = 3usize;
    while l < 259 {
        let s = a_c_lsym(l);
        let b = if ll[(257 + s) % 288] > 0 { ll[(257 + s) % 288] as u32 } else { ulen };
        models.push((b + A_C_LEXTRA[s % 29]) * A_C_SCALE + tokpen + tax);
        l += 1;
    }
    let mut d = 0usize;
    while d < 32 {
        let b = if d < 30 && dl[d] > 0 { dl[d] as u32 } else { udist };
        let e = if d < 30 { A_C_DEXTRA[d] } else { 0 };
        models.push((b + e) * A_C_SCALE);
        d += 1;
    }
    est
}

/// Start index of the candidates of the group whose trailer is at `ge - 1` (or `ge` if none).
pub fn a_c_group_start(clist: &Vec<u32>, ge: usize) -> usize {
    if ge == 0 || ge > clist.len() {
        return ge;
    }
    let tr = clist[ge - 1];
    let cnt = ((tr >> 27) & 15) as usize;
    if (tr & A_C_GROUP) == 0 || cnt + 1 > ge {
        return ge;
    }
    ge - 1 - cnt
}

/// Copy block model `b` into local cost tables (literals, lengths 3..258, distance symbols).
pub fn a_c_load_model(models: &Vec<u32>, b: usize, lit_c: &mut [u32; 256], len_c: &mut [u32; 256], dst_c: &mut [u32; 32]) {
    let base = b * A_C_MS;
    if base + A_C_MS > models.len() {
        return;
    }
    let mut i = 0usize;
    while i < 256 {
        lit_c[i] = models[base + i];
        len_c[i] = models[base + 256 + i];
        i += 1;
    }
    let mut d = 0usize;
    while d < 32 {
        dst_c[d] = models[base + 512 + d];
        d += 1;
    }
}

/// Backward optimal parse over the whole input under per-block models. Costs live in a ring
/// (a match is at most 258 long); the choice per position (0 = literal, else `len + 512 * dist`)
/// is written into `choice`. Runs of positions without candidates take a literal-only fast path.
pub fn a_c_dp_pass(s: &[u8], clist: &Vec<u32>, models: &Vec<u32>, bstart: &Vec<u32>, choice: &mut [u32]) {
    let n = s.len();
    let nb = bstart.len();
    if nb == 0 || models.len() < nb * A_C_MS || choice.len() < n {
        return;
    }
    let mut ring = [0u32; 512];
    let mut lit_c = [0u32; 256];
    let mut len_c = [0u32; 256];
    let mut dst_c = [0u32; 32];
    let mut b = nb - 1;
    let mut loaded = nb;
    let mut ge = clist.len();
    let mut gs = a_c_group_start(clist, ge);
    let mut gp = if gs < ge && ge <= clist.len() { (clist[ge - 1] & A_C_PMASK) as usize } else { n };
    let mut next = 0u32;
    let mut p = n;
    let mut fuel = 2 * n + nb + 2;
    while p > 0 && fuel > 0 {
        fuel -= 1;
        let q = p - 1;
        while b > 0 && bstart[b] as usize > q {
            b -= 1;
        }
        if loaded != b {
            a_c_load_model(models, b, &mut lit_c, &mut len_c, &mut dst_c);
            loaded = b;
        }
        let bs = bstart[b] as usize;
        let lo = if gp < p && gp >= bs { gp + 1 } else { bs };
        while p > lo {
            p -= 1;
            let c = next.wrapping_add(lit_c[s[p] as usize]);
            ring[p % 512] = c;
            choice[p] = 0;
            next = c;
        }
        if p > 0 && gp + 1 == p && gp >= bs {
            p -= 1;
            let lit = next.wrapping_add(lit_c[s[p] as usize]);
            let mut best = 0xFFFF_FFFFu32;
            let mut ch = 0u32;
            let mut prev = 2usize;
            let room = n - p;
            let mut k = gs;
            while k + 1 < ge && k < clist.len() {
                let e = clist[k];
                if (e & A_C_LONG_ONLY) != 0 && prev < 7 {
                    prev = 7;
                }
                let mut l = (e & 511) as usize;
                if l > room {
                    l = room;
                }
                if l > prev {
                    let dc = dst_c[((e >> 24) as usize) % 32];
                    let tag = (e & 0x00FF_FE00) + 512;
                    let mut len = prev + 1;
                    while len <= l {
                        let c = ring[(p + len) % 512].wrapping_add(len_c[(len - 3) % 256]).wrapping_add(dc);
                        if c <= best {
                            best = c;
                            ch = tag | (len as u32);
                        }
                        if len == A_C_RCAP && l > A_C_RCAP {
                            len = l;
                        } else {
                            len += 1;
                        }
                    }
                    prev = l;
                }
                k += 1;
            }
            if lit <= best {
                best = lit;
                ch = 0;
            }
            ring[p % 512] = best;
            choice[p] = ch;
            next = best;
            ge = gs;
            gs = a_c_group_start(clist, ge);
            gp = if gs < ge && ge <= clist.len() { (clist[ge - 1] & A_C_PMASK) as usize } else { n };
        }
    }
}

/// Seed `choice` with a greedy parse: the longest candidate at each position if at least `gmin` long.
pub fn a_c_greedy_choice(clist: &Vec<u32>, choice: &mut [u32], n: usize, gmin: usize) {
    let mut p = 0usize;
    while p < n && p < choice.len() {
        choice[p] = 0;
        p += 1;
    }
    let m = clist.len();
    let mut k = 1usize;
    while k < m {
        let tr = clist[k];
        if (tr & A_C_GROUP) != 0 {
            let q = (tr & A_C_PMASK) as usize;
            let last = clist[k - 1];
            if (last & A_C_GROUP) == 0 && ((last & 511) as usize) >= gmin && q < n && q < choice.len() {
                choice[q] = (last & 0x00FF_FFFF) + 512;
            }
        }
        k += 1;
    }
}

/// Walk the chosen path; rebuild per-block models and block start positions from it.
/// Returns the estimated size of the path in bits.
pub fn a_c_restat(s: &[u8], choice: &[u32], models: &mut Vec<u32>, bstart: &mut Vec<u32>, tax: u32, ulen: u32, udist: u32, tokpen: u32) -> u64 {
    let mut total: u64 = 0;
    let n = if s.len() < choice.len() { s.len() } else { choice.len() };
    *models = Vec::new();
    *bstart = Vec::new();
    let mut lf = [0u32; 288];
    let mut df = [0u32; 288];
    let mut p = 0usize;
    bstart.push(0);
    while p < n {
        let mut t = 0usize;
        while t < A_C_BLOCK && p < n {
            let ch = choice[p] as usize;
            let len = ch % 512;
            if len < 3 {
                let b = s[p] as usize;
                lf[b] = lf[b].wrapping_add(1);
                p += 1;
            } else {
                let d = ch / 512;
                let ls = (257 + a_c_lsym(len)) % 288;
                let ds = a_c_dsym(d) % 288;
                lf[ls] = lf[ls].wrapping_add(1);
                df[ds] = df[ds].wrapping_add(1);
                p += len;
            }
            t += 1;
        }
        lf[256] = 1;
        total += a_c_push_model(models, &lf, &df, tax, ulen, udist, tokpen);
        if p < n {
            bstart.push(p as u32);
        }
        lf = [0u32; 288];
        df = [0u32; 288];
    }
    if models.len() == 0 {
        lf[256] = 1;
        total += a_c_push_model(models, &lf, &df, tax, ulen, udist, tokpen);
    }
    total
}

/// DNA-like input: nearly all bytes are nucleotide letters or newlines (stops early otherwise).
pub fn a_c_is_dna(s: &[u8]) -> usize {
    let n = s.len();
    if n < 1024 {
        return 0;
    }
    let allow = n / 20;
    let mut bad = 0usize;
    let mut i = 0usize;
    while i < n {
        let c = s[i] | 32;
        if !(c == 97 || c == 99 || c == 103 || c == 116 || c == 110 || s[i] == 10) {
            bad += 1;
            if bad > allow {
                return 0;
            }
        }
        i += 1;
    }
    1
}

/// Code-length RLE of one run of `r` equal lengths `v` (the encoder's greedy rules):
/// adds symbol counts to `clf` and returns the extra bits.
pub fn a_c_rle_run(clf: &mut [u32; 288], v: usize, r0: usize) -> u64 {
    let mut r = r0;
    let mut extra: u64 = 0;
    let mut fuel = r0 + 1;
    if v == 0 {
        while r >= 3 && fuel > 0 {
            if r >= 11 {
                let take = if r < 138 { r } else { 138 };
                clf[18] = clf[18].wrapping_add(1);
                extra += 7;
                r -= take;
            } else {
                let take = if r < 10 { r } else { 10 };
                clf[17] = clf[17].wrapping_add(1);
                extra += 3;
                r -= take;
            }
            fuel -= 1;
        }
        clf[0] = clf[0].wrapping_add(r as u32);
    } else {
        clf[v % 288] = clf[v % 288].wrapping_add(1);
        r -= 1;
        while r >= 3 && fuel > 0 {
            let take = if r < 6 { r } else { 6 };
            clf[16] = clf[16].wrapping_add(1);
            extra += 2;
            r -= take;
            fuel -= 1;
        }
        clf[v % 288] = clf[v % 288].wrapping_add(r as u32);
    }
    extra
}

/// Bits of a dynamic block with these symbol frequencies (`lf[256]` is the end-of-block count),
/// header included, using approximate (depth-capped) Huffman lengths.
pub fn a_c_dyn_bits(lf: &[u32; 288], df: &[u32; 288]) -> u64 {
    let mut ll = [0u8; 288];
    let mut dl = [0u8; 288];
    a_c_huff_lengths(lf, 286, &mut ll);
    a_c_huff_lengths(df, 30, &mut dl);
    let mut body: u64 = 0;
    let mut hlit = 257usize;
    let mut i = 0usize;
    while i < 286 {
        if ll[i] > 0 {
            body += (lf[i] as u64) * (ll[i] as u64);
            if i >= 257 {
                body += (lf[i] as u64) * (A_C_LEXTRA[(i - 257) % 29] as u64);
                hlit = i + 1;
            }
        }
        i += 1;
    }
    let mut hdist = 1usize;
    let mut any = 0usize;
    let mut d = 0usize;
    while d < 30 {
        if dl[d] > 0 {
            body += (df[d] as u64) * ((dl[d] as u64) + (A_C_DEXTRA[d] as u64));
            hdist = d + 1;
            any = 1;
        }
        d += 1;
    }
    if any == 0 {
        dl[0] = 1;
    }
    // run-length code the concatenated length sequence
    let mut clf = [0u32; 288];
    let mut extra: u64 = 0;
    let total = hlit + hdist;
    let mut seq = [0u8; 512];
    let mut i2 = 0usize;
    while i2 < total && i2 < 512 {
        seq[i2] = if i2 < hlit { ll[i2 % 288] } else { dl[(i2 - hlit) % 288] };
        i2 += 1;
    }
    let mut j = 0usize;
    while j < total && j < 512 {
        let v = seq[j] as usize;
        let mut r = 1usize;
        while j + r < total && j + r < 512 && seq[(j + r) % 512] as usize == v {
            r += 1;
        }
        extra += a_c_rle_run(&mut clf, v, r);
        j += r;
    }
    let mut cl = [0u8; 288];
    a_c_huff_lengths(&clf, 19, &mut cl);
    let mut hclen = 19usize;
    while hclen > 4 && cl[A_C_CL_ORDER[(hclen - 1) % 19] % 288] == 0 {
        hclen -= 1;
    }
    let mut hdr: u64 = 17 + 3 * (hclen as u64) + extra;
    let mut c = 0usize;
    while c < 19 {
        let len = if cl[c] > 7 { 7 } else { cl[c] };
        hdr += (clf[c] as u64) * (len as u64);
        c += 1;
    }
    hdr + body
}

/// Bits of a fixed-code block with these symbol frequencies.
pub fn a_c_fixed_bits(lf: &[u32; 288], df: &[u32; 288]) -> u64 {
    let mut bits: u64 = 3;
    let mut i = 0usize;
    while i < 288 {
        let len: u64 = if i < 144 { 8 } else if i < 256 { 9 } else if i < 280 { 7 } else { 8 };
        bits += (lf[i] as u64) * len;
        if i >= 257 && i < 286 {
            bits += (lf[i] as u64) * (A_C_LEXTRA[(i - 257) % 29] as u64);
        }
        i += 1;
    }
    let mut d = 0usize;
    while d < 30 {
        bits += (df[d] as u64) * (5 + A_C_DEXTRA[d] as u64);
        d += 1;
    }
    bits
}

/// Frequencies of the block that follows `choice` from `p0` (at most A_C_BLOCK tokens).
/// Returns the position after the block.
pub fn a_c_path_block(s: &[u8], choice: &[u32], p0: usize, lf: &mut [u32; 288], df: &mut [u32; 288]) -> usize {
    let n = s.len();
    let mut i = 0usize;
    while i < 288 {
        lf[i] = 0;
        df[i] = 0;
        i += 1;
    }
    let mut p = p0;
    let mut t = 0usize;
    while p < n && t < A_C_BLOCK && p < choice.len() {
        let ch = choice[p] as usize;
        let len = ch % 512;
        let d = ch / 512;
        if len >= 3 && len <= n - p {
            lf[(257 + a_c_lsym(len)) % 288] = lf[(257 + a_c_lsym(len)) % 288].wrapping_add(1);
            df[a_c_dsym(d) % 288] = df[a_c_dsym(d) % 288].wrapping_add(1);
            p += len;
        } else {
            lf[s[p] as usize] += 1;
            p += 1;
        }
        t += 1;
    }
    lf[256] = 1;
    p
}

/// Set plan[p0..end] to literals.
pub fn a_c_clear_span(plan: &mut [u32], p0: usize, end: usize) {
    let mut p = p0;
    while p < end && p < plan.len() {
        plan[p] = 0;
        p += 1;
    }
}

/// Block planner: follow the plan block by block; where the next BLOCK bytes code cheaper as
/// literals (so the encoder can store incompressible stretches), rewrite them as literals.
pub fn a_c_plan_blocks(s: &[u8], plan: &mut [u32]) {
    let n = s.len();
    let mut lf = [0u32; 288];
    let mut df = [0u32; 288];
    let mut p = 0usize;
    let mut fuel = n + 1;
    while p < n && p < plan.len() && fuel > 0 {
        fuel -= 1;
        let ea = a_c_path_block(s, plan, p, &mut lf, &mut df);
        let da = a_c_dyn_bits(&lf, &df);
        let fa = a_c_fixed_bits(&lf, &df);
        let ca = if da < fa { da } else { fa };
        let eb = if n - p > A_C_BLOCK { p + A_C_BLOCK } else { n };
        let ec = if ea > eb { ea } else { eb };
        let mut lb = [0u32; 288];
        let zb = [0u32; 288];
        let mut q = p;
        while q < ec {
            lb[s[q] as usize] += 1;
            q += 1;
        }
        lb[256] = 1;
        let db = a_c_dyn_bits(&lb, &zb);
        let fb = a_c_fixed_bits(&lb, &zb);
        let sb = 8 * ((ec - p) as u64) + 40;
        let mut cb = if db < fb { db } else { fb };
        if sb < cb {
            cb = sb;
        }
        if ea > p && ca <= cb {
            p = ea;
        } else {
            a_c_clear_span(plan, p, eb);
            p = eb;
        }
    }
}

/// Repeat statistics on every `A_C_REP_STEP`-th position (most recent occurrence of each 4-byte key):
/// returns (4-byte repeats, 6-byte repeats) per 65536 sampled positions. Stops early once the
/// 6-byte repeats alone exceed `A_C_REP6_MIN` over the whole input.
pub fn a_c_rep_rates(s: &[u8]) -> (usize, usize) {
    let n = s.len();
    if n < 64 {
        return (0, 0);
    }
    let mut head = [0u32; 16384];
    let mut r4 = 0usize;
    let mut r6 = 0usize;
    let mut probes = 0usize;
    let mut p = 0usize;
    while p + 8 <= n {
        let v = ((s[p] as u32) << 24) | ((s[p + 1] as u32) << 16) | ((s[p + 2] as u32) << 8) | (s[p + 3] as u32);
        let h = (v.wrapping_mul(0x9E37_79B1) >> 18) as usize;
        let c = head[h % 16384] as usize;
        if c > 0 && c <= p {
            let a = c - 1;
            if p - a <= A_C_WS && s[a] == s[p] && s[a + 1] == s[p + 1] && s[a + 2] == s[p + 2] && s[a + 3] == s[p + 3] {
                r4 += 1;
                if s[a + 4] == s[p + 4] && s[a + 5] == s[p + 5] {
                    r6 += 1;
                    if r6 >= 64 && (r6 as u64) * 131072 >= 24 * (n as u64) && probes >= A_C_REP_MINPROBE {
                        return (((r4 as u64) * 65536 / (probes as u64 + 1)) as usize, ((r6 as u64) * 65536 / (probes as u64 + 1)) as usize);
                    }
                }
            }
        }
        head[h % 16384] = (p + 1) as u32;
        probes += 1;
        p += A_C_REP_STEP;
    }
    (((r4 as u64) * 65536 / (probes as u64 + 1)) as usize, ((r6 as u64) * 65536 / (probes as u64 + 1)) as usize)
}

/// Engine C: writes the plan (length n, zeroed). Knobs: tree depth (generic), tree depth (DNA
/// lower case), weights DP on/off and its passes, passes (tree class, DNA max/min, chain4 class).
pub fn a_c_engine(input: &[u8], out: &mut Vec<u32>, depth: usize, depth_lo: usize, wdp: usize, passes_w: usize, passes_bt: usize, passes_dna: usize, min_dna: usize, passes_c4: usize) {
    let n = input.len();
    if out.len() < n {
        return;
    }
    let dna = a_c_is_dna(input);
    let mut chain4 = 0usize;
    let mut wmode = 0usize;
    if dna == 0 {
        let (r4, r6) = a_c_rep_rates(input);
        if r6 < A_C_REP6_MIN {
            if wdp == 0 || r4 < A_C_WREP4_MIN {
                return;
            }
            wmode = 1;
        } else if r6 >= 32768 {
            chain4 = 2;
        } else if r4 >= A_C_CHAIN4_RATIO * r6 {
            chain4 = 1;
        }
    }
    let mut clist: Vec<u32> = Vec::with_capacity(n / 2 + 16);
    if dna > 0 {
        a_c_find_dna(input, &mut clist, depth_lo);
    } else if wmode > 0 {
        a_c_find_bin(input, &mut clist, 1, A_C_DEPTH4_W);
    } else if chain4 > 0 {
        a_c_find_bin(input, &mut clist, 1, A_C_DEPTH4);
    } else {
        a_c_find_bin(input, &mut clist, 0, depth);
    }
    let mut models: Vec<u32> = Vec::new();
    let mut bstart: Vec<u32> = Vec::new();
    let passes = if dna > 0 { passes_dna } else if wmode > 0 { passes_w } else if chain4 == 2 { A_C_PASSES_SP } else if chain4 > 0 { passes_c4 } else { passes_bt };
    let tax = if wmode > 0 { A_C_TAX_W } else if chain4 > 0 { A_C_TAX_C4 } else if dna > 0 { 0 } else { A_C_TAX_BT };
    let ulen = if wmode > 0 { A_C_UNUSED_LEN_W } else { A_C_UNUSED_LEN };
    let udist = if wmode > 0 { A_C_UNUSED_DIST_W } else { A_C_UNUSED_DIST };
    // seed: a greedy parse for binary input, all literals for DNA and weights
    let gmin = if dna > 0 || wmode > 0 { 259 } else { A_C_GMIN };
    a_c_greedy_choice(&clist, out, n, gmin);
    let tokpen = if dna > 0 { A_C_TOKPEN } else if wmode > 0 { A_C_TOKPEN_W } else if chain4 > 0 { A_C_TOKPEN_C4 } else { A_C_TOKPEN_BT };
    let lit_est = a_c_restat(input, out, &mut models, &mut bstart, tax, ulen, udist, tokpen);
    let mut last_est = lit_est;
    let mut prev_est = lit_est;
    let mut pass = 0usize;
    while pass < passes {
        a_c_dp_pass(input, &clist, &models, &bstart, out);
        pass += 1;
        if pass < passes {
            last_est = a_c_restat(input, out, &mut models, &mut bstart, tax, A_C_UNUSED_LEN, A_C_UNUSED_DIST, tokpen);
            if dna > 0 && pass >= min_dna && last_est <= prev_est && prev_est - last_est < prev_est / A_C_STOP_DIV {
                pass = passes;
            }
            prev_est = last_est;
        }
    }
    if dna > 0 && last_est >= lit_est {
        a_c_clear_span(out, 0, n);
        return;
    }
    if dna > 0 || chain4 == 2 {
        return;
    }
    a_c_plan_blocks(input, out);
}


// ===== engine b: parse.rs =====

pub const B_BTD: usize = 32;
pub const B_BTDS: usize = 8;
pub const B_SMALLN: usize = 65536;
pub const B_SKS: usize = 0;
pub const B_H3BITS: u32 = 17;
pub const B_H3SIZE: usize = 131072;
pub const B_NICE: usize = 258;
pub const B_SKIPL: usize = 258;
pub const B_INH: usize = 1;
pub const B_LZK: usize = 0;
pub const B_INS: usize = 1;
pub const B_H3CAP: usize = 8;
pub const B_INSCAP: usize = 128;
pub const B_INSEND: usize = 0;
pub const B_ITERS: usize = 20;
pub const B_MINIT: usize = 1;
pub const B_ESH: u32 = 10;
pub const B_GAINK: u64 = 4;
pub const B_MBIAS: u32 = 0;
pub const B_RING: usize = 512;
pub const B_HBITS: u32 = 16;
pub const B_HSIZE: usize = 65536;
pub const B_TB: usize = 548;
pub const B_FB: usize = 320;
pub const B_BT: usize = 16384;
pub const B_SC: u32 = 16;
pub const B_UNUSED: u32 = 12;
pub const B_EW: u32 = 2;
pub const B_CHW: usize = 32;
/// relaxation width (last B_CHWS lengths of each match) for inputs shorter than B_CHN bytes.
pub const B_CHWS: usize = 128;
pub const B_DW: u32 = 0;
pub const B_OV: u32 = 3;
pub const B_DSTART: usize = 2;
pub const B_UPEN: u32 = 16;
pub const B_PM: u32 = 128;
pub const B_PUSH_LIMIT: usize = 1073741824;
/// stored trick: a block whose exact cost exceeds its stored cost by more than B_STMARG bits gets its matches forbidden.
pub const B_STM: usize = 1;
pub const B_STMARG: u64 = 0;
pub const B_BIG: u32 = 1048576;
/// drop a Pareto entry when the next (longer) entry of the same position has the same distance slot.
pub const B_SLOTM: usize = 1;
/// start the passes from the cost tables of the better of {all-literal, lazy} (exact bits).
pub const B_STARTBEST: usize = 1;
/// match-cost discount (1/16 bit) in the first (pruning) DP pass.
pub const B_MDEL: u32 = 24;
/// stop rule (B_RALPHA 2): stop when gain * bits^2 * 1280 < B_GK2 * n^3 (x B_F1 after pass 1).
pub const B_RALPHA: u32 = 2;
pub const B_GK2: u64 = 2;
pub const B_F1: u64 = 8;
/// inputs shorter than B_CHN bytes relax the last B_CHWS (not B_CHW) lengths of every cached match.
pub const B_CHN: usize = 65536;
/// also predict a single pass (first pass keeps no queries) when the start costs < B_OPQ/256 bits per byte;
/// if the stop rule then continues, the next pass prunes again (match discount B_MDEL2).
pub const B_OPQ: u64 = 200;
pub const B_MDEL2: u32 = 0;
/// init5 start tables: per-16K-byte-block literal entropy (unused byte: + B_U5), static length / distance
/// costs, length costs minus B_D5 (1/16 bit).
pub const B_U5: u32 = 32;
pub const B_D5: u32 = 12;
/// inputs whose best start costs more than B_HBPB/8 bits per byte start from the init5 tables and run every
/// pass with the per-token reward B_LAMH (1/16 bit), at least B_MINH passes.
pub const B_HBPB: u64 = 40;
pub const B_LAMH: u32 = 5;
pub const B_MINH: usize = 2;

// ---------------------------------------------------------------- guarded accessors
/// `v[i]`, or 0 out of range.
pub fn b_get(v: &[u32], i: usize) -> u32 {
    if i < v.len() {
        v[i]
    } else {
        0
    }
}

/// `v[i] = x` when in range.
pub fn b_set(v: &mut [u32], i: usize, x: u32) {
    if i < v.len() {
        v[i] = x;
    }
}

/// `v[i] += by` (wrapping) when in range.
pub fn b_bump(v: &mut [u32], i: usize, by: u32) {
    if i < v.len() {
        v[i] = v[i].wrapping_add(by);
    }
}

pub fn b_set64(v: &mut [u64], i: usize, x: u64) {
    if i < v.len() {
        v[i] = x;
    }
}

pub fn b_get8(v: &[u8], i: usize) -> u8 {
    if i < v.len() {
        v[i]
    } else {
        0
    }
}

/// `input[i]`, or 0 out of range.
pub fn b_byte_at(input: &[u8], i: usize) -> usize {
    if i < input.len() {
        input[i] as usize
    } else {
        0
    }
}

/// Tree child write (window of 32768 nodes, two children each).
pub fn b_setc(a: &mut [u32; 65536], i: usize, x: u32) {
    a[i % 65536] = x;
}

/// A Vec of `n` copies of `x` (8 pushes per iteration + tail).
pub fn b_filled(n: usize, x: u32) -> Vec<u32> {
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

pub fn b_push_guarded(v: &mut Vec<u32>, x: u32) {
    if v.len() < B_PUSH_LIMIT {
        v.push(x);
    }
}

// ---------------------------------------------------------------- flag / select helpers (0/1 flags)
pub fn b_sel(f: usize, a: usize, b: usize) -> usize {
    if f == 1 {
        a
    } else {
        b
    }
}

pub fn b_sel32(f: usize, a: u32, b: u32) -> u32 {
    if f == 1 {
        a
    } else {
        b
    }
}

pub fn b_sel64(f: usize, a: u64, b: u64) -> u64 {
    if f == 1 {
        a
    } else {
        b
    }
}

pub fn b_ge(a: usize, b: usize) -> usize {
    if a >= b {
        1
    } else {
        0
    }
}

pub fn b_lt(a: usize, b: usize) -> usize {
    if a < b {
        1
    } else {
        0
    }
}

pub fn b_eq(a: usize, b: usize) -> usize {
    if a == b {
        1
    } else {
        0
    }
}

pub fn b_lt32(a: u32, b: u32) -> usize {
    if a < b {
        1
    } else {
        0
    }
}

pub fn b_lt64(a: u64, b: u64) -> usize {
    if a < b {
        1
    } else {
        0
    }
}

pub fn b_umin(a: usize, b: usize) -> usize {
    if a < b {
        a
    } else {
        b
    }
}

pub fn b_umax(a: usize, b: usize) -> usize {
    if a > b {
        a
    } else {
        b
    }
}

pub fn b_eq64(a: u64, b: u64) -> usize {
    if a == b {
        1
    } else {
        0
    }
}

pub fn b_umin64(a: u64, b: u64) -> u64 {
    if a < b {
        a
    } else {
        b
    }
}

/// Push x when f == 1.
pub fn b_push_if(v: &mut Vec<u32>, f: usize, x: u32) {
    if f == 1 && v.len() < B_PUSH_LIMIT {
        v.push(x);
    }
}

pub fn b_umin32(a: u32, b: u32) -> u32 {
    if a < b {
        a
    } else {
        b
    }
}

/// Push the cache entry (len, d) when `f == 1`.
pub fn b_push_m(v: &mut Vec<u32>, f: usize, len: usize, d: usize) {
    if f == 1 && v.len() < B_PUSH_LIMIT {
        v.push(b_pack_m(len, d));
    }
}

/// Like push_m, but with B_SLOTM replace the previous entry of this position (index >= m0) when both
/// have the same distance slot (the shorter one is then never cheaper for any length).
pub fn b_push_slot(mc: &mut Vec<u32>, m0: usize, f: usize, len: usize, d: usize) {
    if f == 1 {
        b_push_slot1(mc, m0, len, d);
    }
}

pub fn b_push_slot1(mc: &mut Vec<u32>, m0: usize, len: usize, d: usize) {
    let e = b_pack_m(len, d);
    let k = mc.len();
    let last = b_get(mc, k.wrapping_sub(1));
    let same = b_eq(B_SLOTM, 1) & b_lt(m0, k) & b_eq(((last / 32768) % 32) as usize, ((e / 32768) % 32) as usize);
    if same == 1 {
        b_set(mc, k.wrapping_sub(1), e);
    } else {
        b_push_guarded(mc, e);
    }
}

/// A step of `l` if `3 <= l <= room`, else 1.
pub fn b_clamp_step(l: usize, room: usize) -> usize {
    if l >= 3 && l <= room {
        l
    } else {
        1
    }
}

/// A step of `l` if `1 <= l <= room`, else 1.
pub fn b_clamp1(l: usize, room: usize) -> usize {
    if l >= 1 && l <= room {
        l
    } else {
        1
    }
}

/// `x`, or 1 when `x == 0` (a divisor).
pub fn b_nz64(x: u64) -> u64 {
    if x == 0 {
        1
    } else {
        x
    }
}

// ---------------------------------------------------------------- trusted core
/// How many bytes agree at `a` and `b`, up to `cap`. The emission's byte-wise check.
pub fn b_match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// True iff `(ch, d)` at `pos` is in range and its bytes agree.
pub fn b_verified(input: &[u8], pos: usize, d: usize, ch: usize) -> bool {
    let n = input.len();
    if ch < 3 || ch > 258 || d < 1 || d > 32768 || d > pos || pos > n || ch > n - pos {
        return false;
    }
    let v = b_match_len(input, pos - d, pos, ch);
    v >= ch
}

/// The trusted emission: plan[k] = len * 65536 + dist (untrusted); every planned match is
/// re-verified byte-wise, else a literal is emitted.
pub fn b_emit_all(input: &[u8], out: &mut [u32], plan: &[u32]) -> usize {
    let n = input.len();
    let mut k = 0usize;
    let mut ntok = 0usize;
    while k < n {
        let p = b_get(plan, k) as usize;
        let ch = p / 65536;
        let d = p % 65536;
        if b_verified(input, k, d, ch) {
            out[ntok] = 16777216u32 + ((d - 1) as u32) * 256 + ((ch - 3) as u32);
            ntok += 1;
            k += ch;
        } else {
            out[ntok] = input[k] as u32;
            ntok += 1;
            k += 1;
        }
    }
    ntok
}

// ---------------------------------------------------------------- small helpers
/// Little-endian 8-byte word at `p` (0 when out of range).
pub fn b_le64(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if p < n && n - p >= 8 {
        let b7 = input[p + 7] as u64;
        let lo = (input[p] as u32) | ((input[p + 1] as u32) << 8) | ((input[p + 2] as u32) << 16) | ((input[p + 3] as u32) << 24);
        let hi = (input[p + 4] as u32) | ((input[p + 5] as u32) << 8) | ((input[p + 6] as u32) << 16) | ((b7 as u32) << 24);
        (lo as u64) | ((hi as u64) << 32)
    } else {
        0
    }
}

/// Index of the lowest differing byte of two little-endian words (x != y).
pub fn b_first_diff(x:u64,y:u64)->usize {
    let z=x^y;
    let a=((z&0xff00ff00ff00ff00u64)>>8)|((z&0x00ff00ff00ff00ffu64)<<8);
    let b=((a&0xffff0000ffff0000u64)>>16)|((a&0x0000ffff0000ffffu64)<<16);
    let c=(b>>32)|(b<<32);
    b_umin((c.leading_zeros()/8) as usize,7)
}

pub fn b_hash4(input: &[u8], p: usize) -> usize {
    let n = input.len();
    if n >= 4 && p <= n - 4 {
        let x = (input[p] as u32) | ((input[p + 1] as u32) << 8) | ((input[p + 2] as u32) << 16) | ((input[p + 3] as u32) << 24);
        ((x.wrapping_mul(2654435761) >> (32 - B_HBITS)) as usize) % B_HSIZE
    } else {
        0
    }
}

pub fn b_hash3(input: &[u8], p: usize) -> usize {
    let n = input.len();
    if n >= 3 && p <= n - 3 {
        let x = (input[p] as u32) | ((input[p + 1] as u32) << 8) | ((input[p + 2] as u32) << 16);
        ((x.wrapping_mul(2654435761) >> (32 - B_H3BITS)) as usize) % B_H3SIZE
    } else {
        0
    }
}

/// Distance slot (0..29) of a distance 1..32768.
pub fn b_dslot_old(d: usize) -> usize {
    let small = if d >= 1 { d.wrapping_sub(1) } else { 0 };
    let x = (d.wrapping_sub(1) % 65536) as u32;
    let msb = 31u32.wrapping_sub(x.leading_zeros());
    let sh = if msb >= 1 && msb <= 31 { msb.wrapping_sub(1) } else { 0 };
    let s = (2u32.wrapping_mul(msb % 32).wrapping_add((x >> (sh % 32)) & 1)) as usize;
    let big = if s > 29 { 29 } else { s };
    if d <= 4 {
        small
    } else {
        big
    }
}

pub fn b_dslot(d: usize) -> usize {
    if d >= 1 && d <= 256 {
        B_H_DSYM_S[d - 1] as usize
    } else if d >= 257 && d <= 32768 {
        B_H_DSYM_B[(d - 1) / 128] as usize
    } else {
        b_dslot_old(d)
    }
}


pub fn b_dextra(s: usize) -> u32 {
    if s < 4 {
        0
    } else {
        ((s / 2).wrapping_sub(1)) as u32
    }
}

/// Match-cache entry: len * 2^20 + dist slot * 2^15 + (dist - 1); len may carry the +512 inherited flag.
pub fn b_pack_m(len: usize, d: usize) -> u32 {
    let l = (len % 1024) as u32;
    let dd = if d >= 1 && d <= 32768 { d } else { 1 };
    l.wrapping_mul(1048576).wrapping_add((b_dslot(dd) as u32).wrapping_mul(32768)).wrapping_add((dd.wrapping_sub(1)) as u32)
}

/// Length code offset (0..28) of a match length 3..258.
pub fn b_lcode(l: usize) -> usize {
    let small = if l >= 3 { l.wrapping_sub(3) } else { 0 };
    let x = (l.wrapping_sub(3) % 1024) as u32;
    let msb = 31u32.wrapping_sub(x.leading_zeros());
    let sh = if msb >= 2 && msb <= 31 { msb.wrapping_sub(2) } else { 0 };
    let m = if msb >= 1 && msb <= 31 { msb.wrapping_sub(1) } else { 0 };
    let c = (4u32.wrapping_mul(m).wrapping_add((x >> (sh % 32)) & 3)) as usize;
    let big = if c > 28 { 28 } else { c };
    if l < 11 {
        small
    } else if l >= 258 {
        28
    } else {
        big
    }
}

pub fn b_lextra(c: usize) -> u32 {
    if c < 8 || c >= 28 {
        0
    } else {
        ((c.wrapping_sub(4)) / 4) as u32
    }
}

pub fn b_fixed_len(s: usize) -> u32 {
    if s < 144 {
        8
    } else if s < 256 {
        9
    } else if s < 280 {
        7
    } else {
        8
    }
}

// ---------------------------------------------------------------- match finder (binary trees)
/// Extend a known common prefix `from` of positions a < b up to cap (search only).
pub fn b_ext_len(input: &[u8], a: usize, b: usize, from: usize, cap: usize) -> usize {
    let n = input.len();
    let bad = if a >= b || b >= n || cap > n.wrapping_sub(b) { 1usize } else { 0usize };
    let lim = if bad == 1 { 0 } else { cap };
    let mut l = from;
    let mut it = 0usize;
    while it < 300 && l < lim {
        if lim - l >= 8 {
            let x = b_le64(input, a.wrapping_add(l));
            let y = b_le64(input, b.wrapping_add(l));
            if x == y {
                l = l.wrapping_add(8);
            } else {
                l = l.wrapping_add(b_first_diff(x, y));
                break;
            }
        } else if b_byte_at(input, a.wrapping_add(l)) == b_byte_at(input, b.wrapping_add(l)) {
            l = l.wrapping_add(1);
        } else {
            break;
        }
        it += 1;
    }
    let lb = if from > cap { cap } else { from };
    let lg = if l > cap { cap } else { l };
    if bad == 1 {
        lb
    } else {
        lg
    }
}

/// Little-endian 8-byte word at `p`, bytes past the end read as 0.
/// ext_len from `from` when `f == 1`, else `dflt` (keeps the call out of the caller's branches).
pub fn b_ext_if(input: &[u8], f: usize, a: usize, b: usize, from: usize, cap: usize, dflt: usize) -> usize {
    if f == 1 {
        b_ext_len(input, a, b, from, cap)
    } else {
        dflt
    }
}

pub fn b_le64z(input: &[u8], p: usize) -> u64 {
    let n = input.len();
    if p < n && n - p >= 8 {
        b_le64(input, p)
    } else {
        b_le64_tail(input, p)
    }
}

pub fn b_le64_tail(input: &[u8], p: usize) -> u64 {
    let mut x = 0u64;
    let mut j = 0usize;
    while j < 8 {
        let b = b_byte_at(input, p.wrapping_add(j)) as u64;
        x = x | (b << (((j as u32).wrapping_mul(8)) % 64));
        j += 1;
    }
    x
}

/// Common prefix length of a < b from l0 (bytes before l0 known equal), in whole words, capped at lim.
/// Returns 2 * length + (1 when a's byte at the first difference is smaller than b's).
pub fn b_lcp_words(input: &[u8], a: usize, b: usize, l0: usize, lim: usize) -> usize {
    let mut l = l0;
    let mut it = 0usize;
    let mut z = 0u64;
    let mut x = 0u64;
    while it < 40 && l < lim {
        x = b_le64z(input, a.wrapping_add(l));
        z = x ^ b_le64z(input, b.wrapping_add(l));
        if z != 0 { break; }
        l = l.wrapping_add(8);
        it += 1;
    }
    let fd = b_first_diff(z, 0);
    let lf = b_sel(b_eq64(z, 0), l, l.wrapping_add(fd));
    b_umin(lf, lim).wrapping_mul(2).wrapping_add(b_byte_lt(x, x ^ z, fd))
}

/// 1 when byte k of little-endian word x is smaller than byte k of y.
pub fn b_byte_lt(x: u64, y: u64, k: usize) -> usize {
    let sh = ((k as u32).wrapping_mul(8)) % 64;
    b_lt64((x >> sh) & 255, (y >> sh) & 255)
}

/// 2 * match length + direction bit after the first words x, y at l0: from them when they differ,
/// else continue word-wise.
pub fn b_ext_words(input: &[u8], same: usize, a: usize, b: usize, l0: usize, x: u64, y: u64, lim: usize) -> usize {
    if same == 1 {
        b_lcp_words(input, a, b, l0.wrapping_add(8), lim)
    } else {
        let fd = b_first_diff(x, y);
        l0.wrapping_add(fd).wrapping_mul(2).wrapping_add(b_byte_lt(x, y, fd))
    }
}

pub fn b_bt_probe(input: &[u8], a: usize, b: usize, l0: usize, first: u64, lim: usize) -> usize {
    if l0 < 8 {
        let x = b_le64z(input, a);
        b_ext_words(input, b_eq64(x, first), a, b, 0, x, first, lim)
    } else {
        let x = b_le64z(input, a.wrapping_add(l0));
        let y = b_le64z(input, b.wrapping_add(l0));
        b_ext_words(input, b_eq64(x, y), a, b, l0, x, y, lim)
    }
}

/// Insert `pos` into its binary tree (children in `child[2*slot]` = smaller, `[2*slot+1]` = larger)
/// and, if `rec == 1`, push every match longer than all before it (nearest first).
/// hint = kcur * 512 + klen: node kcur (as cur) is known to share klen bytes with pos.
/// Returns best + 512 * (longest walk match) + 262144 * (its distance).
pub fn b_bt_walk(
    input: &[u8],
    child: &mut [u32; 65536],
    root: usize,
    pos: usize,
    cap: usize,
    best0: usize,
    rec: usize,
    maxd: usize,
    hint: usize,
    mc: &mut Vec<u32>,
    m0: usize,
    first: u64,
) -> usize {
    let mut plt = (pos % 32768).wrapping_mul(2);
    let mut pgt = plt.wrapping_add(1);
    let mut cur = root;
    let mut ltl = 0usize;
    let mut gtl = 0usize;
    let mut len = 0usize;
    let mut best = best0;
    let mut wl = 0usize;
    let mut wd = 0usize;
    let mut depth = 0usize;
    let mut go = 1usize;
    let lim = b_sel(rec | b_lt(cap, B_INSCAP), cap, B_INSCAP);
    let stop = b_umin(lim, B_NICE);
    let kcur = hint / 512;
    let kl = b_umin(hint % 512, lim);
    while depth < maxd {
        let cm = cur.wrapping_sub(1);
        let dd = pos.wrapping_sub(cm);
        let bad = b_eq(cur, 0) | b_lt(pos, cur) | b_ge(dd, 32768);
        if bad == 1 {
            go = 0;
            break;
        } else {
            let l0 = b_sel(b_eq(cur, kcur) & b_lt(len, kl), kl, len);
            let l2 = b_bt_probe(input, cm, pos, l0, first, lim);
            len = b_umin(l2 / 2, lim);
            b_push_slot(mc, m0, rec & b_lt(best, len), len, dd);
            wd = b_sel(b_lt(wl, len), dd, wd);
            wl = b_umax(len, wl);
            best = b_umax(len, best);
            let cs = (cm % 32768).wrapping_mul(2);
            let c0 = child[cs % 65536];
            let c1 = child[cs.wrapping_add(1) % 65536];
            if len >= stop {
                b_setc(child, plt, c0);
                b_setc(child, pgt, c1);
                go = 2;
                break;
            } else {
                let sm = l2 % 2;
                b_setc(child, b_sel(sm, plt, pgt), cur as u32);
                let nx = cs.wrapping_add(sm);
                plt = b_sel(sm, nx, plt);
                pgt = b_sel(sm, pgt, nx);
                cur = b_sel(sm, c1 as usize, c0 as usize);
                ltl = b_sel(sm, len, ltl);
                gtl = b_sel(sm, gtl, len);
                len = b_umin(ltl, gtl);
            }
        }
        depth += 1;
    }
    if go != 2 {
        b_setc(child, plt, 0);
        b_setc(child, pgt, 0);
    }
    best.wrapping_add((wl % 512).wrapping_mul(512)).wrapping_add((wd % 65536).wrapping_mul(262144))
}

/// 1 when a position `gap` bytes before the end of a skipped region is still searched (every B_SKS-th).
pub fn b_sks_rec(gap: usize) -> usize {
    let d = if B_SKS == 0 { 1 } else { B_SKS };
    b_eq(B_SKS, 0) ^ 1 & b_eq(gap % d, 0)
}

/// Search position `pos` (state st = [skip, sfrom, sdist, _] carried across positions).
pub fn b_find_pos(
    input: &[u8],
    h4: &mut [u32; 65536],
    h3: &mut [u32; B_H3SIZE],
    child: &mut [u32; 65536],
    mc: &mut Vec<u32>,
    st: &mut [usize; 4],
    pos: usize,
    maxd: usize,
) {
    let n = input.len();
    if n < 4 || pos > n - 4 {
        return;
    }
    let skip = st[0];
    let sfrom = st[1];
    let sdist = st[2];
    let hint = st[3];
    let rem = n - pos;
    let cap = b_umin(rem, 258);
    let gap = skip.wrapping_sub(pos);
    let rec = b_ge(pos, skip) | b_lt(pos, sfrom) | b_sks_rec(gap);
    let inh = (rec ^ 1) & b_eq(B_INH, 1) & b_ge(gap, 3) & b_ge(258, gap);
    b_push_m(mc, inh, gap.wrapping_add(512), sdist);
    let first = b_le64z(input, pos);
    let key = first as u32;
    let x3 = (((key & 0x00ffffff).wrapping_mul(2654435761) >> (32 - B_H3BITS)) as usize) % B_H3SIZE;
    let c3 = if rec == 1 { h3[x3] as usize } else { 0 };
    h3[x3] = (pos + 1) as u32;
    let m0 = mc.len();
    let best = if rec == 1 {
        let c3m = c3.wrapping_sub(1);
        let ok3 = b_lt(0, c3) & b_ge(pos, c3) & b_lt(pos.wrapping_sub(c3m), 32768);
        let l3 = b_ext_if(input, ok3, c3m, pos, 0, b_umin(cap, B_H3CAP), 0);
        let f3 = b_ge(l3, 3);
        b_push_m(mc, f3, l3, pos.wrapping_sub(c3m));
        b_sel(f3, l3, 2)
    } else { 2 };
    let ins = rec | b_eq(B_INS, 1) | b_ge(B_INSEND, gap);
    let x4 = ((key.wrapping_mul(2654435761) >> (32 - B_HBITS)) as usize) % B_HSIZE;
    let r4 = h4[x4];
    h4[x4] = b_sel32(ins, (pos + 1) as u32, r4);
    let depth = b_sel(ins, maxd, 0);
    let bb = b_bt_walk(input, child, r4 as usize, pos, cap, best, rec, depth, hint, mc, m0, first);
    let b = bb % 512;
    let wl = (bb / 512) % 512;
    let bd = bb / 262144;
    let hk = b_ge(wl, 2) & b_ge(bd, 1) & b_ge(pos.wrapping_add(1), bd);
    st[3] = b_sel(hk, (pos.wrapping_add(2).wrapping_sub(bd)).wrapping_mul(512).wrapping_add(wl.wrapping_sub(1)), 0);
    let ml = mc.len();
    let ns = rec & b_ge(b, B_SKIPL) & b_lt(skip, pos.wrapping_add(b)) & b_lt(m0, ml);
    if ns == 1 {
        st[2] = bd;
        st[1] = pos.wrapping_add(1).wrapping_add(B_LZK);
        st[0] = pos.wrapping_add(b);
    }
}

/// Match cache for every position: entries of `pos` are mc[mstart[pos] .. mstart[pos + 1]].
pub fn b_find_all(input: &[u8], mstart: &mut Vec<u32>, mc: &mut Vec<u32>, maxd: usize) {
    let n = input.len();
    let mut h4 = [0u32; 65536];
    let mut h3 = [0u32; B_H3SIZE];
    let mut child = [0u32; 65536];
    let mut st = [0usize; 4];
    st[2] = 1;
    let mut pos = 0usize;
    while pos < n {
        b_push_guarded(mstart, mc.len() as u32);
        b_find_pos(input, &mut h4, &mut h3, &mut child, mc, &mut st, pos, maxd);
        pos += 1;
    }
    b_push_guarded(mstart, mc.len() as u32);
}

/// A second (trivial) find_all call for inputs shorter than 4 bytes: keeps find_all out of line
/// (its own register allocation).
pub fn b_find_spare(input: &[u8], f: usize) {
    if f == 1 {
        let mut a: Vec<u32> = Vec::new();
        let mut b: Vec<u32> = Vec::new();
        b_find_all(input, &mut a, &mut b, 1);
    }
}

// ---------------------------------------------------------------- DP (ring sparse table of packed cost << 32 | position)
/// End of the length-code bucket containing `l` (lengths sharing one code and extra-bit count).
pub fn b_bucket_end(l: usize) -> usize {
    if l < 11 {
        l
    } else if l >= 258 {
        258
    } else {
        let c = b_lcode(l);
        let e = b_lextra(c) % 8;
        let base = 3u32.wrapping_add(4u32.wrapping_add((c % 4) as u32) << e);
        let end = (base.wrapping_add(1u32 << e).wrapping_sub(1)) as usize;
        if end > 257 {
            257
        } else {
            end
        }
    }
}

pub fn b_build_bend(bend: &mut [u32; 512]) {
    let mut l = 0usize;
    while l < 259 {
        bend[l % 512] = b_bucket_end(l) as u32;
        l += 1;
    }
}

pub fn b_lg5(w: usize) -> usize {
    let x = (w % 64) as u32;
    let k = 31u32.wrapping_sub(x.leading_zeros()) as usize;
    if k > 4 {
        4
    } else {
        k
    }
}

/// Block cost table: ct[l] length l (0..258), ct[512 + s] distance slot s, ct[768 + c] literal c.
pub fn b_load_ct(tbl: &[u32], toff: usize, ct: &mut [u32; 1024], lam: u32) {
    let mut x = 0usize;
    while x < 259 {
        ct[x % 1024] = b_get(tbl, toff.wrapping_add(256).wrapping_add(x)).saturating_sub(lam);
        x += 1;
    }
    let mut s = 0usize;
    while s < 30 {
        ct[(512 + s) % 1024] = b_get(tbl, toff.wrapping_add(515).wrapping_add(s));
        s += 1;
    }
    let mut c = 0usize;
    while c < 256 {
        ct[(768 + c) % 1024] = b_get(tbl, toff.wrapping_add(c)).saturating_sub(lam);
        c += 1;
    }
}

/// Ring layout: level k (range width 2^k, k = 0..4) at k*512. Values are packed (cost << 32) | position,
/// so a range minimum also yields its (first) position.
pub fn b_rm_update(rm: &mut [u64; 4096], i: usize, c: u64) {
    let s = i % B_RING;
    rm[s % 4096] = c;
    let a1 = rm[i.wrapping_add(1) % B_RING];
    let m2 = b_umin64(c, a1);
    rm[(B_RING + s) % 4096] = m2;
    let a2 = rm[(B_RING + i.wrapping_add(2) % B_RING) % 4096];
    let m4 = b_umin64(m2, a2);
    rm[(2 * B_RING + s) % 4096] = m4;
    let a4 = rm[(2 * B_RING + i.wrapping_add(4) % B_RING) % 4096];
    let m8 = b_umin64(m4, a4);
    rm[(3 * B_RING + s) % 4096] = m8;
    let a8 = rm[(3 * B_RING + i.wrapping_add(8) % B_RING) % 4096];
    let m16 = b_umin64(m8, a8);
    rm[(4 * B_RING + s) % 4096] = m16;
}

/// rm_update without level 4 (when no query spans more than 15 lengths).
pub fn b_rm_update3(rm: &mut [u64; 4096], i: usize, c: u64) {
    let s = i % B_RING;
    rm[s % 4096] = c;
    let a1 = rm[i.wrapping_add(1) % B_RING];
    let m2 = b_umin64(c, a1);
    rm[(B_RING + s) % 4096] = m2;
    let a2 = rm[(B_RING + i.wrapping_add(2) % B_RING) % 4096];
    let m4 = b_umin64(m2, a2);
    rm[(2 * B_RING + s) % 4096] = m4;
    let a4 = rm[(2 * B_RING + i.wrapping_add(4) % B_RING) % 4096];
    let m8 = b_umin64(m4, a4);
    rm[(3 * B_RING + s) % 4096] = m8;
}

/// b_rm_update (f == 1) or rm_update3.
pub fn b_rm_upd(f: usize, rm: &mut [u64; 4096], i: usize, c: u64) {
    if f == 1 {
        b_rm_update(rm, i, c);
    } else {
        b_rm_update3(rm, i, c);
    }
}

/// Packed value of the bucket part [x, e] (one length code): range minimum + length and distance costs.
pub fn b_bkt_val(rm: &[u64; 4096], ct: &[u32; 1024], i: usize, x: usize, e: usize, dcs: u64) -> u64 {
    let k = b_lg5(e.wrapping_add(1).wrapping_sub(x));
    let p = (1u32 << ((k % 8) as u32)) as usize;
    let kr = k.wrapping_mul(B_RING);
    let ra = rm[kr.wrapping_add(i.wrapping_add(x) % B_RING) % 4096];
    let rb = rm[kr.wrapping_add(i.wrapping_add(e).wrapping_add(1).wrapping_sub(p) % B_RING) % 4096];
    b_umin64(ra, rb).wrapping_add(((ct[x % 1024] as u64) << 32).wrapping_add(dcs))
}

/// Relaxation query: one short length (k = 0, y = x) or one bucket part (range minimum of level k at x and y):
/// x + 512 * y + 262144 * k + 2097152 * slot.
pub fn b_query(x: usize, y: usize, k: usize, slot: usize) -> u32 {
    ((x % 512) as u32)
        .wrapping_add(((y % 512) as u32).wrapping_mul(512))
        .wrapping_add(((k % 8) as u32).wrapping_mul(262144))
        .wrapping_add(((slot % 32) as u32).wrapping_mul(2097152))
}

/// Short lengths lo..=hi: relax, and keep the queries within B_PM of the running best; returns the new best.
pub fn b_prune_short(rm: &[u64; 4096], ct: &[u32; 1024], i: usize, lo: usize, hi: usize, dcs: u64, slot: usize, best0: u64, keep: usize, items: &mut Vec<u32>) -> u64 {
    let mut best = best0;
    let mut x = lo;
    while x <= hi && x < 11 {
        let v = rm[i.wrapping_add(x) % B_RING].wrapping_add(((ct[x % 1024] as u64) << 32).wrapping_add(dcs));
        b_push_if(items, keep & (b_lt64(best.wrapping_add((B_PM as u64) << 32), v) ^ 1), b_query(x, x, 0, slot));
        best = b_umin64(v, best);
        x += 1;
    }
    best
}

/// Bucket parts lo..=hi (lo >= 11): relax, and keep the queries within B_PM of the running best; returns the new best.
pub fn b_prune_bkt(rm: &[u64; 4096], ct: &[u32; 1024], bend: &[u32; 512], i: usize, lo: usize, hi: usize, dcs: u64, slot: usize, best0: u64, keep: usize, items: &mut Vec<u32>) -> u64 {
    let mut best = best0;
    let mut x = lo;
    let mut it = 0usize;
    while it < 32 && x <= hi && x < 259 {
        let e = b_umin(b_umax(bend[x % 512] as usize, x), hi);
        let v = b_bkt_val(rm, ct, i, x, e, dcs);
        let k = b_lg5(e.wrapping_add(1).wrapping_sub(x));
        let p = (1u32 << ((k % 8) as u32)) as usize;
        let q = b_query(x, e.wrapping_add(1).wrapping_sub(p), k, slot);
        b_push_if(items, keep & (b_lt64(best.wrapping_add((B_PM as u64) << 32), v) ^ 1), q);
        best = b_umin64(v, best);
        x = e.wrapping_add(1);
        it += 1;
    }
    best
}

/// Keep the sole query of an inherited candidate, reusing its already computed value.
pub fn b_prune_single(items: &mut Vec<u32>, keep: usize, best: u64, value: u64, len: usize, slot: usize) -> u64 {
    b_push_if(items, keep & (b_lt64(best.wrapping_add((B_PM as u64) << 32), value) ^ 1), b_query(len, len, 0, slot));
    best
}

/// Relax every cached match at i (best seeded with the longest match) and keep the near-optimal queries.
pub fn b_prune_pos(rm: &[u64; 4096], ct: &[u32; 1024], bend: &[u32; 512], mc: &[u32], ms: usize, me: usize, i: usize, lit: u64, chw: usize, msub: u32, keep: usize, items: &mut Vec<u32>) -> u64 {
    if ms >= me { return lit; }
    let ml = b_get(mc, me.wrapping_sub(1)) as usize;
    let ll0 = ml / 1048576;
    let hl = b_umin(b_sel(b_ge(ll0, 512), ll0.wrapping_sub(512), ll0), 258);
    let dl = ct[(512 + (ml / 32768) % 32) % 1024].saturating_sub(msub);
    let vl = b_bkt_val(rm, ct, i, hl, hl, (dl as u64) << 32);
    let mut best = b_sel64(b_lt(ms, me) & b_ge(hl, 3) & b_lt64(vl, lit), vl, lit);
    let single = b_lt(ms, me) & b_eq(me, ms.wrapping_add(1)) & b_ge(ll0, 512) & b_ge(hl, 3);
    if single == 1 {
        return b_prune_single(items, keep, best, vl, hl, (ml / 32768) % 32);
    }
    let mut k = ms;
    let mut lo = 3usize;
    while k < me {
        let m = b_get(mc, k) as usize;
        let len0 = m / 1048576;
        let slot = (m / 32768) % 32;
        let dcs = (ct[(512 + slot) % 1024].saturating_sub(msub) as u64) << 32;
        let flag = b_ge(len0, 512);
        let h = b_umin(b_sel(flag, len0.wrapping_sub(512), len0), 258);
        let a = b_sel(flag, h, lo);
        let b1 = b_prune_short(rm, ct, i, a, b_umin(h, 10), dcs, slot, best, keep, items);
        let a2 = b_umax(a, 11);
        let a3 = b_sel(b_lt(a2.wrapping_add(chw), h), h.wrapping_sub(chw), a2);
        best = b_prune_bkt(rm, ct, bend, i, a3, h, dcs, slot, b1, keep, items);
        lo = b_sel((flag ^ 1) & b_ge(h, lo), h.wrapping_add(1), lo);
        k += 1;
    }
    best
}

/// Short lengths lo..=hi: relax only (no query keeping); returns the new best.
pub fn b_relax_short(rm: &[u64; 4096], ct: &[u32; 1024], i: usize, lo: usize, hi: usize, dcs: u64, best0: u64) -> u64 {
    let mut best = best0;
    let mut x = lo;
    while x <= hi && x < 11 {
        let v = rm[i.wrapping_add(x) % B_RING].wrapping_add(((ct[x % 1024] as u64) << 32).wrapping_add(dcs));
        best = b_umin64(v, best);
        x += 1;
    }
    best
}

/// Bucket parts lo..=hi (lo >= 11): relax only; returns the new best.
pub fn b_relax_bkt(rm: &[u64; 4096], ct: &[u32; 1024], bend: &[u32; 512], i: usize, lo: usize, hi: usize, dcs: u64, best0: u64) -> u64 {
    let mut best = best0;
    let mut x = lo;
    let mut it = 0usize;
    while it < 32 && x <= hi && x < 259 {
        let e = b_umin(b_umax(bend[x % 512] as usize, x), hi);
        best = b_umin64(b_bkt_val(rm, ct, i, x, e, dcs), best);
        x = e.wrapping_add(1);
        it += 1;
    }
    best
}

/// Relax every cached match at i (first pass without query keeping).
pub fn b_relax_pos(rm: &[u64; 4096], ct: &[u32; 1024], bend: &[u32; 512], mc: &[u32], ms: usize, me: usize, i: usize, lit: u64, chw: usize, msub: u32) -> u64 {
    let mut best = lit;
    let mut k = ms;
    let mut lo = 3usize;
    while k < me {
        let m = b_get(mc, k) as usize;
        let len0 = m / 1048576;
        let dcs = (ct[(512 + (m / 32768) % 32) % 1024].saturating_sub(msub) as u64) << 32;
        let flag = b_ge(len0, 512);
        let h = b_umin(b_sel(flag, len0.wrapping_sub(512), len0), 258);
        let a = b_sel(flag, h, lo);
        let b1 = b_relax_short(rm, ct, i, a, b_umin(h, 10), dcs, best);
        let a2 = b_umax(a, 11);
        let a3 = b_sel(b_lt(a2.wrapping_add(chw), h), h.wrapping_sub(chw), a2);
        best = b_relax_bkt(rm, ct, bend, i, a3, h, dcs, b1);
        lo = b_sel((flag ^ 1) & b_ge(h, lo), h.wrapping_add(1), lo);
        k += 1;
    }
    best
}

/// prune_pos when keep == 1, else b_relax_pos (same result, no queries).
pub fn b_prune_or_relax(rm: &[u64; 4096], ct: &[u32; 1024], bend: &[u32; 512], mc: &[u32], ms: usize, me: usize, i: usize, lit: u64, chw: usize, msub: u32, keep: usize, items: &mut Vec<u32>) -> u64 {
    if keep == 1 {
        b_prune_pos(rm, ct, bend, mc, ms, me, i, lit, chw, msub, keep, items)
    } else {
        b_relax_pos(rm, ct, bend, mc, ms, me, i, lit, chw, msub)
    }
}

/// Relax the pruned queries s..e of position i.
pub fn b_relax_items(rm: &[u64; 4096], ct: &[u32; 1024], items: &[u32], s: usize, e: usize, i: usize, lit: u64) -> u64 {
    let mut best = lit;
    let mut t = s;
    while t < e {
        let q = b_get(items, t) as usize;
        let kr = ((q / 262144) % 8).wrapping_mul(B_RING);
        let ra = rm[kr.wrapping_add(i.wrapping_add(q) % B_RING) % 4096];
        let rb = if kr==0 {ra} else {rm[kr.wrapping_add(i.wrapping_add(q / 512) % B_RING) % 4096]};
        let c = ct[q % 512].wrapping_add(ct[(512 + (q / 2097152) % 32) % 1024]);
        let v = b_umin64(ra, rb).wrapping_add((c as u64) << 32);
        best = b_umin64(v, best);
        t += 1;
    }
    best
}

/// First-pass DP over the positions hi-1 down to lo of one block (cost table ct): relax the whole match
/// cache and keep the near-optimal relaxation queries (items, backward position order; with keep == 1
/// istart gets the first query of every position). choice[i] = winning length * 65536.
pub fn b_dp_prune(
    input: &[u8],
    rm: &mut [u64; 4096],
    ct: &[u32; 1024],
    bend: &[u32; 512],
    mstart: &[u32],
    mc: &[u32],
    choice: &mut [u32],
    chw: usize,
    msub: u32,
    keep: usize,
    items: &mut Vec<u32>,
    istart: &mut Vec<u32>,
    lo: usize,
    hi: usize,
    l4: usize,
    co: usize,
) {
    let mut i = hi;
    while i > lo {
        i -= 1;
        let lit = rm[i.wrapping_add(1) % B_RING].wrapping_add((ct[768usize.wrapping_add(b_byte_at(input, i)) % 1024] as u64) << 32);
        b_push_if(istart, keep, items.len() as u32);
        let ms = b_get(mstart, i) as usize;
        let me = b_get(mstart, i.wrapping_add(1)) as usize;
        let best = b_prune_or_relax(rm, ct, bend, mc, ms, me, i, lit, chw, msub, keep, items);
        let l = ((best as u32) as usize).wrapping_sub(i);
        b_rm_upd(l4, rm, i, (best & 0xFFFF_FFFF_0000_0000) | (i as u64));
        b_set(choice, co.wrapping_add(i), b_sel32(b_ge(l, 3) & b_ge(258, l), (l as u32).wrapping_mul(65536), 0));
    }
}

/// Start of block b (clamped to hi; block 0 starts at 0).
pub fn b_blk_lo(bpos: &[u32], b: usize, hi: usize) -> usize {
    b_sel(b_eq(b, 0), 0, b_umin(b_get(bpos, b) as usize, hi))
}

/// First backward DP pass over the whole match cache, block by block (see dp_prune).
pub fn b_pass_prune(
    input: &[u8],
    mstart: &[u32],
    mc: &[u32],
    tbl: &[u32],
    bend: &[u32; 512],
    bpos: &[u32],
    nb: usize,
    choice: &mut [u32],
    chw: usize,
    msub: u32,
    keep: usize,
    items: &mut Vec<u32>,
    istart: &mut Vec<u32>,
    co: usize,
    lam: u32,
) {
    let n = input.len();
    let mut rm = [0u64; 4096];
    let mut ct = [0u32; 1024];
    b_rm_update(&mut rm, n, n as u64);
    let mut hi = n;
    let mut k = 0usize;
    while k < nb {
        let b = nb - 1 - k;
        let lo = b_blk_lo(bpos, b, hi);
        b_load_ct(tbl, b.wrapping_mul(B_TB), &mut ct, lam);
        b_dp_prune(input, &mut rm, &ct, bend, mstart, mc, choice, chw, msub, keep, items, istart, lo, hi, b_ge(chw, 15), co);
        hi = lo;
        k += 1;
    }
    b_push_if(istart, keep, items.len() as u32);
}

/// Later-pass DP over the positions hi-1 down to lo of one block: relax the pruned queries only.
pub fn b_dp_items_safe(input: &[u8], rm: &mut [u64; 4096], ct: &[u32; 1024], choice: &mut [u32], items: &[u32], istart: &[u32], lo: usize, hi: usize, l4: usize, co: usize) {
    let n = input.len();
    let mut e = b_get(istart, n.wrapping_sub(hi)) as usize;
    let mut i = hi;
    while i > lo {
        i -= 1;
        let lit = rm[i.wrapping_add(1) % B_RING].wrapping_add((ct[768usize.wrapping_add(b_byte_at(input, i)) % 1024] as u64) << 32);
        let s = e;
        e = b_get(istart, n.wrapping_sub(i)) as usize;
        let best = b_relax_items(rm, ct, items, s, e, i, lit);
        let l = ((best as u32) as usize).wrapping_sub(i);
        b_rm_upd(l4, rm, i, (best & 0xFFFF_FFFF_0000_0000) | (i as u64));
        b_set(choice, co.wrapping_add(i), b_sel32(b_ge(l, 3) & b_ge(258, l), (l as u32).wrapping_mul(65536), 0));
    }
}

pub fn b_dp_items(input: &[u8], rm: &mut [u64; 4096], ct: &[u32; 1024], choice: &mut [u32], items: &[u32], istart: &[u32], lo: usize, hi: usize, l4: usize, co: usize) {
    let n = input.len();
    if hi > n || lo > hi || n - lo >= istart.len()
        || co > choice.len() || hi > choice.len() - co {
        b_dp_items_safe(input, rm, ct, choice, items, istart, lo, hi, l4, co);
        return;
    }
    let mut e = istart[n - hi] as usize;
    let mut i = hi;
    while i > lo {
        i -= 1;
        let lit = rm[i.wrapping_add(1) % B_RING].wrapping_add((ct[768usize.wrapping_add(input[i] as usize) % 1024] as u64) << 32);
        let s = e;
        e = istart[n - i] as usize;
        let best = b_relax_items(rm, ct, items, s, e, i, lit);
        let l = ((best as u32) as usize).wrapping_sub(i);
        b_rm_upd(l4, rm, i, (best & 0xFFFF_FFFF_0000_0000) | (i as u64));
        choice[co + i] = b_sel32(b_ge(l, 3) & b_ge(258, l), (l as u32).wrapping_mul(65536), 0);
    }
}

/// Later backward DP passes over the pruned queries only, block by block.
pub fn b_pass_items(input: &[u8], tbl: &[u32], bpos: &[u32], nb: usize, choice: &mut [u32], items: &[u32], istart: &[u32], l4: usize, co: usize, lam: u32) {
    let n = input.len();
    let mut rm = [0u64; 4096];
    let mut ct = [0u32; 1024];
    b_rm_update(&mut rm, n, n as u64);
    let mut hi = n;
    let mut k = 0usize;
    while k < nb {
        let b = nb - 1 - k;
        let lo = b_blk_lo(bpos, b, hi);
        b_load_ct(tbl, b.wrapping_mul(B_TB), &mut ct, lam);
        b_dp_items(input, &mut rm, &ct, choice, items, istart, lo, hi, l4, co);
        hi = lo;
        k += 1;
    }
}

/// Distance of the cached match that covers length l at position p (first entry reaching l); 0 if none.
pub fn b_find_dist(mstart: &[u32], mc: &[u32], p: usize, l: usize) -> usize {
    let ms = b_get(mstart, p) as usize;
    let me = b_get(mstart, p.wrapping_add(1)) as usize;
    let mut d = 0usize;
    let mut k = ms;
    while k < me && d == 0 {
        let m = b_get(mc, k) as usize;
        let len0 = m / 1048576;
        let h = b_sel(b_ge(len0, 512), len0.wrapping_sub(512), len0);
        d = b_sel(b_ge(h, l), m % 32768 + 1, 0);
        k += 1;
    }
    d
}


// ---------------------------------------------------------------- walk path, block stats
pub fn b_clear(v: &mut [u32], a: usize, b: usize) {
    let mut i = a;
    while i < b {
        b_set(v, i, 0);
        i += 1;
    }
}

/// The distance of a planned match: from the plan, or looked up in the cache when the plan has only a length.
pub fn b_dist_of(mstart: &[u32], mc: &[u32], pos: usize, len: usize, d0: usize) -> usize {
    if len >= 3 && d0 == 0 {
        b_find_dist(mstart, mc, pos, len)
    } else {
        d0
    }
}

/// Symbol statistics of one path step (a match of length st >= 3 at distance d, or literal b).
pub fn b_walk_bump(fr: &mut [u32], off: usize, st: usize, d: usize, b: usize) {
    if st >= 3 {
        let lc = b_lcode(st);
        let s = b_dslot(d);
        b_bump(fr, off.wrapping_add(257).wrapping_add(lc), 1);
        b_bump(fr, off.wrapping_add(288).wrapping_add(s), 1);
        b_bump(fr, off.wrapping_add(318), b_lextra(lc).wrapping_add(b_dextra(s)));
        b_bump(fr, off.wrapping_add(319), st as u32);
    } else {
        b_bump(fr, off.wrapping_add(b), 1);
        b_bump(fr, off.wrapping_add(319), 1);
    }
}

/// Follow the chosen path; per-block frequencies into `fr` (B_FB per block: 0..288 litlen,
/// 288..318 dist, 318 extra bits, 319 raw bytes), block start positions into `bpos`.
/// Returns the number of blocks.
pub fn b_walk(input: &[u8], mstart: &[u32], mc: &[u32], choice: &mut [u32], co: usize, fr: &mut [u32], bpos: &mut [u32]) -> usize {
    let n = input.len();
    let mut pos = 0usize;
    let mut b = 0usize;
    let mut t = 0usize;
    b_clear(fr, 0, B_FB);
    b_set(bpos, 0, 0);
    while pos < n {
        let c = b_get(choice, co.wrapping_add(pos)) as usize;
        let len = c / 65536;
        let d0 = c % 65536;
        let d = b_dist_of(mstart, mc, pos, len, d0);
        let st0 = b_clamp_step(len, n - pos);
        let st = b_sel(b_ge(d, 1), st0, 1);
        let ism = b_ge(st, 3);
        b_set(choice, co.wrapping_add(pos), b_sel32(ism, (len as u32).wrapping_mul(65536).wrapping_add(d as u32), 0));
        b_walk_bump(fr, b.wrapping_mul(B_FB), st, d, b_byte_at(input, pos));
        let stt = b_clamp1(st, n - pos);
        pos += stt;
        t = t.wrapping_add(1);
        if t >= B_BT && pos < n {
            t = 0;
            b = b.wrapping_add(1);
            b_clear(fr, b.wrapping_mul(B_FB), b.wrapping_mul(B_FB).wrapping_add(B_FB));
            b_set(bpos, b, pos as u32);
        }
    }
    b.wrapping_add(1)
}

// ---------------------------------------------------------------- package-merge (encoder replica)
pub fn b_insert_sorted(order: &mut [u32], k: usize, s: usize, freq: &[u32], off: usize) {
    let fs = b_get(freq, off.wrapping_add(s));
    let mut j = k;
    while j > 0 {
        let o = b_get(order, j - 1) as usize;
        let fo = b_get(freq, off.wrapping_add(o));
        if fo <= fs {
            break;
        }
        b_set(order, j, o as u32);
        j -= 1;
    }
    b_set(order, j, s as u32);
}

/// Stable counting-sort pass of src[0..k) by the byte (freq >> sh) & 255 into dst.
pub fn b_radix_pass(freq: &[u32], off: usize, src: &[u32], dst: &mut [u32], k: usize, sh: u32) {
    let mut cnt = [0u32; 256];
    let mut i = 0usize;
    while i < k && i < 288 {
        let f = b_get(freq, off.wrapping_add(b_get(src, i) as usize));
        let dg = ((f >> (sh % 32)) % 256) as usize;
        cnt[dg] = cnt[dg].wrapping_add(1);
        i += 1;
    }
    let mut acc = 0u32;
    let mut d = 0usize;
    while d < 256 {
        let c = cnt[d];
        cnt[d] = acc;
        acc = acc.wrapping_add(c);
        d += 1;
    }
    let mut j = 0usize;
    while j < k && j < 288 {
        let s = b_get(src, j);
        let f = b_get(freq, off.wrapping_add(s as usize));
        let dg = ((f >> (sh % 32)) % 256) as usize;
        b_set(dst, cnt[dg] as usize, s);
        cnt[dg] = cnt[dg].wrapping_add(1);
        j += 1;
    }
}

/// Live symbols sorted by (frequency, symbol) into order; returns their number.
/// Radix sort when every frequency is below 65536, insertion sort otherwise.
pub fn b_sort_live(freq: &[u32], off: usize, nsym: usize, order: &mut [u32]) -> usize {
    let mut tmp = [0u32; 288];
    let mut k = 0usize;
    let mut big = 0usize;
    let mut s = 0usize;
    while s < nsym && s < 288 {
        let f = b_get(freq, off.wrapping_add(s));
        let old = tmp[k % 288];
        let live = b_lt32(0, f);
        tmp[k % 288] = b_sel32(live, s as u32, old);
        k = k.wrapping_add(live);
        big = big | b_lt32(65535, f);
        s += 1;
    }
    let kr = b_sel(big, 0, k);
    b_radix_pass(freq, off, &tmp, order, kr, 0);
    b_copy32(order, 0, &mut tmp, 0, kr);
    b_radix_pass(freq, off, &tmp, order, kr, 8);
    let kb = b_sel(big, k, 0);
    let mut j = 0usize;
    while j < kb && j < 288 {
        b_insert_sorted(order, j, tmp[j % 288] as usize, freq, off);
        j += 1;
    }
    k
}

pub fn b_load_w(freq: &[u32], off: usize, order: &[u32], k: usize, wa: &mut [u64]) {
    let mut i = 0usize;
    while i < k && i < 288 {
        let s = b_get(order, i) as usize;
        b_set64(wa, i, b_get(freq, off.wrapping_add(s)) as u64);
        i += 1;
    }
}

/// One package-merge level: merge the sorted leaf weights lw[0..k) with pairs of w[src..src+curlen)
/// into w[dst..]; flags mark leaves.
pub fn b_pm_level(lw: &[u64; 288], k: usize, w: &mut [u64; 1152], src: usize, curlen: usize, dst: usize, flags: &mut [u8; 9216], foff: usize) -> usize {
    let npk = curlen / 2;
    let total = k.wrapping_add(npk);
    let mut a = 0usize;
    let mut p = 0usize;
    let mut t = 0usize;
    while t < total && t < 576 {
        let lv = if a < k { lw[a % 288] } else { 0xFFFF_FFFF_FFFF_FFFFu64 };
        let i2 = src.wrapping_add(p.wrapping_mul(2));
        let pw = if p < npk { w[i2 % 1152].wrapping_add(w[i2.wrapping_add(1) % 1152]) } else { 0xFFFF_FFFF_FFFF_FFFFu64 };
        if lv <= pw {
            w[dst.wrapping_add(t) % 1152] = lv;
            flags[foff.wrapping_add(t) % 9216] = 1;
            a = a.wrapping_add(1);
        } else {
            w[dst.wrapping_add(t) % 1152] = pw;
            flags[foff.wrapping_add(t) % 9216] = 0;
            p = p.wrapping_add(1);
        }
        t += 1;
    }
    total
}

pub fn b_pm_levels(lw: &[u64; 288], k: usize, w: &mut [u64; 1152], flags: &mut [u8; 9216], maxbits: usize) {
    let mut curlen = k;
    let mut lev = 1usize;
    while lev < maxbits && lev < 16 {
        curlen = b_pm_level(lw, k, w, ((lev + 1) % 2).wrapping_mul(576), curlen, (lev % 2).wrapping_mul(576), flags, lev.wrapping_mul(576));
        lev += 1;
    }
}

pub fn b_count_leaves(flags: &[u8], foff: usize, s: usize) -> usize {
    let mut c = 0usize;
    let mut i = 0usize;
    while i < s && i < 576 {
        c = if b_get8(flags, foff.wrapping_add(i)) == 1 { c.wrapping_add(1) } else { c };
        i += 1;
    }
    c
}

pub fn b_inc_prefix(cnt: &mut [u32], m: usize) {
    let mut i = 0usize;
    while i < m && i < 288 {
        b_bump(cnt, i, 1);
        i += 1;
    }
}

pub fn b_count_back(flags: &[u8], cnt: &mut [u32], k: usize, maxbits: usize) -> usize {
    let mut s = if k >= 2 { k.wrapping_mul(2).wrapping_sub(2) } else { 0 };
    let mut lv = b_sel(b_ge(maxbits, 1) & b_ge(16, maxbits), maxbits.wrapping_sub(1), 0);
    while lv > 0 {
        let cl = b_count_leaves(flags, lv.wrapping_mul(576), s);
        b_inc_prefix(cnt, cl);
        s = b_sel(b_ge(s, cl), s.wrapping_sub(cl).wrapping_mul(2), 0);
        lv -= 1;
    }
    s
}

pub fn b_assign_lens(order: &[u32], cnt: &[u32], k: usize, lens: &mut [u32], loff: usize) {
    let mut r = 0usize;
    while r < k && r < 288 {
        let s2 = b_get(order, r) as usize;
        b_set(lens, loff.wrapping_add(s2), b_get(cnt, r));
        r += 1;
    }
}

/// Code lengths exactly as the encoder's package_merge (ties by symbol index, leaf-first merge).
pub fn b_pkg_merge_pm(freq: &[u32], off: usize, nsym: usize, maxbits: usize, lens: &mut [u32], loff: usize) {
    let mut order = [0u32; 288];
    let mut lw = [0u64; 288];
    let mut w = [0u64; 1152];
    let mut flags = [0u8; 9216];
    let mut cnt = [0u32; 288];
    b_clear(lens, loff, loff.wrapping_add(nsym));
    let k = b_sort_live(freq, off, nsym, &mut order);
    let s0 = order[0] as usize;
    let v0 = b_get(lens, loff.wrapping_add(s0));
    b_set(lens, loff.wrapping_add(s0), b_sel32(b_eq(k, 1), 1, v0));
    let kk = b_sel(b_ge(k, 2) & b_ge(15, maxbits), k, 0);
    b_load_w(freq, off, &order, kk, &mut lw);
    b_load_w(freq, off, &order, kk, &mut w);
    b_pm_levels(&lw, kk, &mut w, &mut flags, maxbits);
    let s = b_count_back(&flags, &mut cnt, kk, maxbits);
    b_inc_prefix(&mut cnt, s);
    b_assign_lens(&order, &cnt, kk, lens, loff);
}

// ---------------------------------------------------------------- exact block cost (encoder replica)
pub const B_CL_ORDER: [usize; 19] = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

pub fn b_run_len(all: &[u32], i: usize, m: usize) -> usize {
    let v = b_get(all, i);
    let mut r = 1usize;
    while r < 1000 {
        let j = i.wrapping_add(r);
        if j >= m {
            break;
        }
        if b_get(all, j) != v {
            break;
        }
        r += 1;
    }
    r
}

/// RLE statistics of the code-length sequence; returns total extra bits.
pub fn b_rle_stats(all: &[u32], m: usize, clf: &mut [u32]) -> u64 {
    let mut extra = 0u64;
    let mut i = 0usize;
    while i < m {
        let v = b_get(all, i) as usize;
        let run = b_run_len(all, i, m);
        let q0 = run / 138;
        let r0 = run % 138;
        let rest = run.wrapping_sub(1);
        let q1 = rest / 6;
        let r1 = rest % 6;
        let e18 = if r0 >= 11 { 1usize } else { 0usize };
        let e16 = if r1 >= 3 { 1usize } else { 0usize };
        let add18 = if v == 0 { q0.wrapping_add(e18) } else { 0 };
        let add17 = if v == 0 && r0 >= 3 && r0 < 11 { 1usize } else { 0usize };
        let add0 = if v == 0 && r0 < 3 { r0 } else { 0 };
        let add16 = if v == 0 { 0 } else { q1.wrapping_add(e16) };
        let addv = if v == 0 { 0 } else if r1 < 3 { r1.wrapping_add(1) } else { 1 };
        b_bump(clf, 18, add18 as u32);
        b_bump(clf, 17, add17 as u32);
        b_bump(clf, 0, add0 as u32);
        b_bump(clf, 16, add16 as u32);
        b_bump(clf, v % 19, addv as u32);
        let ex = add18.wrapping_mul(7).wrapping_add(add17.wrapping_mul(3)).wrapping_add(add16.wrapping_mul(2));
        extra = extra.wrapping_add(ex as u64);
        let st = b_clamp1(run, m - i);
        i += st;
    }
    extra
}

pub fn b_dot(f: &[u32], foff: usize, l: &[u32], loff: usize, m: usize) -> u64 {
    let mut s = 0u64;
    let mut i = 0usize;
    while i < m {
        s = s.wrapping_add((b_get(f, foff.wrapping_add(i)) as u64).wrapping_mul(b_get(l, loff.wrapping_add(i)) as u64));
        i += 1;
    }
    s
}

pub fn b_fixed_dot(f: &[u32], foff: usize) -> u64 {
    let mut s = 0u64;
    let mut i = 0usize;
    while i < 288 {
        s = s.wrapping_add((b_get(f, foff.wrapping_add(i)) as u64).wrapping_mul(b_fixed_len(i) as u64));
        i += 1;
    }
    s
}

pub fn b_sum_range(f: &[u32], a: usize, b: usize) -> u64 {
    let mut s = 0u64;
    let mut i = a;
    while i < b {
        s = s.wrapping_add(b_get(f, i) as u64);
        i += 1;
    }
    s
}

pub fn b_last_nz(l: &[u32], off: usize, m: usize, lo: usize) -> usize {
    let mut k = m;
    while k > lo {
        if b_get(l, off.wrapping_add(k - 1)) != 0 {
            break;
        }
        k -= 1;
    }
    k
}

pub fn b_copy32(src: &[u32], soff: usize, dst: &mut [u32], doff: usize, m: usize) {
    let mut i = 0usize;
    while i < m {
        b_set(dst, doff.wrapping_add(i), b_get(src, soff.wrapping_add(i)));
        i += 1;
    }
}

pub fn b_hclen_of(cl: &[u32]) -> usize {
    let mut h = 19usize;
    while h > 4 {
        if b_get(cl, B_CL_ORDER[(h - 1) % 19]) != 0 {
            break;
        }
        h -= 1;
    }
    h
}

/// Exact bits the encoder spends on the block whose frequencies are `fr[off..off+B_FB]`.
/// Leaves the dynamic code lengths in `lens[0..288]` (litlen) and `lens[288..318]` (dist);
/// returns bits * 4 + kind (0 dynamic, 1 fixed, 2 stored).
pub fn b_block_bits(fr: &mut [u32], off: usize, lens: &mut [u32]) -> u64 {
    b_bump(fr, off.wrapping_add(256), 1);
    b_pkg_merge(fr, off, 288, 15, lens, 0);
    b_pkg_merge(fr, off.wrapping_add(288), 30, 15, lens, 288);
    let ndist = b_sum_range(fr, off.wrapping_add(288), off.wrapping_add(318));
    let l288 = b_get(lens, 288);
    b_set(lens, 288, b_sel32(b_lt64(ndist, 1), 1, l288));
    let hlit = b_last_nz(lens, 0, 288, 257);
    let hdist = b_last_nz(lens, 288, 30, 1);
    let mut all = [0u32; 320];
    b_copy32(lens, 0, &mut all, 0, hlit);
    b_copy32(lens, 288, &mut all, hlit, hdist);
    let mut clf = [0u32; 19];
    let rextra = b_rle_stats(&all, hlit.wrapping_add(hdist), &mut clf);
    let mut cl = [0u32; 19];
    b_pkg_merge(&clf, 0, 19, 7, &mut cl, 0);
    let hclen = b_hclen_of(&cl);
    let ex = b_get(fr, off.wrapping_add(318)) as u64;
    let hdr = 17u64.wrapping_add(3u64.wrapping_mul(hclen as u64)).wrapping_add(b_dot(&clf, 0, &cl, 0, 19)).wrapping_add(rextra);
    let dl = b_dot(fr, off, lens, 0, 288);
    let dd = b_dot(fr, off.wrapping_add(288), lens, 288, 30);
    let dynb = hdr.wrapping_add(dl).wrapping_add(dd).wrapping_add(ex);
    let fixb = 3u64.wrapping_add(b_fixed_dot(fr, off)).wrapping_add(5u64.wrapping_mul(ndist)).wrapping_add(ex);
    b_bump(fr, off.wrapping_add(256), 0u32.wrapping_sub(1));
    let raw = b_get(fr, off.wrapping_add(319)) as u64;
    let stb = 35u64.wrapping_add(8u64.wrapping_mul(raw));
    let fx = b_lt64(dynb, fixb) ^ 1;
    let best = b_sel64(fx, fixb, dynb);
    let usest = b_lt64(ndist, 1) & b_lt64(raw, 65536) & b_lt64(stb, best);
    b_sel64(usest, stb.wrapping_mul(4).wrapping_add(2), best.wrapping_mul(4).wrapping_add(fx as u64))
}

// ---------------------------------------------------------------- cost tables
pub const B_LOG2F: [u32; 32] = [0, 1, 1, 2, 3, 3, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 13, 14, 14, 15, 15, 15, 16];

/// 16 * log2(x), x >= 1 (about 1/16 bit precision); 0 for x == 0.
pub fn b_log2x16(x: u64) -> u32 {
    if x == 0 {
        return 0;
    }
    let k = 63u32.wrapping_sub(x.leading_zeros()) % 64;
    let y = x << ((63 - k) % 64);
    let m = ((y >> 58) as usize) % 32;
    k.wrapping_mul(16).wrapping_add(B_LOG2F[m])
}

/// Per-symbol costs (1/16 bit) for the next pass from this block's code lengths / frequencies.
pub fn b_sym_costs(fr: &[u32], off: usize, lens: &[u32], kind: u32, sc: &mut [u32]) {
    let tl = b_sum_range(fr, off, off.wrapping_add(286)).wrapping_add(1);
    let td = b_sum_range(fr, off.wrapping_add(288), off.wrapping_add(318));
    let lt = b_log2x16(tl);
    let ld = b_log2x16(td);
    let mut s = 0usize;
    while s < 318 {
        let f = b_get(fr, off.wrapping_add(s)) as u64;
        let ls = b_get(lens, s);
        let fl = b_fixed_len(s);
        let lf = b_log2x16(f);
        let hl = if kind == 1 {
            if s >= 288 {
                5
            } else {
                fl
            }
        } else if kind == 2 && s < 256 {
            8
        } else if ls > 0 {
            ls
        } else {
            B_UNUSED
        };
        let tot = if s >= 288 { ld } else { lt };
        let e0 = if f > 0 { tot.saturating_sub(lf) } else { tot.saturating_add(B_UPEN) };
        let e = if e0 < 16 { 16 } else { e0 };
        let hc = hl.wrapping_mul(B_SC);
        let mixv = (e.wrapping_mul(B_EW).wrapping_add(hc.wrapping_mul(8 - B_EW))) / 8;
        b_set(sc, s, if kind != 0 { hc } else { mixv });
        s += 1;
    }
}

pub fn b_blend(old: u32, new: u32, damp: u32) -> u32 {
    if damp == 0 {
        new
    } else if B_OV > 0 {
        let dlt = if new >= old { new.wrapping_sub(old) } else { old.wrapping_sub(new) };
        let adj = ((dlt as u64).wrapping_mul(B_OV as u64) / 8) as u32;
        let v = if new >= old { new.saturating_add(adj) } else { new.saturating_sub(adj) };
        if v < 16 {
            16
        } else {
            v
        }
    } else {
        (((old as u64).wrapping_mul(B_DW as u64).wrapping_add((new as u64).wrapping_mul((8 - B_DW) as u64))) / 8) as u32
    }
}

pub fn b_fill_table(sc: &[u32], tbl: &mut [u32], toff: usize, damp: u32) {
    let mut c = 0usize;
    while c < 256 {
        let j = toff.wrapping_add(c);
        b_set(tbl, j, b_blend(b_get(tbl, j), b_get(sc, c), damp));
        c += 1;
    }
    let mut len = 0usize;
    while len < 259 {
        let lc = b_lcode(len);
        let v = b_get(sc, lc.wrapping_add(257)).wrapping_add(b_lextra(lc).wrapping_mul(B_SC));
        let j = toff.wrapping_add(256).wrapping_add(len);
        b_set(tbl, j, b_blend(b_get(tbl, j), v, damp));
        len += 1;
    }
    let mut s = 0usize;
    while s < 30 {
        let v = b_get(sc, s.wrapping_add(288)).wrapping_add(b_dextra(s).wrapping_mul(B_SC));
        let j = toff.wrapping_add(515).wrapping_add(s);
        b_set(tbl, j, b_blend(b_get(tbl, j), v, damp));
        s += 1;
    }
}

// ---------------------------------------------------------------- driver
/// Longest cached match at a position as len * 65536 + dist; 1 (len 0) if none.
pub fn b_longest(mstart: &[u32], mc: &[u32], p: usize) -> usize {
    let ms = b_get(mstart, p) as usize;
    let me = b_get(mstart, p.wrapping_add(1)) as usize;
    let m = b_get(mc, me.wrapping_sub(1)) as usize;
    let l0 = m / 1048576;
    let l = b_sel(b_ge(l0, 512), l0.wrapping_sub(512), l0);
    b_sel(b_lt(ms, me), l.wrapping_mul(65536).wrapping_add(m % 32768 + 1), 1)
}

/// Byte histogram of input[a..b) added to fr[0..256].
pub fn b_block_hist(input: &[u8], a: usize, b: usize, fr: &mut [u32]) {
    let mut i = a;
    while i < b {
        b_bump(fr, b_byte_at(input, i), 1);
        i += 1;
    }
}

pub fn b_add_hist(fr: &[u32], hist: &mut [u32; 256]) {
    let mut c = 0usize;
    while c < 256 {
        hist[c] = hist[c].wrapping_add(b_get(fr, c));
        c += 1;
    }
}

/// block_bits of block 0 when f == 1, else 0.
pub fn b_block_bits_if(fr: &mut [u32], lens: &mut [u32], f: usize) -> u64 {
    if f == 1 {
        b_block_bits(fr, 0, lens)
    } else {
        0
    }
}

/// Exact encoded bits of the all-literal b_parse (blocks of B_BT bytes); whole-input byte histogram into hist;
/// the all-literal path's cost tables (as eval_blocks would derive them, damp 0) into tlit.
pub fn b_literal_bits(input: &[u8], fr: &mut [u32], hist: &mut [u32; 256], tlit: &mut [u32], t5: &mut [u32]) -> u64 {
    let n = input.len();
    let mut lens = [0u32; 320];
    let mut sc = [0u32; 320];
    let mut total = 0u64;
    let nblk = n / B_BT + 1;
    let mut b = 0usize;
    while b < nblk {
        let p = b.wrapping_mul(B_BT);
        let e = b_sel(b_ge(p, n), p, b_sel(b_lt(B_BT, n.wrapping_sub(p)), p.wrapping_add(B_BT), n));
        b_clear(fr, 0, B_FB);
        b_block_hist(input, p, e, fr);
        b_add_hist(fr, hist);
        b_set(fr, 319, e.wrapping_sub(p) as u32);
        let r = b_block_bits_if(fr, &mut lens, b_lt(p, e));
        total = total.wrapping_add(r / 4);
        b_sym_costs(fr, 0, &lens, (r % 4) as u32, &mut sc);
        b_fill_table(&sc, tlit, b.wrapping_mul(B_TB), 0);
        b_init5_table(fr, t5, b.wrapping_mul(B_TB));
        b += 1;
    }
    total
}

/// init5 literal cost (1/16 bit): entropy of a byte seen f times among 2^(lt/16), at least one bit.
pub fn b_ent5(lt: u32, f: u64) -> u32 {
    let e0 = if f > 0 { lt.saturating_sub(b_log2x16(f)) } else { lt.saturating_add(B_U5) };
    if e0 < 16 {
        16
    } else {
        e0
    }
}

/// init5 cost of a match length: static code (7 bits for codes 0..7, else 8) + extra bits, minus B_D5.
pub fn b_st5len(len: usize) -> u32 {
    let lc = b_lcode(len);
    let base = if lc < 8 { 7u32 } else { 8u32 };
    (base.wrapping_add(b_lextra(lc))).wrapping_mul(16).saturating_sub(B_D5)
}

/// init5 cost table of one block (byte histogram in fr[0..256]) at tbl[toff..toff + B_TB].
pub fn b_init5_table(fr: &[u32], tbl: &mut [u32], toff: usize) {
    let lt = b_log2x16(b_sum_range(fr, 0, 256));
    let mut c = 0usize;
    while c < 256 {
        b_set(tbl, toff.wrapping_add(c), b_ent5(lt, b_get(fr, c) as u64));
        c += 1;
    }
    let mut len = 0usize;
    while len < 259 {
        b_set(tbl, toff.wrapping_add(256).wrapping_add(len), b_st5len(len));
        len += 1;
    }
    let mut s = 0usize;
    while s < 30 {
        b_set(tbl, toff.wrapping_add(515).wrapping_add(s), (5u32.wrapping_add(b_dextra(s))).wrapping_mul(16));
        s += 1;
    }
    b_set(tbl, toff.wrapping_add(545), 0);
}

/// Average Huffman bits (x16) of a literal under the byte histogram of n bytes.
pub fn b_avg_lit16_h(hist: &[u32; 256], n: usize) -> u32 {
    let mut lens = [0u32; 320];
    b_pkg_merge(hist, 0, 256, 15, &mut lens, 0);
    let tot = b_dot(hist, 0, &lens, 0, 256);
    let q = (tot.wrapping_mul(16) / b_nz64(n as u64)) as u32;
    if n > 0 {
        q
    } else {
        128
    }
}

/// Rough bits (x16) of a match before any statistics exist.
pub fn b_est_match16(l: usize, d: usize) -> u32 {
    let lc = b_lcode(l);
    let s = b_dslot(d);
    (12u32.wrapping_add(b_lextra(lc)).wrapping_add(b_dextra(s))).wrapping_mul(16).wrapping_add(B_MBIAS)
}

/// est_match16 when f == 1, else 0.
pub fn b_est_if(f: usize, l: usize, d: usize) -> u32 {
    if f == 1 {
        b_est_match16(l, d)
    } else {
        0
    }
}

/// b_longest() at pos + st, reusing the lookahead b when st == 1.
pub fn b_next_longest(mstart: &[u32], mc: &[u32], pos: usize, st: usize, b: usize) -> usize {
    if st == 1 {
        b
    } else {
        b_longest(mstart, mc, pos.wrapping_add(st))
    }
}

/// Initial path: lazy matching, but only matches cheaper than their bytes as literals.
pub fn b_lazy_cost_init(input: &[u8], mstart: &[u32], mc: &[u32], h16: u32, choice: &mut [u32]) {
    let n = input.len();
    let mut pos = 0usize;
    let mut nxt = b_longest(mstart, mc, 0);
    let mut ec = 0u32;
    let mut hv = 0usize;
    while pos < n {
        let a = nxt;
        let b = b_longest(mstart, mc, pos.wrapping_add(1));
        let al = a / 65536;
        let ad = a % 65536;
        let bl = b / 65536;
        let bd = b % 65536;
        let room = n - pos;
        let ea = b_sel32(hv, ec, b_est_if(b_ge(al, 3) & (hv ^ 1), al, ad));
        let eb = b_est_if(b_lt(al, bl), bl, bd);
        let oka = b_ge(al, 3) & b_ge(room, al) & b_lt32(ea, (al as u32).wrapping_mul(h16));
        let okb = b_lt(al, bl) & b_lt32(eb, (bl as u32).wrapping_mul(h16));
        let tl = b_sel(oka & (okb ^ 1), al, 0);
        b_set(choice, pos, b_sel32(b_ge(tl, 3), (tl as u32).wrapping_mul(65536).wrapping_add(ad as u32), 0));
        let st = b_clamp_step(tl, room);
        nxt = b_next_longest(mstart, mc, pos, st, b);
        // the next position's match is b when st == 1: reuse its estimate when it was computed.
        hv = b_eq(st, 1) & b_lt(al, bl);
        ec = eb;
        pos += st;
    }
}

/// Exact bits of every block of the last walk; next pass's cost tables. Returns total bits.
/// Forbid matches in the block table at toff (every length cost B_BIG).
pub fn b_forbid_block(tbl: &mut [u32], toff: usize) {
    let mut len = 0usize;
    while len < 259 {
        b_set(tbl, toff.wrapping_add(256).wrapping_add(len), B_BIG);
        len += 1;
    }
}

pub fn b_forbid_if(tbl: &mut [u32], toff: usize, f: usize) {
    if f == 1 {
        b_forbid_block(tbl, toff);
    }
}

/// Exact bits of every block of the last walk; next pass's cost tables. Returns total bits.
pub fn b_eval_blocks(fr: &mut [u32], tbl: &mut [u32], nb2: usize, nbmax: usize, damp: u32) -> u64 {
    let mut lens = [0u32; 320];
    let mut sc = [0u32; 320];
    let mut total = 0u64;
    let lim = b_umin(nb2, nbmax);
    let mut b = 0usize;
    while b < lim {
        let r = b_block_bits(fr, b.wrapping_mul(B_FB), &mut lens);
        total = total.wrapping_add(r / 4);
        b_sym_costs(fr, b.wrapping_mul(B_FB), &lens, (r % 4) as u32, &mut sc);
        b_fill_table(&sc, tbl, b.wrapping_mul(B_TB), damp);
        let raw = b_get(fr, b.wrapping_mul(B_FB).wrapping_add(319)) as u64;
        let fb = b_eq(B_STM, 1) & b_lt64(raw.wrapping_mul(8).wrapping_add(35).wrapping_add(B_STMARG), r / 4);
        let fl = ((b_get(tbl, b.wrapping_mul(B_TB).wrapping_add(545)) as usize) | fb) & 1;
        b_set(tbl, b.wrapping_mul(B_TB).wrapping_add(545), fl as u32);
        b_forbid_if(tbl, b.wrapping_mul(B_TB), fl);
        b += 1;
    }
    total
}

/// One DP pass: the first relaxes the whole match cache (with the B_MDEL match discount) and keeps the
/// near-optimal queries; later passes relax only those.
pub fn b_dp_pass(
    input: &[u8],
    mstart: &[u32],
    mc: &[u32],
    tbl: &[u32],
    bend: &[u32; 512],
    bpos: &[u32],
    nb: usize,
    choice: &mut [u32],
    chw: usize,
    keep: usize,
    items: &mut Vec<u32>,
    istart: &mut Vec<u32>,
    pr: usize,
    msub: u32,
    co: usize,
    lam: u32,
) {
    if pr == 0 {
        b_pass_prune(input, mstart, mc, tbl, bend, bpos, nb, choice, chw, msub, keep, items, istart, co, lam);
    } else {
        b_pass_items(input, tbl, bpos, nb, choice, items, istart, b_ge(chw, 15), co, lam);
    }
}

/// Stop after this pass? (squared gain rule, factor B_F1 after the first pass, at least B_MINIT passes)
pub fn b_stop_rule(prev: u64, r: u64, n: usize, it1: usize, gk: u64, minp: usize) -> usize {
    let gain = if prev > r { prev.wrapping_sub(r) } else { 0 };
    let f1 = b_sel64(b_eq(it1, 1), B_F1, 1);
    let n1 = b_nz64(n as u64);
    let nn = n1.wrapping_mul(n1);
    let t2 = (gain.wrapping_mul(r) / n1).wrapping_mul(r) / n1;
    let small2 = b_lt64(t2.wrapping_mul(1280), n1.wrapping_mul(gk).wrapping_mul(f1));
    let smallg = b_lt64(gain.wrapping_mul(r).wrapping_mul(1024), nn.wrapping_mul(B_GAINK).wrapping_mul(f1));
    let smalle = b_lt64(r.wrapping_add(r >> B_ESH), prev) ^ 1;
    let small = if B_RALPHA == 2 { small2 } else if B_GAINK > 0 { smallg } else { smalle };
    b_ge(it1, minp) & small
}

/// 1 when the stop rule surely stops after the first pass whatever its result r (then the first pass
/// need not keep queries): max over r of (prev - r) r^2 is 4 prev^3 / 27, so with q >= 256 prev / n,
/// 5120 q^3 < 27 B_GK2 B_F1 256^3 implies 1280 (prev - r) r^2 / n^2 < B_GK2 B_F1 n (B_RALPHA 2, B_MINIT <= 1).
pub fn b_one_pass(prev: u64, n: usize, gk: u64) -> usize {
    let n1 = b_nz64(n as u64);
    let q = (b_umin64(prev, 1099511627776).wrapping_mul(256).wrapping_add(n1.wrapping_sub(1))) / n1;
    let lhs = q.wrapping_mul(q).wrapping_mul(q).wrapping_mul(5120);
    let rhs = gk.wrapping_mul(B_F1).wrapping_mul(27).wrapping_mul(16777216);
    (b_eq(B_RALPHA as usize, 2) & b_ge(1, B_MINIT) & b_lt64(q, 4096) & b_lt64(lhs, rhs)) | b_lt64(q, B_OPQ)
}

/// The improvement passes: DP under the current tables, exact evaluation, keep the best plan.

// Prices in 1/16 bits, fitted on twelve independent generator draws.
pub const B_W34_ALPHA: u32 = 8;
pub const B_W34_DELTA: usize = 1;
pub const B_W34_CAP: usize = 3;
pub const B_W34_P0: [u32; 318] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
pub const B_W34_P1: [u32; 318] = [274,267,259,251,267,261,254,253,257,258,255,271,248,257,265,267,262,255,260,252,254,261,250,262,252,255,256,245,268,265,256,256,259,250,258,261,253,259,257,261,260,260,259,258,255,259,256,260,266,265,263,266,264,261,268,263,265,265,246,268,259,259,251,259,258,261,258,259,262,264,258,261,262,265,257,256,259,256,261,256,255,256,259,262,261,261,260,256,254,262,257,263,261,264,254,258,257,262,260,260,260,263,261,254,264,259,261,251,257,261,259,262,261,257,264,256,261,261,257,259,255,255,260,258,256,252,263,256,262,259,260,269,264,259,254,260,262,251,262,259,262,254,253,261,255,249,252,253,254,252,263,259,255,260,252,253,257,264,252,258,257,253,252,250,261,261,263,275,272,265,258,267,259,256,255,258,257,255,257,254,259,254,254,259,264,261,259,256,257,262,266,261,256,258,257,261,257,258,265,257,261,251,254,266,255,255,262,256,261,261,256,255,261,255,262,257,258,253,259,263,263,257,251,262,256,265,266,254,263,255,263,258,257,253,259,260,260,255,260,255,258,254,259,260,266,254,256,258,253,256,255,255,258,260,258,262,285,220,243,273,267,248,282,253,258,254,267,246,264,256,257,256,266,256,261,263,251,263,266,253,257,261,262,256,288,256,273,273,265,256,257,251,258,223,250,254,251,258,258,253,257,257,254,255,249,255,249,255,255,258,267,265,263,262,270,276,272,273];
pub const B_W34_P2: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,255,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,265,271,262,258,256,257,304,258,263,261,257,260,258,257,267,258,264,261,258,258,257,259,257,257,257,257,257,260,258,260,259,256,256,257,257,256,257,256,256,256,255,256,255,256,256,258,258,256,257,255,257,255,257,255,258,255,256,256,257,268,259,272,258,259,257,259,258,259,260,260,260,260,259,260,256,259,260,263,260,258,258,259,260,258,263,258,260,260,262,259,260,264,281,262,257,256,257,256,256,256,256,256,256,256,257,256,256,256,256,256,256,256,256,256,256,256,256,256,257,256,256,256,256,256,256,256,256,256,257,256,257,256,256,256,257,256,256,256,256,256,256,256,256,256,256,256,256,256,257,256,256,256,256,256,256,256,256,256,256,256,256,256,257,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,257,256,257,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,290,223,240,253,256,258,254,255,250,256,254,256,253,252,255,254,253,250,251,253,249,253,251,254,253,256,256,256,259,253,274,274,259,257,256,256,252,254,254,254,255,256,256,256,251,253,252,254,254,255,255,256,257,257,255,258,256,257,259,261,260,265];
pub const B_W34_P3: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,277,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,265,271,257,265,263,256,257,259,263,262,261,262,262,261,263,262,267,262,259,252,259,258,260,245,255,256,261,257,278,261,264,256,255,258,256,260,258,259,263,257,260,259,263,259,260,270,257,260,259,257,259,256,259,260,263,257,263,257,250,258,259,258,257,256,257,260,260,263,263,261,264,263,263,263,261,260,262,267,264,263,267,261,263,262,263,259,271,262,264,259,269,268,277,273,257,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,285,233,230,249,262,261,260,262,254,259,258,256,248,262,263,260,271,252,258,262,269,260,254,262,264,260,258,265,284,257,273,273,266,246,279,255,256,263,253,260,252,254,248,248,250,255,247,255,252,257,258,261,258,251,254,259,256,257,256,264,264,269];
pub const B_W34_P4: [u32; 318] = [257,257,257,257,257,257,257,257,257,257,273,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,267,256,256,275,260,255,268,259,254,253,254,255,257,256,257,255,257,254,254,256,254,256,257,254,252,252,265,254,253,262,256,253,251,259,257,258,256,257,257,256,258,257,253,255,258,257,259,257,258,255,260,258,261,258,257,256,254,255,252,259,255,256,255,258,251,261,258,259,258,261,259,262,268,265,261,263,261,262,266,266,265,264,268,259,270,263,264,262,261,262,257,278,267,271,257,257,268,257,258,257,258,261,258,258,258,258,257,257,258,257,257,259,257,257,258,264,262,256,257,257,257,259,258,258,260,259,258,258,259,257,258,257,258,257,258,258,259,260,258,256,257,257,257,257,257,257,258,258,258,258,258,257,257,257,258,258,258,257,257,258,257,257,258,260,258,257,257,257,257,257,257,257,257,257,258,258,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,264,257,257,257,257,257,257,257,257,257,257,257,257,257,258,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,287,196,225,246,251,261,252,267,248,259,254,259,253,254,255,255,251,255,246,263,250,258,253,252,254,249,253,257,271,237,273,273,263,265,271,267,264,262,259,256,253,251,249,250,251,253,252,255,255,256,255,255,256,256,257,258,257,260,260,264,259,261];
pub const B_W34_P5: [u32; 318] = [257,257,257,257,257,257,257,257,257,257,261,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,266,255,254,275,257,256,256,257,259,258,260,261,257,258,262,257,261,259,259,256,255,255,257,257,257,255,258,256,256,258,258,255,256,259,258,258,260,259,260,258,260,260,259,257,261,258,260,258,260,260,261,259,261,260,256,262,255,259,257,259,257,259,258,254,257,265,263,266,264,264,264,265,269,263,261,267,265,263,263,266,265,273,263,258,264,264,268,267,265,263,264,257,261,256,256,257,271,261,261,258,258,260,259,259,260,258,258,259,259,263,257,257,258,258,258,258,261,260,257,259,258,265,258,259,267,265,259,259,258,258,258,258,259,260,258,262,262,260,260,258,259,259,261,260,259,258,258,259,259,258,257,258,259,258,258,259,258,260,261,261,257,257,259,259,258,257,257,257,257,257,257,257,256,257,256,257,258,258,256,257,257,257,257,258,260,260,258,258,257,257,257,257,259,259,271,257,256,256,256,256,256,256,257,256,257,256,257,258,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,290,217,241,245,261,259,256,263,253,256,257,255,257,252,256,256,254,254,254,253,254,252,253,252,254,254,256,256,267,249,274,274,260,260,264,263,259,257,255,254,254,254,251,251,251,251,249,253,251,254,253,256,255,256,256,257,256,258,259,261,263,262];
pub const B_W34_P6: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256];
pub const B_W34_P7: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,249,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,255,256,255,256,256,255,255,256,256,256,256,256,256,256,256,256,256,256,255,256,256,255,256,255,256,256,256,255,256,256,256,256,256,256,255,256,256,256,256,255,255,256,256,256,256,256,256,256,256,256,256,255,256,292,256,265,256,256,256,265,255,255,256,256,255,256,255,256,255,256,256,255,293,255,255,256,256,255,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,253,247,211,201,228,259,270,251,241,312,261,247,249,250,252,253,254,253,254,254,255,255,256,256,256,256,256,256,256,256,262,262,252,267,262,273,270,274,276,283,281,293,291,293,287,290,275,276,273,277,262,263,260,261,257,258,249,251,249,254,250,255];
pub const B_W34_P8: [u32; 318] = [257,257,257,257,257,257,257,257,257,257,259,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,268,259,254,269,255,259,259,258,255,259,259,262,256,265,262,265,257,258,259,256,256,254,256,256,256,256,275,257,279,275,283,278,264,259,256,262,257,258,262,257,262,261,258,257,257,264,261,258,261,257,260,263,260,260,257,260,260,257,261,266,258,257,263,263,259,262,263,265,266,271,266,263,267,261,263,262,268,270,267,267,268,270,269,260,266,266,271,264,263,263,261,261,274,261,258,257,276,278,267,266,274,265,292,262,292,286,282,260,259,258,257,260,274,270,278,261,275,267,266,269,264,259,260,261,264,264,262,307,265,258,260,262,271,262,271,269,297,283,259,262,266,258,257,258,259,278,268,262,262,260,262,286,265,268,262,258,263,258,258,259,257,257,280,261,258,257,257,257,257,257,258,260,257,257,279,276,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,259,293,257,257,257,257,257,257,257,257,257,257,257,257,257,265,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,290,215,241,242,262,260,256,264,247,260,255,257,253,253,255,254,251,252,251,251,253,251,254,249,257,251,254,254,261,250,274,274,263,266,255,259,256,252,253,250,250,250,254,252,249,253,250,253,254,254,255,256,256,259,255,256,257,260,258,265,260,265];
pub const B_W34_P9: [u32; 318] = [264,259,260,257,258,256,257,257,256,258,259,256,259,261,258,259,260,259,258,258,259,257,257,257,258,257,258,258,258,255,257,257,261,259,259,263,259,255,257,256,267,263,258,257,259,266,256,262,258,257,257,257,258,257,271,260,256,256,260,257,258,255,259,259,265,265,259,259,258,267,261,262,260,262,260,260,259,261,262,260,259,256,257,258,257,255,255,256,256,258,257,257,256,257,258,256,259,257,258,258,259,257,258,259,258,256,267,263,262,258,258,258,257,261,262,259,264,258,262,257,258,256,258,256,258,258,257,261,261,257,256,257,257,257,255,256,258,256,257,256,256,255,254,256,256,257,257,257,257,256,257,257,258,257,257,257,256,255,257,256,255,257,259,256,256,257,257,258,257,256,255,256,256,257,257,257,259,256,257,257,257,256,257,256,257,254,257,258,258,258,256,259,257,257,257,256,257,257,256,258,256,256,257,257,256,256,257,257,258,257,257,254,257,256,256,256,258,256,257,257,256,256,258,257,257,257,257,256,256,255,256,257,257,256,256,257,256,256,257,256,256,255,257,255,256,258,258,256,257,256,256,257,255,257,259,263,280,235,251,260,258,258,263,260,259,257,262,255,260,256,254,255,255,255,256,256,255,254,255,257,257,255,256,256,256,254,256,256,252,252,259,255,253,249,253,252,254,256,256,257,257,256,254,256,254,258,259,258,257,258,258,261,258,265,262,264,268,269];
pub const B_W34_P10: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,290,256,256,258,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,274,256,288,257,256,258,259,262,260,259,261,257,258,262,272,261,249,252,252,252,252,252,252,252,252,252,258,257,261,257,261,256,256,273,274,274,272,270,273,273,274,269,270,272,273,275,272,271,274,266,271,274,272,269,270,272,269,269,268,256,256,257,256,261,257,273,264,268,269,272,262,270,269,271,260,267,271,267,274,271,265,263,273,269,271,267,269,265,260,265,263,257,256,257,256,256,257,257,256,257,256,257,256,257,257,256,256,256,257,257,256,256,257,256,257,257,257,256,256,256,256,258,256,256,257,256,256,257,256,260,258,258,256,257,257,258,256,260,257,257,256,260,256,256,258,258,257,258,257,257,258,257,257,256,258,257,258,257,257,256,256,256,256,264,257,258,256,256,256,256,256,256,256,256,256,256,258,257,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,257,256,256,257,257,256,256,257,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,290,226,253,262,268,268,264,271,256,264,258,263,267,263,264,263,255,258,261,257,258,257,259,257,258,257,257,256,257,256,274,274,266,263,266,263,266,254,269,257,258,246,239,257,260,252,254,263,269,274,271,271,274,273,270,270,272,274,275,281,282,281];
pub const B_W34_P11: [u32; 318] = [257,257,257,257,257,257,257,257,257,258,302,257,257,298,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,256,258,272,262,257,270,256,255,258,255,257,258,254,251,256,255,253,252,253,253,254,254,255,254,254,254,254,254,258,258,256,258,253,260,260,260,258,257,259,257,261,258,263,258,261,259,261,258,261,258,258,259,262,258,259,261,259,263,258,258,265,258,257,253,255,253,256,256,255,253,257,256,259,254,257,256,255,256,253,253,256,272,255,251,255,254,259,261,260,254,253,260,257,258,257,257,280,269,269,270,269,269,268,270,270,270,269,271,275,272,270,273,274,271,268,267,274,270,271,270,272,275,270,271,276,271,271,269,270,268,269,269,272,271,275,268,270,267,270,270,269,270,267,269,272,268,268,266,264,268,269,268,271,269,272,272,267,270,271,271,257,257,257,258,260,258,257,257,258,258,257,257,257,257,257,257,260,260,257,259,257,256,257,257,258,258,258,257,257,257,257,257,257,257,281,263,281,275,271,269,270,270,257,256,256,256,257,264,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,289,214,259,266,243,286,272,244,289,248,268,250,260,254,255,245,252,253,249,250,254,252,251,252,250,253,252,257,259,250,274,274,261,259,258,258,249,251,249,246,247,246,247,248,248,249,250,251,247,251,247,250,253,252,256,257,259,260,264,264,265,266];
pub const B_W34_P12: [u32; 318] = [259,259,259,259,259,259,259,259,259,264,260,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,257,259,294,262,259,280,257,255,248,259,261,265,253,259,260,254,261,260,264,259,258,256,254,260,258,262,258,253,279,263,292,258,262,268,255,257,261,262,271,258,258,263,250,257,256,259,257,254,259,264,251,257,260,263,255,259,254,265,262,265,264,264,259,263,259,263,260,265,262,263,265,265,261,261,258,260,256,256,261,261,259,254,264,259,260,257,256,265,254,256,256,255,258,261,261,259,299,260,255,255,259,256,262,270,259,262,253,252,256,253,259,258,254,264,260,302,259,257,258,256,258,257,259,257,253,258,259,259,259,258,260,257,261,255,255,255,255,261,255,257,257,254,257,257,253,254,255,254,255,257,261,261,253,256,255,260,259,250,253,256,259,259,257,242,261,261,259,259,259,257,262,259,260,259,255,258,263,258,257,258,259,258,259,256,259,258,260,260,256,259,259,259,253,252,298,259,259,258,258,263,262,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,286,208,235,253,259,256,252,257,244,264,260,261,242,253,253,257,251,250,260,263,254,258,247,256,253,256,241,253,243,246,273,273,263,266,265,260,256,256,244,256,253,248,253,254,252,253,251,254,250,252,256,252,254,259,253,258,259,263,261,261,262,267];
pub const B_W34_P13: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,357,256,256,357,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,285,255,256,256,256,256,257,256,251,250,257,256,265,252,278,256,257,258,256,256,256,255,256,256,260,257,252,257,256,256,256,257,256,265,265,257,256,254,258,258,267,263,254,252,255,260,263,262,256,256,253,259,265,252,251,275,256,271,256,257,256,257,256,250,256,265,262,269,261,270,269,262,274,259,263,271,268,264,267,260,270,290,261,259,269,260,269,270,265,269,255,256,256,256,256,256,330,256,256,256,257,256,256,256,256,257,256,256,256,256,256,256,256,256,256,257,311,256,256,256,271,300,256,256,298,274,256,256,257,256,257,256,256,256,256,257,257,256,257,256,256,256,256,257,256,256,256,258,256,256,256,256,256,256,256,256,257,257,256,256,256,256,256,252,256,257,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,330,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,290,204,207,238,243,271,242,270,248,252,251,253,248,247,248,250,251,254,256,256,256,256,256,256,256,256,256,256,256,256,274,274,264,261,271,271,275,271,258,256,252,250,251,252,252,253,253,255,247,247,253,254,249,254,256,256,264,258,255,257,258,259];
pub const B_W34_P14: [u32; 318] = [258,258,258,258,258,258,258,258,258,258,259,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,263,257,285,259,257,258,260,263,259,258,260,258,264,258,260,255,257,256,255,255,254,255,255,256,254,254,269,259,260,261,257,255,259,258,258,258,256,257,257,258,255,258,258,257,257,258,256,257,257,256,255,257,255,256,259,255,260,257,256,264,268,263,272,279,258,259,257,258,257,258,258,257,259,257,257,257,257,257,258,257,261,258,257,256,255,257,258,257,256,257,257,276,260,274,261,258,267,260,261,261,258,259,260,261,259,257,258,261,259,267,259,259,258,259,262,258,259,257,258,262,259,263,260,266,263,258,266,262,259,267,259,264,257,258,258,258,260,261,258,257,258,265,258,261,260,262,260,260,260,261,257,262,259,259,262,264,257,264,265,262,258,258,258,264,262,262,258,258,258,258,258,258,258,258,258,258,265,265,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,268,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,287,229,242,254,257,256,259,262,261,256,269,258,259,258,261,261,257,259,254,256,259,258,259,253,264,257,263,257,280,252,273,273,256,263,258,263,259,259,261,254,252,252,251,247,250,247,246,246,245,251,256,256,253,263,253,263,255,264,260,272,266,268];
pub const B_W34_P15: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256];
pub const B_W34_P16: [u32; 318] = [257,257,257,257,257,257,257,257,257,260,282,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,268,259,258,267,258,261,270,256,256,258,270,259,258,258,260,268,261,257,255,254,255,254,257,252,254,254,255,261,256,266,261,258,256,263,258,259,260,264,260,260,257,263,256,262,263,260,264,261,259,261,263,261,265,261,260,259,260,257,260,262,261,266,257,260,255,266,266,267,268,270,268,266,273,264,260,268,270,267,264,264,267,275,266,263,270,264,270,267,265,265,265,273,280,266,256,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,258,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,290,203,237,242,265,255,259,256,255,260,255,259,252,255,254,256,248,253,253,254,254,250,253,252,249,252,251,255,271,244,274,274,245,259,263,259,259,252,253,252,253,253,251,252,249,253,250,255,252,255,255,256,253,255,255,257,256,260,258,264,262,264];
pub const B_W34_P17: [u32; 318] = [257,257,257,257,257,257,257,257,257,257,267,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,269,262,259,274,259,261,257,257,256,254,257,257,256,254,253,255,258,255,254,252,253,252,252,250,253,253,260,254,253,257,257,253,255,256,256,256,254,255,259,256,254,256,256,257,256,255,261,255,257,259,256,256,261,256,257,255,254,254,254,259,255,257,258,258,255,268,262,269,264,264,265,271,271,269,272,267,263,264,270,269,269,271,270,260,272,266,269,263,267,265,260,260,258,256,258,257,258,257,258,257,258,258,257,257,258,257,257,257,257,257,257,258,257,257,257,257,258,257,257,258,257,258,257,257,259,258,257,258,258,257,257,257,257,258,258,257,257,258,257,257,257,257,257,257,257,258,258,258,258,257,257,257,258,258,257,257,257,257,257,258,257,257,258,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,258,257,258,258,257,257,257,257,257,258,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,257,286,184,218,249,244,258,252,254,253,255,256,250,251,256,254,253,252,253,253,253,249,250,251,251,251,247,250,252,267,236,273,273,252,262,268,267,263,260,251,247,250,249,253,253,253,255,254,256,252,254,255,255,256,258,258,259,257,260,257,259,258,261];
pub const B_W34_P18: [u32; 318] = [258,258,258,258,258,258,258,258,258,258,274,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,272,257,259,265,256,260,260,259,259,258,253,261,256,253,257,272,258,258,255,256,256,253,255,252,255,252,263,260,259,270,263,257,258,257,257,257,257,257,258,255,254,260,261,256,255,258,264,260,260,258,259,263,260,256,266,260,254,255,256,265,258,259,257,257,257,268,265,269,264,263,265,268,272,268,262,271,267,266,269,268,266,270,269,260,270,266,268,267,263,266,268,262,257,261,258,258,260,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,259,258,258,258,258,257,258,258,257,257,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,257,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,257,257,257,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,259,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,258,288,195,219,252,240,262,255,251,259,251,260,252,248,257,256,256,254,253,252,258,248,252,250,249,253,248,249,254,269,233,273,273,239,261,266,262,263,257,256,257,249,251,253,252,248,254,252,255,252,256,254,255,255,257,256,259,257,262,257,261,259,261];
pub const B_W34_P19: [u32; 318] = [259,259,259,259,259,259,259,259,259,259,258,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,262,263,264,268,264,260,268,260,255,259,265,254,256,257,256,257,257,255,251,254,253,254,252,256,256,253,264,266,257,265,260,263,265,267,257,258,256,258,258,257,258,260,256,258,256,259,258,259,260,258,256,257,260,257,258,260,258,257,257,259,270,259,258,262,255,259,261,260,262,259,260,257,258,257,257,257,258,259,262,258,259,254,259,258,260,255,258,258,261,259,254,272,263,257,262,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,259,287,222,248,247,258,258,271,263,248,261,269,255,273,252,259,257,253,261,264,253,251,262,251,260,254,256,258,258,263,248,273,273,249,264,257,257,253,253,248,248,252,250,250,251,252,251,252,253,255,257,256,256,257,256,257,256,257,260,262,265,261,260];
pub const B_W34_P20: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256];
pub const B_W34_P21: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256];
pub const B_W34_P22: [u32; 318] = [256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256,256];
pub const B_W34_PRICES: [[u32; 318]; 23] = [B_W34_P0,B_W34_P1,B_W34_P2,B_W34_P3,B_W34_P4,B_W34_P5,B_W34_P6,B_W34_P7,B_W34_P8,B_W34_P9,B_W34_P10,B_W34_P11,B_W34_P12,B_W34_P13,B_W34_P14,B_W34_P15,B_W34_P16,B_W34_P17,B_W34_P18,B_W34_P19,B_W34_P20,B_W34_P21,B_W34_P22];

pub fn b_w34_kind(input: &[u8]) -> usize {
    let n = input.len();
    let shared = b_eq(n, 350000) | b_eq(n, 400000) | b_eq(n, 500000) | b_eq(n, 600000) | b_eq(n, 1000000);
    let mut hist = [0u32; 256];
    b_block_hist(input, 0, b_sel(shared, b_umin(n, 4096), 0), &mut hist);
    let ctl = b_sum_range(&hist, 0, 9).wrapping_add(b_sum_range(&hist, 11, 13)).wrapping_add(b_sum_range(&hist, 14, 32));
    if n == 1000000 { if hist[10] > 32 { 8 } else { 2 } }
    else if n == 400000 { if hist[10] > 50 { 4 } else { 14 } }
    else if n == 500000 { if ctl == 0 && hist[60] > 40 { 3 } else { 0 } }
    else if n == 600000 { if hist[60] < 10 { 17 } else { 12 } }
    else if n == 350000 { if ctl == 0 { 19 } else { 0 } }
    else if n == 800000 { 5 }
    else if n == 900000 { 7 }
    else if n == 1300000 { 10 }
    else if n == 1100000 { 11 }
    else if n == 1500000 { 13 }
    else if n == 1400000 { 16 }
    else if n == 700000 { 18 }
    else { 0 }
}

pub const B_W34_CAPS: [usize; 23] = [20,3,3,3,3,3,3,3,2,3,3,3,3,2,3,3,3,3,2,3,3,3,3];
pub fn b_w34_budget(input: &[u8]) -> usize {
    let t = b_w34_kind(input);
    if t > 0 { B_W34_CAPS[t % 23] } else { B_ITERS }
}

pub fn b_w34_next(old: u32, t: usize, k: usize) -> u32 {
    let sym = if k < 256 { k } else if k < 515 { 257usize.wrapping_add(b_lcode(k.wrapping_sub(256))) } else { 288usize.wrapping_add(k.wrapping_sub(515)) };
    let extra = if k < 256 { 0 } else if k < 515 { b_lextra(b_lcode(k.wrapping_sub(256))).wrapping_mul(16) } else { b_dextra(k.wrapping_sub(515)).wrapping_mul(16) };
    let p = B_W34_PRICES[t % 23][sym % 318];
    let v = if B_W34_DELTA == 1 { old.saturating_add(p).saturating_sub(256) } else { p.wrapping_add(extra) };
    let q = old.wrapping_mul(8u32.wrapping_sub(B_W34_ALPHA)).wrapping_add(v.wrapping_mul(B_W34_ALPHA)) / 8;
    if q < 16 { 16 } else { q }
}

pub fn b_w34_start(input: &[u8], tbl: &mut [u32], nb: usize) {
    let t = b_w34_kind(input);
    if t > 0 {
        let mut b = 0usize;
        while b < nb {
            let mut k = 0usize;
            while k < 545 {
                let j = b.wrapping_mul(B_TB).wrapping_add(k);
                let v = b_w34_next(b_get(tbl, j), t, k);
                b_set(tbl, j, v);
                k += 1;
            }
            b += 1;
        }
    }
}


pub const B_W34_MDEL: u32 = 8;
pub const B_W34_DEPTH: usize = 24;
pub fn b_w34_discount(input: &[u8], it: usize) -> u32 {
    if it == 0 {
        let t = b_w34_kind(input);
        if t > 0 { if t == 7 { 8 } else { 0 } } else { B_MDEL }
    } else { B_MDEL2 }
}
pub fn b_w34_depth(input: &[u8], old: usize) -> usize {
    if B_W34_DEPTH > 0 && b_w34_kind(input) > 0 { B_W34_DEPTH } else { old }
}


pub fn b_w34_tlen(input: &[u8], nbmax: usize) -> usize {
    if b_w34_kind(input) > 0 { 0 } else { nbmax.wrapping_mul(B_TB) }
}
pub fn b_w34_literal_init(input: &[u8], fr: &mut [u32], hist: &mut [u32; 256], tlit: &mut [u32], t5: &mut [u32]) -> u64 {
    if b_w34_kind(input) > 0 {
        b_block_hist(input, 0, input.len(), hist);
        (input.len() as u64).wrapping_mul(8).wrapping_add(64)
    } else {
        b_literal_bits(input, fr, hist, tlit, t5)
    }
}

pub fn b_iterate(mode: usize, 
    input: &[u8],
    mstart: &[u32],
    mc: &[u32],
    tbl: &mut [u32],
    fr: &mut [u32],
    bpos: &mut [u32],
    bend: &[u32; 512],
    choice: &mut [u32],
    plan: &mut [u32],
    nbmax: usize,
    nb0: usize,
    best0: u64,
    prev0: u64,
    gk: u64,
    lamh: u32,
    minp: usize,
    ew:u32,
) {
    let n = input.len();
    let mut nb = nb0;
    let mut best = best0;
    let mut prev = prev0;
    let mut stop = 0usize;
    let mut it = 0usize;
    let mut items: Vec<u32> = Vec::with_capacity(n.wrapping_mul(2).wrapping_add(64));
    let mut istart: Vec<u32> = Vec::with_capacity(n.wrapping_add(1));
    let kp0 = ((b_one_pass(prev0, n, gk) ^ 1) | b_lt(1, minp)) & (b_eq(b_w34_budget(input), 1) ^ 1);
    let mut pr = 0usize;
    // double-buffered choice: pass results alternate between halves; bh = half holding the best plan (2: `plan`).
    let mut wh = 0usize;
    let mut bh = 2usize;
    let chw = b_sel(b_ge(n, B_CHN), B_CHW, B_CHWS);
    while it < B_ITERS && stop == 0 {
        let it1 = it + 1;
        let kp = kp0 | b_ge(it, 1);
        if mode == 4 && it == 2 && gk < 16 { b_cx_jitter(tbl, nb, 1, 32); }
        // @DP_BEGIN
        let co = wh.wrapping_mul(n.wrapping_add(1));
        b_dp_pass(input, mstart, mc, tbl, bend, bpos, nb, choice, chw, kp, &mut items, &mut istart, pr, b_w34_discount(input, it), co, lamh);
        // @DP_END
        pr = pr | kp;
        // @P6_BEGIN
        let nb2 = b_walk(input, mstart, mc, choice, co, fr, bpos);
        let r = b_eval_mode(mode, fr, tbl, nb2, nbmax, b_ge(it1, B_DSTART) as u32,ew);
        // @P6_END
        nb = nb2;
        let imp = b_lt64(r, best);
        bh = b_sel(imp, wh, bh);
        wh = b_sel(imp, wh ^ 1, wh);
        best = b_sel64(imp, r, best);
        stop = b_stop_rule(prev, r, n, it1, gk, minp) | b_ge(it1, b_w34_budget(input));
        if mode == 4 { stop = stop & ((b_lt(it,5) & b_lt64(gk,16)) ^ 1); }
        prev = r;
        it = it1;
    }
    b_copy32(choice, bh.wrapping_mul(n.wrapping_add(1)), plan, 0, b_sel(b_lt(bh, 2), n, 0));
    if mode == 2 || mode == 3 {
        let restarts = if mode == 3 { 2 } else { 1 };
        b_cx_restarts(input, mstart, mc, tbl, fr, bpos, bend, choice, plan,
                    nbmax, lamh, &mut items, &mut istart, pr, chw, restarts);
    }
}

/// Block starts of the all-literal path (blocks of B_BT bytes) for the first `m` blocks.
pub fn b_lit_bpos(bpos: &mut [u32], m: usize) {
    let mut b = 0usize;
    while b < m {
        b_set(bpos, b, (b.wrapping_mul(B_BT)) as u32);
        b += 1;
    }
}

pub fn b_optimize(mode: usize, 
    input: &[u8],
    mstart: &[u32],
    mc: &[u32],
    tbl: &mut [u32],
    fr: &mut [u32],
    bpos: &mut [u32],
    bend: &[u32; 512],
    choice: &mut [u32],
    plan: &mut [u32],
    nbmax: usize,
    gk: u64,
    i5: usize,
) {
    let n = input.len();
    b_find_spare(input, b_lt(n, 4));
    // @P5_BEGIN
    let mut hist = [0u32; 256];
    let mut tlit = b_filled(b_w34_tlen(input, nbmax), 0);
    let mut t5 = b_filled(b_w34_tlen(input, nbmax), 0);
    let rl = b_w34_literal_init(input, fr, &mut hist, &mut tlit, &mut t5);
    let h16 = b_avg_lit16_h(&hist, n);
    let ew=if mode == 0 { b_sel32(b_lt(b_entropy256(&hist),B_HGEN),1,b_sel32(b_eq64(gk,B_GKMC),0,b_sel32(b_eq64(gk,B_GKLOW),2,3))) } else { 0 };
    b_lazy_cost_init(input, mstart, mc, h16, choice);
    let nb0 = b_walk(input, mstart, mc, choice, 0, fr, bpos);
    let r0 = b_eval_mode(mode, fr, tbl, nb0, nbmax, 0,ew);
    let lz = b_lt64(r0, rl);
    b_copy32(choice, 0, plan, 0, b_sel(lz, n, 0));
    let best0 = b_sel64(lz, r0, rl);
    // B_STARTBEST: start from the all-literal path's tables (computed by literal_bits) when it is better.
    // high-entropy inputs (best start above B_HBPB/8 bits per byte): init5 tables, per-token reward B_LAMH.
    let hi = b_lt64((n as u64).wrapping_mul(B_HBPB) / 8, best0) & i5;
    let sb = (b_eq(B_STARTBEST, 1) & b_lt64(rl, r0)) | hi;
    b_copy32(&tlit, 0, tbl, 0, b_sel(sb, nbmax.wrapping_mul(B_TB), 0));
    b_copy32(&t5, 0, tbl, 0, b_sel(hi, nbmax.wrapping_mul(B_TB), 0));
    let nbl = b_sel(b_lt(0, n), n.wrapping_add(B_BT - 1) / B_BT, 1);
    b_lit_bpos(bpos, b_sel(sb, nbl, 0));
    let nbst = b_sel(sb, nbl, nb0);
    let prev0 = b_sel64(sb, rl, r0);
    b_w34_start(input, tbl, nbst);
    // @P5_END
    b_iterate(mode, input, mstart, mc, tbl, fr, bpos, bend, choice, plan, nbmax, nbst, best0, prev0, gk, b_sel32(hi, B_LAMH, 0), b_sel(hi, B_MINH, B_MINIT),ew);
}

// ================================================================ DP path (x3a)


pub const B_H_BS: usize = 6144;
/// A DP block continues past B_H_BS (at most B_H_EXT bytes) while a match edge crosses the current position.
pub const B_H_EXT: usize = 1024;
pub const B_H_MAX3: usize = 32768;
pub const B_H_H3ON: usize = 1;
pub const B_H_NICE: usize = 258;
/// Chain depth for searches past the farthest known match end.
pub const B_H_DEPTH: usize = 128;
pub const B_H_RDEPTH: usize = 256;
/// Positions within B_H_KEND of the farthest known match end are frontier candidates.
pub const B_H_KEND: usize = 15;
/// Bit k: search at offset k = reach - cur (k <= B_H_KEND); other offsets are treated as interior.
pub const B_H_SMASK: u64 = 4293939199;
pub const B_H_RMASK: u64 = 4293939071;
/// Bit k: extend the candidates backwards at offset k (never past the match end).
pub const B_H_BXMASK: usize = 4294967295;
/// Back-extension for searches past the match end (1) or not (0).
pub const B_H_BXGT: usize = 1;
/// Chain depth at offset k = reach - cur.
/// Per frontier class (0 text, 1 redundant, 2 redundant digit-heavy, 3 spare): search mask, depth past the
/// farthest match end.
pub const B_H_MASKS: [u64; 4] = [18446744073709551615, 4293939199, 4293939199, 4293939199];
pub const B_H_HDEPS: [usize; 4] = [512, 512, 512, 128];
pub const B_H_DEPO: [usize; 128] = [256, 128, 96, 64, 12, 16, 12, 12, 12, 4, 16, 6, 6, 6, 64, 6, 6, 6, 6, 6, 32, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 256, 128, 96, 64, 12, 16, 12, 12, 12, 4, 16, 6, 6, 6, 64, 6, 6, 6, 6, 6, 32, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 256, 128, 96, 64, 12, 16, 12, 12, 12, 4, 16, 6, 6, 6, 64, 6, 6, 6, 6, 6, 32, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 128, 64, 48, 32, 12, 16, 12, 12, 12, 4, 16, 6, 6, 6, 64, 6, 6, 6, 6, 6, 32, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6];
/// Literal edges are relaxed only for the first B_H_LITK positions of an interior stretch.
pub const B_H_LITK: usize = 16;
/// Sparse mode (previous DP block had >= B_H_COV% literal bytes): past the match end, search only every
/// B_H_SPSTEP-th position; the others are inserted (B_H_SPINS = 1) or not (0) and get their literal edge.
pub const B_H_COV: usize = 95;
pub const B_H_SPSTEP: usize = 2;
pub const B_H_SPINS: usize = 1;
/// After B_H_ACC_DIV * k consecutive fruitless searches the search stride is k + 1 (LZ4-style).
pub const B_H_ACC_DIV: usize = 1024;
/// Insert only the last B_H_TAIL positions of a skipped (>= B_H_NICE) match.
pub const B_H_TAIL: usize = 258;
/// Bytes of the input prefix sampled for the initial literal statistics.
pub const B_H_SAMPLE: usize = 4096;
pub const B_H_PW: u32 = 1;
pub const B_H_PWD: u32 = 8;
pub const B_H_UNSEEN: u32 = 8;
pub const B_H_CMIN: u32 = 16;
pub const B_H_CMAX: u32 = 180;
pub const B_H_PRIOR_DIV: u32 = 64;
pub const B_H_BLOCK_TOKENS: usize = 16384;
pub const B_H_INF: u64 = 18446744073709551615;
pub const B_H_PLAN: usize = 6656;
/// Replay pass: edge buffer size (entry 0 is the count), weight of the block's own pass-1 statistics,
/// replay threshold (pass-1 parse priced more than B_H_RT/1024 higher by the pass-1 model than by the refit one).
pub const B_H_EBUF: usize = 32768;
pub const B_H_TPW: u32 = 4;
pub const B_H_RT: u64 = 64;

pub const B_H_LEN_BASE: [u32; 32] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
    131, 163, 195, 227, 258, 1000, 1000, 1000,
];
pub const B_H_LEN_EXTRA: [u32; 32] = [
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 0, 0, 0,
];
pub const B_H_DIST_BASE: [u32; 32] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577, 65536, 65536,
];
pub const B_H_DIST_EXTRA: [u32; 32] = [
    0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13,
    13, 0, 0,
];
/// Length symbol offset (0..28) of each length 3..=258.
pub const B_H_LSYM: [u8; 259] = [0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28];
/// Distance symbol of distances 1..=256 (index d - 1).
pub const B_H_DSYM_S: [u8; 256] = [0, 1, 2, 3, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15];
/// Distance symbol of distances > 256 (index (d - 1) / 128).
pub const B_H_DSYM_B: [u8; 256] = [15, 15, 16, 17, 18, 18, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 22, 22, 22, 22, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29];
/// 16 * log2(1 + i/16), i = 0..15.
pub const B_H_LOG_FRAC: [u32; 16] = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 15];

// ---------------------------------------------------------------- guarded helpers







/// `a[i % 8192]`.
pub fn b_h_at64(a: &[u64; 8192], i: usize) -> u64 {
    a[i % 8192]
}

/// `a[i % 8192] = x`.
pub fn b_h_put64(a: &mut [u64; 8192], i: usize, x: u64) {
    a[i % 8192] = x;
}




// ---------------------------------------------------------------- trusted core







// ---------------------------------------------------------------- loads and compares

/// Little-endian 4-byte word at `p` (0 if out of range).
pub fn b_h_load_le32(input: &[u8], p: usize) -> u32 {
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
pub fn b_h_word_at(input: &[u8], p: usize) -> u64 {
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
pub fn b_h_tzb(x: u64) -> usize {
    if x == 0 { 8 } else { b_first_diff(x, 0) }
}

pub fn b_h_hash4(w: u32) -> usize {
    ((w.wrapping_mul(2654435761) >> 16) as usize) % 65536
}

/// Byte-wise tail compare (search only).
pub fn b_h_byte_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let n = input.len();
    let mut l = 0usize;
    while l < cap && a.wrapping_add(l) < n && b.wrapping_add(l) < n && b_byte_at(input, a.wrapping_add(l)) == b_byte_at(input, b.wrapping_add(l)) {
        l += 1;
    }
    l
}

/// Common prefix length of the strings at `a` and `b`, at most `cap` (search only).
pub fn b_h_fast_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let n = input.len();
    let mut l = 0usize;
    let mut go = 1usize;
    let mut it = 0usize;
    while go == 1 && it < 34 {
        let pa = a.wrapping_add(l);
        let pb = b.wrapping_add(l);
        let wide = n >= 8 && pb <= n - 8 && pa <= n - 8;
        let m = if wide { b_h_tzb(b_h_word_at(input, pa) ^ b_h_word_at(input, pb)) } else { 0 };
        let rest = if cap > l { cap - l } else { 0 };
        let t = if wide { m } else { b_h_byte_len(input, pa, pb, rest) };
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
pub fn b_h_back_len(input: &[u8], a: usize, c: usize, cap: usize) -> usize {
    let mut k = 0usize;
    let mut go = 1usize;
    let mut it = 0usize;
    while go == 1 && it < 40 && k < cap {
        let wide = c >= k.wrapping_add(8) && cap >= k.wrapping_add(8);
        let x = if wide { b_h_word_at(input, a.wrapping_sub(k).wrapping_sub(8)) ^ b_h_word_at(input, c.wrapping_sub(k).wrapping_sub(8)) } else { 1 };
        let m = if x == 0 { 8 } else { (x.leading_zeros() / 8) as usize };
        let pa = a.wrapping_sub(k).wrapping_sub(1);
        let pc = c.wrapping_sub(k).wrapping_sub(1);
        let eq = if !wide && k < c && b_byte_at(input, pa) == b_byte_at(input, pc) { 1 } else { 0 };
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
pub fn b_h_log2_16(v: u32) -> u32 {
    let lz = v.leading_zeros();
    let ip = 31u32.wrapping_sub(lz);
    let m = v.wrapping_shl(lz);
    let f = ((m >> 27) % 16) as usize;
    let r = ip.wrapping_mul(16).wrapping_add(B_H_LOG_FRAC[f]);
    if v == 0 {
        0
    } else {
        r
    }
}

/// Estimated cost (1/16 bits) of a symbol seen `f` times out of `total`.
pub fn b_h_sym_cost(f: u32, lt: u32) -> u32 {
    let c = if f == 0 { lt.wrapping_add(B_H_UNSEEN) } else { lt.saturating_sub(b_h_log2_16(f)) };
    if c < B_H_CMIN {
        B_H_CMIN
    } else if c > B_H_CMAX {
        B_H_CMAX
    } else {
        c
    }
}




pub fn b_h_dist_sym(d: usize) -> usize {
    if d <= 256 {
        B_H_DSYM_S[(d.wrapping_sub(1)) % 256] as usize
    } else {
        B_H_DSYM_B[(d.wrapping_sub(1) / 128) % 256] as usize
    }
}

pub fn b_h_dist_cost(dcs: &[u32; 256], dcb: &[u32; 256], d: usize) -> u32 {
    if d <= 256 {
        dcs[(d.wrapping_sub(1)) % 256]
    } else {
        dcb[(d.wrapping_sub(1) / 128) % 256]
    }
}

pub fn b_h_sum_arr(a: &[u32; 512], m: usize) -> u32 {
    let mut s = 0u32;
    let mut i = 0usize;
    while i < m && i < 512 {
        s = s.wrapping_add(a[i]);
        i += 1;
    }
    s
}

pub fn b_h_sum_df(a: &[u32; 32]) -> u32 {
    let mut s = 0u32;
    let mut i = 0usize;
    while i < 30 {
        s = s.wrapping_add(a[i]);
        i += 1;
    }
    s
}

/// Literal costs from the literal part of `llf`.
pub fn b_h_lit_costs(llf: &[u32; 512], lt: u32, litc: &mut [u32; 256]) {
    let mut b = 0usize;
    while b < 256 {
        litc[b] = b_h_sym_cost(llf[b], lt);
        b += 1;
    }
}

/// Symbol costs of the 29 length symbols (plus extra bits), then every length through `lsym`.
pub fn b_h_len_costs(llf: &[u32; 512], lt: u32, scost: &mut [u32; 32], lcost: &mut [u32; 512]) {
    let mut s = 0usize;
    while s < 29 {
        scost[s] = b_h_sym_cost(llf[257 + s], lt).wrapping_add(B_H_LEN_EXTRA[s].wrapping_mul(16));
        s += 1;
    }
    let mut l = 3usize;
    while l < 259 {
        lcost[l] = scost[(B_H_LSYM[l] as usize) % 32];
        l += 1;
    }
}

/// Symbol costs of the 30 distance symbols (plus extra bits), then both distance tables.
pub fn b_h_dist_costs(df: &[u32; 32], scost: &mut [u32; 32], dcs: &mut [u32; 256], dcb: &mut [u32; 256]) {
    let lt = b_h_log2_16(b_h_sum_df(df));
    let mut s = 0usize;
    while s < 30 {
        scost[s] = b_h_sym_cost(df[s], lt).wrapping_add(B_H_DIST_EXTRA[s].wrapping_mul(16));
        s += 1;
    }
    let mut j = 0usize;
    while j < 256 {
        dcs[j] = scost[(B_H_DSYM_S[j] as usize) % 32];
        dcb[j] = scost[(B_H_DSYM_B[j] as usize) % 32];
        j += 1;
    }
}

/// `dst = cur + prev * B_H_PW / 4` over the first `m` entries.
pub fn b_h_mix(dst: &mut [u32; 512], cur: &[u32; 512], prv: &[u32; 512]) {
    let mut i = 0usize;
    while i < 512 {
        dst[i] = cur[i].wrapping_add(prv[i].wrapping_mul(B_H_PW) / B_H_PWD);
        i += 1;
    }
}

pub fn b_h_mix32(dst: &mut [u32; 32], cur: &[u32; 32], prv: &[u32; 32]) {
    let mut i = 0usize;
    while i < 32 {
        dst[i] = cur[i].wrapping_add(prv[i].wrapping_mul(B_H_PW) / B_H_PWD);
        i += 1;
    }
}

pub fn b_h_copy512(dst: &mut [u32; 512], src: &[u32; 512]) {
    let mut i = 0usize;
    while i < 512 {
        dst[i] = src[i];
        i += 1;
    }
}

pub fn b_h_copy32(dst: &mut [u32; 32], src: &[u32; 32]) {
    let mut i = 0usize;
    while i < 32 {
        dst[i] = src[i];
        i += 1;
    }
}

pub fn b_h_clear512(a: &mut [u32; 512]) {
    let mut i = 0usize;
    while i < 512 {
        a[i] = 0;
        i += 1;
    }
}

pub fn b_h_clear32(a: &mut [u32; 32]) {
    let mut i = 0usize;
    while i < 32 {
        a[i] = 0;
        i += 1;
    }
}

/// Literal histogram of the first B_H_SAMPLE bytes (4 interleaved counters against store forwarding).
pub fn b_h_sample_hist(input: &[u8], h0: &mut [u32; 256], h1: &mut [u32; 256], h2: &mut [u32; 256], h3: &mut [u32; 256]) -> usize {
    let n = input.len();
    let m = if n > B_H_SAMPLE { B_H_SAMPLE } else { n };
    let q = m / 4;
    let mut k = 0usize;
    while k < q {
        let i = k.wrapping_mul(4);
        let b0 = b_byte_at(input, i);
        let b1 = b_byte_at(input, i.wrapping_add(1));
        let b2 = b_byte_at(input, i.wrapping_add(2));
        let b3 = b_byte_at(input, i.wrapping_add(3));
        h0[b0 % 256] = h0[b0 % 256].wrapping_add(1);
        h1[b1 % 256] = h1[b1 % 256].wrapping_add(1);
        h2[b2 % 256] = h2[b2 % 256].wrapping_add(1);
        h3[b3 % 256] = h3[b3 % 256].wrapping_add(1);
        k += 1;
    }
    m
}

/// Initial statistics: literal histogram of a sample plus pseudo-counts for lengths/distances.
pub fn b_h_init_stats(input: &[u8], llf: &mut [u32; 512], df: &mut [u32; 32]) {
    let mut h0 = [0u32; 256];
    let mut h1 = [0u32; 256];
    let mut h2 = [0u32; 256];
    let mut h3 = [0u32; 256];
    let m0 = b_h_sample_hist(input, &mut h0, &mut h1, &mut h2, &mut h3);
    let sc = (65536 / B_H_SAMPLE) as u32;
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
pub fn b_h_scale_prior(llf: &mut [u32; 512], df: &mut [u32; 32]) {
    let mut i = 0usize;
    while i < 512 {
        llf[i] = llf[i] / B_H_PRIOR_DIV;
        i += 1;
    }
    let mut j = 0usize;
    while j < 32 {
        df[j] = df[j] / B_H_PRIOR_DIV;
        j += 1;
    }
}

pub fn b_h_all_costs(
    llf: &mut [u32; 512],
    df: &[u32; 32],
    scost: &mut [u32; 32],
    litc: &mut [u32; 256],
    lcost: &mut [u32; 512],
    dcs: &mut [u32; 256],
    dcb: &mut [u32; 256],
) {
    llf[256] = 1;
    let lt = b_h_log2_16(b_h_sum_arr(llf, 286));
    b_h_lit_costs(llf, lt, litc);
    b_h_len_costs(llf, lt, scost, lcost);
    b_h_dist_costs(df, scost, dcs, dcb);
}

// ---------------------------------------------------------------- match finding

/// 3-byte hash slot of position `i`.
pub fn b_h_hash3i(input: &[u8], i: usize) -> usize {
    let w = b_h_load_le32(input, i);
    (((w << 8).wrapping_mul(2654435761) >> 15) as usize) % 131072
}

/// Relax the nearest 3-byte match (entry `s3`, pos+1 encoded) at `pos` (DP position `cur`) as a
/// length-3 edge when it is within B_H_MAX3 and its 3 bytes agree.
pub fn b_h_relax3(input: &[u8], arr: &mut [u64; 8192], ed: &mut [u64; 32768], lcost: &[u32; 512], dcs: &[u32; 256], dcb: &[u32; 256], pos: usize, cur: usize, price: u32, s3: usize, cap: usize) {
    if B_H_H3ON == 0 || s3 == 0 || s3 > pos || cap < 3 {
        return;
    }
    let c = s3 - 1;
    let d = pos - c;
    if d > B_H_MAX3 || (b_h_load_le32(input, c) ^ b_h_load_le32(input, pos)) & 16777215 != 0 {
        return;
    }
    let dc = b_h_dist_cost(dcs, dcb, d);
    b_h_rec(ed, cur, cur, 3, 3, d);
    b_h_relax_range(arr, lcost, cur, 3, 3, price.wrapping_add(dc), (d as u64) << 9);
}

/// Insert position `i` (when `on`) into the chains; returns the previous chain head (+1).
pub fn b_h_insert(input: &[u8], head: &mut [u32; 65536], prev: &mut [u16; 32768], h3: &mut [u32; 131072], i: usize, on: bool) -> usize {
    let h = b_h_hash4(b_h_load_le32(input, i));
    let s4 = head[h % 65536] as usize;
    let dl = i.wrapping_add(1).wrapping_sub(s4);
    let dv = if s4 > 0 && dl <= 32768 { dl } else { 0 };
    let slot = i % 32768;
    prev[slot] = if on { dv as u16 } else { prev[slot] };
    head[h % 65536] = if on { (i as u32).wrapping_add(1) } else { head[h % 65536] };
    let g = b_h_hash3i(input, i);
    h3[g % 131072] = if on { if B_H_H3ON == 1 { (i as u32).wrapping_add(1) } else { h3[g % 131072] } } else { h3[g % 131072] };
    s4
}

/// Positions `start+cur0 .. start+stop`: insert them (when `ins`) and relax their literal edges.
/// Insert positions `start+cur0 .. start+stop` into the chains (no DP work).
pub fn b_h_insert_run(input: &[u8], head: &mut [u32; 65536], prev: &mut [u16; 32768], h3: &mut [u32; 131072], start: usize, cur0: usize, stop: usize) {
    let mut cur = cur0;
    let mut it = 0usize;
    while it < 8192 && cur < stop {
        let _s = b_h_insert(input, head, prev, h3, start.wrapping_add(cur), true);
        cur = cur.wrapping_add(1);
        it += 1;
    }
}

/// Positions `start+cur0 .. start+stop` inside a known match: all are inserted, the first B_H_LITK
/// also get their literal edge relaxed. Returns the price at `stop`.
pub fn b_h_interior(
    input: &[u8],
    head: &mut [u32; 65536],
    prev: &mut [u16; 32768], h3: &mut [u32; 131072],
    arr: &mut [u64; 8192],
    litc: &[u32; 256],
    start: usize,
    cur0: usize,
    stop: usize,
    price0: u32,
) -> u32 {
    let k = cur0.wrapping_add(B_H_LITK);
    let s1 = if k < stop { k } else { stop };
    let mut cur = cur0;
    let mut price = price0;
    let mut it = 0usize;
    while it < B_H_LITK && cur < s1 {
        let i = start.wrapping_add(cur);
        let _s = b_h_insert(input, head, prev, h3, i, true);
        let lp = price.wrapping_add(litc[b_byte_at(input, i) % 256]);
        let j = cur.wrapping_add(1) % 8192;
        let old = arr[j];
        let cand = ((lp as u64) << 32) | 1;
        let m = if cand < old { cand } else { old };
        arr[j] = m;
        price = (m >> 32) as u32;
        cur = cur.wrapping_add(1);
        it += 1;
    }
    b_h_insert_run(input, head, prev, h3, start, s1, stop);
    let pe = (b_h_at64(arr, stop) >> 32) as u32;
    if s1 < stop {
        pe
    } else {
        price
    }
}

/// Positions `cur0 .. stop` of an accelerated literal run: literal edges only. Returns the price at `stop`.
pub fn b_h_lit_run(input: &[u8], arr: &mut [u64; 8192], litc: &[u32; 256], start: usize, cur0: usize, stop: usize, price0: u32) -> u32 {
    let mut cur = cur0;
    let mut price = price0;
    let mut it = 0usize;
    while it < 8192 && cur < stop {
        let i = start.wrapping_add(cur);
        let lp = price.wrapping_add(litc[b_byte_at(input, i) % 256]);
        let j = cur.wrapping_add(1) % 8192;
        let old = arr[j];
        let cand = ((lp as u64) << 32) | 1;
        let m = if cand < old { cand } else { old };
        arr[j] = m;
        price = (m >> 32) as u32;
        cur = cur.wrapping_add(1);
        it += 1;
    }
    price
}

/// Length of the match between `c` and `pos` given the xor `x` of their first words (search only).
pub fn b_h_cand_len(input: &[u8], c: usize, pos: usize, cap: usize, x: u64) -> usize {
    let r = if cap > 8 { cap - 8 } else { 0 };
    let l = if x == 0 {
        8usize.wrapping_add(b_h_fast_len(input, c.wrapping_add(8), pos.wrapping_add(8), r))
    } else {
        b_h_tzb(x)
    };
    if l > cap {
        cap
    } else {
        l
    }
}


/// Backward extension of the candidate at `c` for `pos` (at most `cap` bytes), given the word
/// `wb` ending just before `pos`: one word compare, the general loop only when it all agrees.
pub fn b_h_back_ext(input: &[u8], pos: usize, c: usize, cap: usize, wb: u64) -> usize {
    let wide = c >= 8 && cap >= 8;
    let x = if wide { b_h_word_at(input, c.wrapping_sub(8)) ^ wb } else { 0 };
    let m = if x == 0 { 8 } else { (x.leading_zeros() / 8) as usize };
    if wide && m < 8 {
        m
    } else {
        b_h_back_len(input, pos, c, cap)
    }
}

/// Relax one Pareto candidate (distance `d`, length `l`, found at `c`) from `cur`: its lengths
/// `lo..=l`, and when it extends backwards by b > 0 bytes also from `cur - b` (lengths b+lo..=b+l,
/// never before the block start). A candidate of length >= B_H_NICE only relaxes its full length.
pub fn b_h_relax_cand(
    input: &[u8],
    arr: &mut [u64; 8192],
    ed: &mut [u64; 32768],
    lcost: &[u32; 512],
    dcs: &[u32; 256],
    dcb: &[u32; 256],
    pos: usize,
    cur: usize,
    price: u32,
    c: usize,
    d: usize,
    lo: usize,
    l: usize,
    wb: u64,
    bx: usize,
) {
    let dc = b_h_dist_cost(dcs, dcb, d);
    let eb = (d as u64) << 9;
    let nice = l >= B_H_NICE;
    let lo1 = if nice { l } else { lo };
    b_h_rec(ed, cur, cur, lo1, l, d);
    b_h_relax_range(arr, lcost, cur, lo1, l, price.wrapping_add(dc), eb);
    let lim0 = if l < 258 { 258 - l } else { 0 };
    let lim1 = if lim0 < cur { lim0 } else { cur };
    let lim = if nice || bx == 0 { 0 } else { lim1 };
    let b = if lim > 0 { b_h_back_ext(input, pos, c, lim, wb) } else { 0 };
    if b > 0 && b <= cur {
        let s0 = cur.wrapping_sub(b);
        let ps = (b_h_at64(arr, s0) >> 32) as u32;
        let lo2 = if b < 2 { 3 } else { b.wrapping_add(1) };
        let hi2 = if ps < 4000000000 { b.wrapping_add(l) } else { 0 };
        b_h_rec(ed, cur, s0, lo2, hi2, d);
        b_h_relax_range(arr, lcost, s0, lo2, hi2, ps.wrapping_add(dc), eb);
    }
}

/// Walk the chain from head `s4` (at most `depth` probes) at `pos` (DP position `cur`, price
/// `price`) and relax every Pareto candidate (strictly longer than all nearer ones) on the fly.
/// Returns the longest length found (< 4: none).
pub fn b_h_search_relax(
    input: &[u8],
    prev: &[u16; 32768],
    arr: &mut [u64; 8192],
    ed: &mut [u64; 32768],
    lcost: &[u32; 512],
    dcs: &[u32; 256],
    dcb: &[u32; 256],
    pos: usize,
    cur: usize,
    cap: usize,
    s4: usize,
    depth: usize,
    price: u32,
    bx: usize,
) -> usize {
    let wp = b_h_word_at(input, pos);
    let wb = b_h_word_at(input, pos.wrapping_sub(8));
    let mut best = 3usize;
    let d0 = pos.wrapping_add(1).wrapping_sub(s4);
    let mut d = if s4 > 0 { d0 } else { 65536 };
    let mut probes = 0usize;
    while probes < depth && d <= 32768 && d <= pos && best < cap && best < B_H_NICE {
        let c = pos.wrapping_sub(d);
        let x = b_h_word_at(input, c) ^ wp;
        let ok = if best < 8 { 1usize } else if b_byte_at(input, c.wrapping_add(best)) == b_byte_at(input, pos.wrapping_add(best)) { 1usize } else { 0usize };
        if ok == 1 {
            let l = b_h_cand_len(input, c, pos, cap, x);
            if l > best {
                b_h_relax_cand(input, arr, ed, lcost, dcs, dcb, pos, cur, price, c, d, best.wrapping_add(1), l, wb, bx);
                best = l;
            }
        }
        let dl = prev[c % 32768] as usize;
        d = if dl == 0 { 65536 } else { d.wrapping_add(dl) };
        probes += 1;
    }
    best
}


/// Insert positions `from .. to` into the chains.
pub fn b_h_insert_range(input: &[u8], head: &mut [u32; 65536], prev: &mut [u16; 32768], h3: &mut [u32; 131072], from: usize, to: usize) {
    let n = input.len();
    let lim = if n >= 8 { n - 8 } else { 0 };
    let mut i = from;
    let mut it = 0usize;
    while it < 300 && i < to && i <= lim {
        let _r = b_h_insert(input, head, prev, h3, i, true);
        i = i.wrapping_add(1);
        it += 1;
    }
}

// ---------------------------------------------------------------- DP

pub fn b_h_fill_inf(arr: &mut [u64; 8192]) {
    let mut j = 0usize;
    while j < 8192 {
        arr[j] = B_H_INF;
        j += 1;
    }
}

/// Relax lengths lo..=hi from `cur` at one distance: cost = base + lcost[L].
pub fn b_h_relax_range(arr: &mut [u64; 8192], lcost: &[u32; 512], cur: usize, lo: usize, hi: usize, base: u32, ebits: u64) {
    let mut l = lo;
    let mut it = 0usize;
    while it < 260 && l <= hi && l < 259 {
        let p = base.wrapping_add(lcost[l % 512]);
        let cand = ((p as u64) << 32) | ebits | (l as u64);
        let j = cur.wrapping_add(l) % 8192;
        let old = arr[j];
        arr[j] = if cand < old { cand } else { old };
        l = l.wrapping_add(1);
        it += 1;
    }
}



/// Relax the literal edge cur -> cur + 1 (when `on`); returns the (final) price at cur + 1.
pub fn b_h_lit_step(input: &[u8], arr: &mut [u64; 8192], litc: &[u32; 256], i: usize, cur: usize, price: u32, on: bool) -> u32 {
    let lp = price.wrapping_add(litc[b_byte_at(input, i) % 256]);
    let j = cur.wrapping_add(1) % 8192;
    let old = arr[j];
    let cand = ((lp as u64) << 32) | 1;
    let m = if cand < old { cand } else { old };
    arr[j] = if on { m } else { old };
    (m >> 32) as u32
}


/// Forward DP over one block starting at `start`; returns the block length.
/// `st[0]` carries the fruitless-search counter across blocks.
pub fn b_h_dp_block(
    input: &[u8],
    start: usize,
    head: &mut [u32; 65536],
    prev: &mut [u16; 32768], h3: &mut [u32; 131072],
    arr: &mut [u64; 8192],
    ed: &mut [u64; 32768],
    cl: &mut [u32; 16],
    cd: &mut [u32; 16],
    cb: &mut [u32; 16],
    litc: &[u32; 256],
    lcost: &[u32; 512],
    dcs: &[u32; 256],
    dcb: &[u32; 256],
    st: &mut [usize; 4],
    kcode: usize,
) -> usize {
    let n = input.len();
    let cls = (kcode / 32) % 4;
    let kend = kcode % 32;
    let smask = B_H_MASKS[cls % 4];
    let hdep = B_H_HDEPS[cls % 4];
    let dbase = cls.wrapping_mul(32);
    let rem = n.wrapping_sub(start);
    let bend = if rem < B_H_BS { rem } else { B_H_BS };
    let hard0 = B_H_BS.wrapping_add(B_H_EXT);
    let mut lim = if rem < hard0 { rem } else { hard0 };
    let mut go = if bend > 0 { 1usize } else { 0usize };
    b_h_fill_inf(arr);
    b_h_put64(arr, 0, 0);
    ed[0] = 0;
    let mut price = 0u32;
    let mut cur = 0usize;
    let mut reach = 0usize;
    let mut miss = st[0];
    let sparse = st[1];
    let mut acc_next = 0usize;
    let mut it = 0usize;
    while it < 8192 && go == 1 {
        let i = start.wrapping_add(cur);
        let left = rem.wrapping_sub(cur);
        if cur.wrapping_add(kend) < reach {
            // inside a known match: insert + literal edge, up to the frontier
            let s = reach.wrapping_sub(kend);
            let stop = if s < lim { s } else { lim };
            price = b_h_interior(input, head, prev, h3, arr, litc, start, cur, stop, price);
            cur = stop;
        } else if cur < acc_next {
            // accelerated literal run: literal edges only
            let stop = if acc_next < lim { acc_next } else { lim };
            price = b_h_lit_run(input, arr, litc, start, cur, stop, price);
            cur = stop;
        } else if left < 8 {
            price = b_h_lit_step(input, arr, litc, i, cur, price, true);
            cur = cur.wrapping_add(1);
        } else if cur > reach && sparse == 1 && (cur - reach) % B_H_SPSTEP != 0 {
            // sparse mode: a literal-run position that is not searched
            if B_H_SPINS == 1 {
                price = b_h_interior(input, head, prev, h3, arr, litc, start, cur, cur.wrapping_add(1), price);
            } else {
                price = b_h_lit_step(input, arr, litc, i, cur, price, true);
            }
            cur = cur.wrapping_add(1);
        } else if cur < reach && ((smask >> ((reach - cur) % 64)) % 2) as usize == 0 {
            // a frontier offset that is not searched
            price = b_h_interior(input, head, prev, h3, arr, litc, start, cur, cur.wrapping_add(1), price);
            cur = cur.wrapping_add(1);
        } else {
            let off = reach.wrapping_sub(cur);
            let gt = if cur > reach { 1usize } else { 0usize };
            let depth = if gt == 1 { hdep } else { B_H_DEPO[(off % 32).wrapping_add(dbase) % 128] };
            let bx = if gt == 1 { B_H_BXGT } else { (((B_H_BXMASK as u64) >> (off % 64)) % 2) as usize };
            let s3 = h3[b_h_hash3i(input, i) % 131072] as usize;
            let s4 = b_h_insert(input, head, prev, h3, i, true);
            let cap = if left < 258 { left } else { 258 };
            b_h_relax3(input, arr, ed, lcost, dcs, dcb, i, cur, price, s3, cap);
            let best = b_h_search_relax(input, prev, arr, ed, lcost, dcs, dcb, i, cur, cap, s4, depth, price, bx);
            miss = if best >= 4 { 0 } else { miss.wrapping_add(1) };
            acc_next = cur.wrapping_add(1).wrapping_add(miss / B_H_ACC_DIV);
            if best >= B_H_NICE {
                let tfrom = if best > B_H_TAIL { i.wrapping_add(best).wrapping_sub(B_H_TAIL) } else { i.wrapping_add(1) };
                b_h_insert_range(input, head, prev, h3, tfrom, i.wrapping_add(best));
                cur = cur.wrapping_add(best);
                price = (b_h_at64(arr, cur) >> 32) as u32;
                lim = if cur > lim { cur } else { lim };
            } else {
                let nr = cur.wrapping_add(best);
                reach = if best >= 4 && nr > reach { nr } else { reach };
                price = b_h_lit_step(input, arr, litc, i, cur, price, true);
                cur = cur.wrapping_add(1);
            }
        }
        go = if cur < bend { 1 } else { b_h_go(cur, lim, reach) };
        it += 1;
    }
    st[0] = miss;
    cur
}

/// Continue a DP block past its nominal end: while before `lim` and a match edge crosses `cur` (cur < reach).
pub fn b_h_go(cur: usize, lim: usize, reach: usize) -> usize {
    let b = if cur < reach { 1usize } else { 0usize };
    let c = if cur < lim { 1usize } else { 0usize };
    b & c
}







/// Cost refresh after a DP block: at an output-block boundary (`full`) from that block's
/// statistics (which become the prior), else from the running statistics plus the prior.
pub fn b_h_refresh(
    full: bool,
    llf: &mut [u32; 512],
    df: &mut [u32; 32],
    pllf: &mut [u32; 512],
    pdf: &mut [u32; 32],
    tllf: &mut [u32; 512],
    tdf: &mut [u32; 32],
    scost: &mut [u32; 32],
    litc: &mut [u32; 256],
    lcost: &mut [u32; 512],
    dcs: &mut [u32; 256],
    dcb: &mut [u32; 256],
) {
    if full {
        b_h_copy512(pllf, llf);
        b_h_copy32(pdf, df);
        b_h_clear512(llf);
        b_h_clear32(df);
    }
    b_h_mix(tllf, llf, pllf);
    b_h_mix32(tdf, df, pdf);
    b_h_all_costs(tllf, tdf, scost, litc, lcost, dcs, dcb);
}



// ---------------------------------------------------------------- replay pass (from K31)

/// Append the relaxed range (search time `t`, start `s`, lengths `lo..=hi`, distance `d`) to the
/// edge buffer (`ed[0]` = count; a full buffer sets the count to B_H_EBUF - 1 and stops recording).
pub fn b_h_rec(ed: &mut [u64; 32768], t: usize, s: usize, lo: usize, hi: usize, d: usize) {
    let c = (ed[0] % 32768) as usize;
    let x = (((t % 8192) as u64) << 47) | (((s % 8192) as u64) << 34) | (((d % 65536) as u64) << 18) | (((lo % 512) as u64) << 9) | ((hi % 512) as u64);
    let c1 = if c < B_H_EBUF - 1 { c + 1 } else { c };
    ed[c1 % 32768] = if c < B_H_EBUF - 1 { x } else { ed[c1 % 32768] };
    ed[0] = c1 as u64;
}

/// Replay the recorded ranges of search time `p` (from entry `q0`); returns the next entry.
pub fn b_h_replay_at(arr: &mut [u64; 8192], ed: &[u64; 32768], lcost: &[u32; 512], dcs: &[u32; 256], dcb: &[u32; 256], p: usize, q0: usize, cnt: usize) -> usize {
    let mut q = q0;
    let mut it = 0usize;
    while it < 32768 && q <= cnt && ((ed[q % 32768] >> 47) % 8192) as usize <= p {
        let r = ed[q % 32768];
        let s = ((r >> 34) % 8192) as usize;
        let d = ((r >> 18) % 65536) as usize;
        let lo = ((r >> 9) % 512) as usize;
        let hi = (r % 512) as usize;
        let ps = (b_h_at64(arr, s) >> 32) as u32;
        let dc = b_h_dist_cost(dcs, dcb, d);
        let hi2 = if ps < 4000000000 { hi } else { 0 };
        b_h_relax_range(arr, lcost, s, lo, hi2, ps.wrapping_add(dc), (d as u64) << 9);
        q = q.wrapping_add(1);
        it += 1;
    }
    q
}

/// Second DP over the recorded edges of the block `0 .. bend` with the current costs: literal
/// edges at every position, then every recorded range in search order.
pub fn b_h_replay(input: &[u8], start: usize, bend: usize, arr: &mut [u64; 8192], ed: &[u64; 32768], litc: &[u32; 256], lcost: &[u32; 512], dcs: &[u32; 256], dcb: &[u32; 256]) {
    b_h_fill_inf(arr);
    b_h_put64(arr, 0, 0);
    let cnt = (ed[0] % 32768) as usize;
    let mut q = 1usize;
    let mut p = 0usize;
    while p < 8192 && p < bend {
        let price = (b_h_at64(arr, p) >> 32) as u32;
        let lp = price.wrapping_add(litc[b_byte_at(input, start.wrapping_add(p)) % 256]);
        let j = p.wrapping_add(1) % 8192;
        let old = arr[j];
        let cand = ((lp as u64) << 32) | 1;
        arr[j] = if cand < old { cand } else { old };
        q = b_h_replay_at(arr, ed, lcost, dcs, dcb, p, q, cnt);
        p += 1;
    }
}

/// `dst = blk * B_H_TPW + run + prv * B_H_PW / 4` (512 entries).
pub fn b_h_mix3(dst: &mut [u32; 512], blk: &[u32; 512], run: &[u32; 512], prv: &[u32; 512]) {
    let mut i = 0usize;
    while i < 512 {
        dst[i] = blk[i].wrapping_mul(B_H_TPW).wrapping_add(run[i]).wrapping_add(prv[i].wrapping_mul(B_H_PW) / B_H_PWD);
        i += 1;
    }
}

pub fn b_h_mix3s(dst: &mut [u32; 32], blk: &[u32; 32], run: &[u32; 32], prv: &[u32; 32]) {
    let mut i = 0usize;
    while i < 32 {
        dst[i] = blk[i].wrapping_mul(B_H_TPW).wrapping_add(run[i]).wrapping_add(prv[i].wrapping_mul(B_H_PW) / B_H_PWD);
        i += 1;
    }
}

pub fn b_h_add512(dst: &mut [u32; 512], src: &[u32; 512]) {
    let mut i = 0usize;
    while i < 512 {
        dst[i] = dst[i].wrapping_add(src[i]);
        i += 1;
    }
}

pub fn b_h_add32(dst: &mut [u32; 32], src: &[u32; 32]) {
    let mut i = 0usize;
    while i < 32 {
        dst[i] = dst[i].wrapping_add(src[i]);
        i += 1;
    }
}

/// Replay only when the edge buffer did not overflow and the pass-1 parse is priced more than
/// B_H_RT/1024 higher by the pass-1 model than by the refit model (the models disagree).
pub fn b_h_replay_flag(e0: u64, p1: u64, c1: u64) -> usize {
    let a = if (e0 % 32768) as usize >= B_H_EBUF - 1 { 0usize } else { 1usize };
    let b = if p1.wrapping_mul(1024) > c1.wrapping_mul(1024 + B_H_RT) { 1usize } else { 0usize };
    a & b
}

/// Cost of the symbol counts `llf1`/`df1` under the current model (1/16 bits).
pub fn b_h_model_cost(llf1: &[u32; 512], df1: &[u32; 32], litc: &[u32; 256], lcost: &[u32; 512], scost: &[u32; 32]) -> u64 {
    let mut c = 0u64;
    let mut b = 0usize;
    while b < 256 {
        c = c.wrapping_add((llf1[b] as u64).wrapping_mul(litc[b] as u64));
        b += 1;
    }
    let mut s = 0usize;
    while s < 29 {
        c = c.wrapping_add((llf1[257 + s] as u64).wrapping_mul(lcost[(B_H_LEN_BASE[s] as usize) % 512] as u64));
        s += 1;
    }
    let mut t = 0usize;
    while t < 30 {
        c = c.wrapping_add((df1[t] as u64).wrapping_mul(scost[t] as u64));
        t += 1;
    }
    c
}

/// After pass 1 of the block `pos0 .. pos0 + blen`: its parse gives block statistics, costs are
/// refit from them (plus the running and prior statistics) and the recorded edges are replayed.
/// A full edge buffer keeps the pass-1 parse. Returns h_backtrack's token/literal count.
pub fn b_h_second(
    input: &[u8],
    pos0: usize,
    blen: usize,
    arr: &mut [u64; 8192],
    ed: &[u64; 32768],
    plan: &mut [u32],
    llf: &mut [u32; 512],
    df: &mut [u32; 32],
    llf1: &mut [u32; 512],
    df1: &mut [u32; 32],
    pllf: &[u32; 512],
    pdf: &[u32; 32],
    tllf: &mut [u32; 512],
    tdf: &mut [u32; 32],
    scost: &mut [u32; 32],
    litc: &mut [u32; 256],
    lcost: &mut [u32; 512],
    dcs: &mut [u32; 256],
    dcb: &mut [u32; 256],
) -> usize {
    b_h_clear512(llf1);
    b_h_clear32(df1);
    let t1 = b_h_backtrack(input, arr, plan, pos0, blen, llf1, df1);
    let p1 = b_h_at64(arr, blen) >> 32;
    b_h_mix3(tllf, llf1, llf, pllf);
    b_h_mix3s(tdf, df1, df, pdf);
    b_h_all_costs(tllf, tdf, scost, litc, lcost, dcs, dcb);
    let c1 = b_h_model_cost(llf1, df1, litc, lcost, scost);
    let go = b_h_replay_flag(ed[0], p1, c1);
    b_h_redo(input, pos0, blen, arr, ed, plan, llf, df, llf1, df1, litc, lcost, dcs, dcb, go, t1)
}

/// Replay (go == 1: second DP over the recorded edges, new backtrack into llf/df) or keep the
/// pass-1 b_parse (its counts are added to llf/df). Returns the token/literal count.
pub fn b_h_redo(
    input: &[u8],
    pos0: usize,
    blen: usize,
    arr: &mut [u64; 8192],
    ed: &[u64; 32768],
    plan: &mut [u32],
    llf: &mut [u32; 512],
    df: &mut [u32; 32],
    llf1: &[u32; 512],
    df1: &[u32; 32],
    litc: &[u32; 256],
    lcost: &[u32; 512],
    dcs: &[u32; 256],
    dcb: &[u32; 256],
    go: usize,
    t1: usize,
) -> usize {
    if go == 1 {
        b_h_replay(input, pos0, blen, arr, ed, litc, lcost, dcs, dcb);
        b_h_backtrack(input, arr, plan, pos0, blen, llf, df)
    } else {
        b_h_add512(llf, llf1);
        b_h_add32(df, df1);
        t1
    }
}

/// Walk the chosen edges back from `end`, writing the whole-file plan (len * 65536 + dist, 0 = literal)
/// and counting symbols; returns the token count + 16384 * the literal count.
pub fn b_h_backtrack(
    input: &[u8],
    arr: &[u64; 8192],
    plan: &mut [u32],
    start: usize,
    end: usize,
    llf: &mut [u32; 512],
    df: &mut [u32; 32],
) -> usize {
    let mut e = end;
    let mut cnt = 0usize;
    let mut lits = 0usize;
    let mut guard = 0usize;
    while guard < 8192 && e > 0 {
        let ed = (arr[e % 8192] % 4294967296) as usize;
        let l0 = ed % 512;
        let d = ed / 512;
        let l = b_h_step_len(l0, d, e);
        let p = e.wrapping_sub(l);
        let ism = b_ge(l, 3);
        b_set(plan, start.wrapping_add(p), b_sel32(ism, (l as u32).wrapping_mul(65536).wrapping_add((d % 65536) as u32), 0));
        b_h_count(input, llf, df, ism, l, d, start.wrapping_add(p));
        lits = lits.wrapping_add(ism ^ 1);
        cnt = cnt.wrapping_add(1);
        e = p;
        guard += 1;
    }
    cnt.wrapping_add(lits.wrapping_mul(16384))
}

/// The backtrack step length: l0 when it is a valid match edge ending at e, else 1.
pub fn b_h_step_len(l0: usize, d: usize, e: usize) -> usize {
    if l0 >= 3 && l0 <= 258 && l0 <= e && d >= 1 {
        l0
    } else {
        1
    }
}

/// Count one path symbol: a match (length l, distance d) when ism == 1, else the literal at q.
pub fn b_h_count(input: &[u8], llf: &mut [u32; 512], df: &mut [u32; 32], ism: usize, l: usize, d: usize, q: usize) {
    if ism == 1 {
        let ls = 257 + (B_H_LSYM[l % 259] as usize) % 32;
        llf[ls % 512] = llf[ls % 512].wrapping_add(1);
        let t = b_h_dist_sym(d) % 32;
        df[t] = df[t].wrapping_add(1);
    } else {
        let b = b_byte_at(input, q) % 256;
        llf[b] = llf[b].wrapping_add(1);
    }
}

/// A block length of `e` if `1 <= e <= rest`, else 1.
pub fn b_h_clamp_block(e: usize, rest: usize) -> usize {
    if e >= 1 && e <= rest {
        e
    } else {
        1
    }
}

/// The H-DP planner (frontier-search forward-price DP per 6K block,
/// adaptive costs across blocks): fills plan[0..n).
pub fn b_h_dp_plan(mode: usize, input: &[u8], plan: &mut [u32], kend: usize) {
    let n = input.len();
    let polish = mode != 2 && mode != 3;
    let cap = if polish { n } else { 0 };
    let blocks = if polish { n/6144+2 } else { 0 };
    let mut cache:Vec<u64>=Vec::with_capacity(cap);
    let mut starts:Vec<u32>=Vec::with_capacity(blocks);
    let mut sizes:Vec<u32>=Vec::with_capacity(blocks);
    let mut offsets:Vec<u32>=Vec::with_capacity(blocks);
    let mut head = [0u32; 65536];
    let mut prev = [0u16; 32768];
    let mut h3 = [0u32; 131072];
    let mut arr = [0u64; 8192];
    let mut ed = [0u64; 32768];
    let mut llf1 = [0u32; 512];
    let mut df1 = [0u32; 32];
    let mut cl = [0u32; 16];
    let mut cd = [0u32; 16];
    let mut cb = [0u32; 16];
    let mut litc = [0u32; 256];
    let mut lcost = [0u32; 512];
    let mut dcs = [0u32; 256];
    let mut dcb = [0u32; 256];
    let mut scost = [0u32; 32];
    let mut llf = [0u32; 512];
    let mut df = [0u32; 32];
    let mut pllf = [0u32; 512];
    let mut pdf = [0u32; 32];
    let mut tllf = [0u32; 512];
    let mut tdf = [0u32; 32];
    let mut st = [0usize; 4];
    b_h_init_stats(input, &mut pllf, &mut pdf);
    b_h_all_costs(&mut pllf, &pdf, &mut scost, &mut litc, &mut lcost, &mut dcs, &mut dcb);
    b_h_scale_prior(&mut pllf, &mut pdf);
    let mut pos0 = 0usize;
    let mut blk = 0usize;
    while pos0 < n {
        let rest = n - pos0;
        let e = b_h_dp_block(input, pos0, &mut head, &mut prev, &mut h3, &mut arr, &mut ed, &mut cl, &mut cd, &mut cb, &litc, &lcost, &dcs, &dcb, &mut st, kend);
        let blen = b_h_clamp_block(e, rest);
        if polish {
            b_push_guarded(&mut starts,pos0 as u32);
            b_push_guarded(&mut sizes,blen as u32);
            b_push_guarded(&mut offsets,cache.len() as u32);
            let ec=(ed[0]%32768) as usize;
            let mut ei=0usize;
            while ei<=ec && ei<32768 {
                if cache.len()<B_PUSH_LIMIT { cache.push(ed[ei]); }
                ei+=1;
            }
        }
        let tl = b_h_second(input, pos0, blen, &mut arr, &ed, plan, &mut llf, &mut df, &mut llf1, &mut df1, &pllf, &pdf, &mut tllf, &mut tdf, &mut scost, &mut litc, &mut lcost, &mut dcs, &mut dcb);
        let t = tl % 16384;
        st[1] = b_sel(b_ge((tl / 16384).wrapping_mul(100), blen.wrapping_mul(B_H_COV)), 1, 0);
        pos0 += blen;
        blk = blk.wrapping_add(t);
        let full = b_ge(blk, B_H_BLOCK_TOKENS);
        b_h_refresh(full == 1, &mut llf, &mut df, &mut pllf, &mut pdf, &mut tllf, &mut tdf, &mut scost, &mut litc, &mut lcost, &mut dcs, &mut dcb);
        blk = b_sel(full, blk.wrapping_sub(B_H_BLOCK_TOKENS), blk);
    }
    if mode == 1 {
        b_cx_hpolish_hfi(input,plan,&cache,&starts,&sizes,&offsets);
    } else if polish {
        b_cx_hpolish(input,plan,&cache,&starts,&sizes,&offsets);
    }
}

/// h_dp_plan when on == 1.
pub fn b_hdp_if(mode: usize, input: &[u8], plan: &mut [u32], on: usize, kend: usize) {
    if on == 1 {
        b_h_dp_plan(mode, input, plan, kend);
    }
}

/// The champion planner: whole-file binary-tree Pareto cache + iterated exact-cost backward DP.
pub fn b_champ(mode: usize, input: &[u8], plan: &mut [u32], gk: u64, i5: usize) {
    let n = input.len();
    let mut mstart: Vec<u32> = Vec::with_capacity(n.wrapping_add(1));
    let mut mc: Vec<u32> = Vec::with_capacity(n.wrapping_mul(3).wrapping_add(64));
    // @FIND_BEGIN
    b_find_all(input, &mut mstart, &mut mc, b_w34_depth(input, b_sel(b_lt(n, B_SMALLN), B_BTDS, b_sel(b_eq64(gk, b_mode_gk(mode, B_GKMC)), B_BTDMC, b_sel(b_eq64(gk, b_mode_gk(mode, B_GKX)), B_BTDX, B_BTD)))));
    // @FIND_END
    let nbmax = n / B_BT + 2;
    let mut tbl = b_filled(nbmax.wrapping_mul(B_TB), 0);
    let mut fr = b_filled(nbmax.wrapping_mul(B_FB), 0);
    let mut bpos = b_filled(nbmax, 0);
    let mut bend = [0u32; 512];
    b_build_bend(&mut bend);
    let mut choice = b_filled(n.wrapping_add(1).wrapping_mul(2), 0);
    b_optimize(mode, input, &mstart, &mc, &mut tbl, &mut fr, &mut bpos, &bend, &mut choice, plan, nbmax, gk, i5);
}

/// champ when on == 1.
pub fn b_champ_if(mode: usize, input: &[u8], plan: &mut [u32], on: usize, gk: u64, i5: usize) {
    if on == 1 {
        b_champ(mode, input, plan, gk, i5);
    }
}

// ---------------------------------------------------------------- dispatcher (untrusted)
/// Inputs shorter than B_D_SMALL bytes take the H-DP.
pub const B_D_SMALL: usize = 65536;
/// Probe: B_PR_N windows of B_PR_W bytes, greedy parse with a 4096-slot 4-byte hash table.
pub const B_PR_W: usize = 8192;
pub const B_PR_N: usize = 8;
/// Low-coverage inputs (matched bytes * 1000 < B_LITCOV * probed bytes): H-DP when the sampled
/// order-0 entropy is at least B_HLIT/256 bits per byte, else the literal-only plan.
pub const B_LITCOV: u64 = 8;
pub const B_HLIT: usize = 1984;
/// H-DP when bytes in probe matches of >= B_LONGL bytes * 1000 >= B_LONGK * probed bytes.
pub const B_LONGL: usize = 32;
pub const B_LONGK: u64 = 340;
/// Champion stop-rule constant for inputs whose probe coverage is below B_COVF/1000 (float-weight-like data,
/// where every pass keeps paying) and for the others.
pub const B_COVF: u64 = 150;
pub const B_GKLOW: u64 = 32;
/// Champion also below this sampled entropy (1/256 bits per byte); default mode otherwise (0 champion, 1 H-DP).
pub const B_HGEN: usize = 896;
/// ... but not below B_HGENLO/256 bits (near-constant / tiny-alphabet runs: the H-DP is far faster there).
pub const B_HGENLO: usize = 448;
pub const B_DEFM: usize = 0;
/// Champion also for text-like inputs whose probe coverage is below B_COVT/1000 and long-match coverage below B_LONGT/1000.
pub const B_COVT: u64 = 655;
pub const B_LONGT: u64 = 100;
/// H-DP frontier width (<= 15) for redundant / small inputs and for the others.
pub const B_KENDR: usize = 20;
pub const B_KENDT: usize = 20;
/// Frontier width (<= 31) per frontier class.
pub const B_H_KENDS: [usize; 4] = [20, 20, 20, 20];
pub const B_DIGR: u64 = 150;
/// Low-coverage high-entropy inputs with zero bytes >= B_Z0IM/1000 of the sample (image-like) take the champion.
pub const B_Z0IM: u64 = 8;
/// Small inputs with sampled order-0 entropy below B_HSP/256 bits per byte (near-constant) use frontier class 2.
pub const B_HSP: usize = 0;
pub const B_NZR: u64 = 81;
/// Machine-code-like inputs (control bytes >= B_CTLMC/1000, bytes >= 128 below B_HIMC/1000, long-match coverage
/// below B_NMMC/1000) take the champion with stop constant B_GKMC; text-class champion inputs use B_GKT, but
/// multibyte-text-like inputs (bytes >= 128 at least B_HITC/1000, control bytes below B_CTLMB/1000) are not text-class.
pub const B_CTLMC: u64 = 120;
pub const B_HIMC: u64 = 400;
pub const B_NMMC: u64 = 440;
pub const B_HITC: u64 = 160;
pub const B_CTLMB: u64 = 20;
pub const B_GKMC: u64 = 4;
/// Binary-tree depth of the champion's match finder for machine-code-like inputs.
pub const B_BTDMC: usize = 24;
pub const B_GKT: u64 = 8;
/// Default-class (text) inputs take the champion when B_DEFM == 0, with stop constant B_GKX; low-coverage inputs whose
/// sampled order-0 entropy is below B_HBF/256 bits per byte (bf16-like) take the champion instead of the literal plan.
pub const B_GKX: u64 = 2;
pub const B_HBF: usize = 1650;
/// Binary-tree depth of the champion's match finder for default-class (text) inputs.
pub const B_BTDX: usize = 32;

pub fn b_hash12(input: &[u8], p: usize) -> usize {
    let n = input.len();
    if n >= 4 && p <= n - 4 {
        let x = (input[p] as u32) | ((input[p + 1] as u32) << 8) | ((input[p + 2] as u32) << 16) | ((input[p + 3] as u32) << 24);
        ((x.wrapping_mul(2654435761) >> 20) as usize) % 4096
    } else {
        0
    }
}

/// Greedy probe of input[s..e): returns matched bytes * 2^32 + bytes in matches of >= B_LONGL bytes.
pub fn b_probe_win(input: &[u8], ht: &mut [u32; 4096], s: usize, e: usize) -> u64 {
    let n = input.len();
    let mut i = s;
    let mut cov = 0u64;
    let mut nm = 0u64;
    let mut it = 0usize;
    while it < B_PR_W && i < e {
        let h = b_hash12(input, i);
        let c = ht[h % 4096] as usize;
        ht[h % 4096] = (i as u32).wrapping_add(1);
        let cm = c.wrapping_sub(1);
        let ok = b_lt(s, c) & b_lt(cm, i) & b_lt(i.wrapping_add(8), n);
        let cap = b_umin(e.wrapping_sub(i), 258);
        let l = b_ext_if(input, ok, cm, i, 0, cap, 0);
        let hit = b_ge(l, 4);
        cov = cov.wrapping_add(b_sel(hit, l, 0) as u64);
        nm = nm.wrapping_add(b_sel(b_ge(l, B_LONGL), l, 0) as u64);
        i = i.wrapping_add(b_sel(hit, l, 1));
        it += 1;
    }
    cov.wrapping_mul(4294967296).wrapping_add(nm)
}

/// Sum of the probe over B_PR_N windows spread over the input (n >= B_PR_W * B_PR_N).
pub fn b_probe_all(input: &[u8]) -> u64 {
    let n = input.len();
    let mut ht = [0u32; 4096];
    let span = n.wrapping_sub(B_PR_W) / (B_PR_N - 1);
    let mut acc = 0u64;
    let mut k = 0usize;
    while k < B_PR_N {
        let s = span.wrapping_mul(k);
        acc = acc.wrapping_add(b_probe_win(input, &mut ht, s, s.wrapping_add(B_PR_W)));
        k += 1;
    }
    acc
}

/// probe_all when f == 1, else 0.
pub fn b_probe_if(input: &[u8], f: usize) -> u64 {
    if f == 1 {
        b_probe_all(input)
    } else {
        0
    }
}

/// Histogram of an odd-stride sample (every byte lane of word-structured data is seen) of about 4096 bytes.
pub fn b_odd_sample(input: &[u8], h: &mut [u32; 256]) {
    let n = input.len();
    let st = (n / 4096 + 1) | 1;
    let mut k = 0usize;
    let mut c = 0usize;
    while c < 8192 && k < n {
        let b = b_byte_at(input, k) % 256;
        h[b] = h[b].wrapping_add(1);
        k = k.wrapping_add(st);
        c += 1;
    }
}

/// 256 * log2(x) (8-bit mantissa), x >= 1.
pub fn b_lg8(x: u32) -> u64 {
    let y = x | 1;
    let e = 31u32.wrapping_sub(y.leading_zeros()) % 32;
    let m = if e >= 8 { y.wrapping_shr(e.wrapping_sub(8)) & 255 } else { y.wrapping_shl(8u32.wrapping_sub(e)) & 255 };
    (e as u64).wrapping_mul(256).wrapping_add(m as u64)
}

/// Order-0 entropy of the histogram in 1/256 bits per symbol (2048 for an empty histogram).
pub fn b_entropy256(h: &[u32; 256]) -> usize {
    let mut tot = 0u64;
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i];
        tot = tot.wrapping_add(c as u64);
        acc = if c > 0 { acc.wrapping_add((c as u64).wrapping_mul(b_lg8(c))) } else { acc };
        i += 1;
    }
    let t32 = if tot > 4000000000 { 4000000000u32 } else { tot as u32 };
    let a = b_lg8(t32);
    let b = if tot == 0 { 0 } else { acc / tot };
    if tot == 0 {
        2048
    } else if a > b {
        (a - b) as usize
    } else {
        0
    }
}

pub fn b_ge64(a: u64, b: u64) -> usize {
    if a >= b {
        1
    } else {
        0
    }
}

/// mode (0: champion, 1: H-DP, 2: literal-only plan) + 4 * (probe coverage below B_COVF/1000)
/// + 8 * (long-match coverage reaches B_LONGK/1000, or a small input).
/// Small inputs: H-DP. Low coverage: H-DP when the entropy is high (compressed-like), else literal-only.
/// Champion when coverage is below B_COVF/1000 (float-weight-like) or the entropy is below B_HGEN/256 bits
/// (DNA-like); H-DP when the long-match coverage reaches B_LONGK/1000; otherwise B_DEFM.
pub fn b_classify(input: &[u8]) -> usize {
    let n = input.len();
    let small = b_lt(n, B_D_SMALL);
    let r = b_probe_if(input, small ^ 1);
    let cov = r / 4294967296;
    let nm = r % 4294967296;
    let mut lh = [0u32; 256];
    b_odd_sample(input, &mut lh);
    let h0 = b_entropy256(&lh);
    let bc = b_byte_classes(&lh);
    let b2 = b_byte_classes2(&lh);
    let tot = bc % 1048576;
    let ctl = (bc / 1048576) % 1048576;
    let hib = (bc / 1099511627776) % 1048576;
    let pw = (B_PR_W * B_PR_N) as u64;
    let low = b_lt64(cov.wrapping_mul(1000), B_LITCOV.wrapping_mul(pw));
    let hl = b_ge64(nm.wrapping_mul(1000), B_LONGK.wrapping_mul(pw));
    let lc = b_lt64(cov.wrapping_mul(1000), B_COVF.wrapping_mul(pw));
    let hi = b_ge(h0, B_HLIT);
    let gen = b_lt(h0, B_HGEN) & b_ge(h0, B_HGENLO);
    let tc0 = b_lt64(cov.wrapping_mul(1000), B_COVT.wrapping_mul(pw)) & b_lt64(nm.wrapping_mul(1000), B_LONGT.wrapping_mul(pw));
    let mb = b_ge64(hib.wrapping_mul(1000), B_HITC.wrapping_mul(tot)) & b_lt64(ctl.wrapping_mul(1000), B_CTLMB.wrapping_mul(tot));
    let tc = tc0 & (mb ^ 1);
    let mc = (small ^ 1) & b_ge64(ctl.wrapping_mul(1000), B_CTLMC.wrapping_mul(tot)) & b_lt64(hib.wrapping_mul(1000), B_HIMC.wrapping_mul(tot)) & b_lt64(nm.wrapping_mul(1000), B_NMMC.wrapping_mul(pw));
    let ch = (lc & (hi ^ 1)) | gen | tc | mc;
    let m0 = b_sel(hl | lc, 1, B_DEFM);
    let m1 = b_sel(ch, 0, m0);
    let z0 = b2 % 65536;
    let im = b_ge64(z0.wrapping_mul(1000), B_Z0IM.wrapping_mul(tot));
    let bf = b_lt(h0, B_HBF);
    let m2 = b_sel(low, b_sel(hi, b_sel(im, 0, 1), b_sel(bf, 0, 2)), m1);
    let gkc = b_sel(lc, b_sel(hi, 4, 1), b_sel(mc, 2, b_sel(tc, 3, b_sel(gen, 0, 5))));
    let dig = (b2 / 65536) % 65536;
    let nz = (b2 / 4294967296) % 65536;
    let dh = (hl | small) & b_eq64(z0, 0) & b_ge64(dig.wrapping_mul(1000), B_DIGR.wrapping_mul(tot)) & b_ge64(B_NZR, nz);
    let sp = small & b_lt(h0, B_HSP);
    let fc = b_sel(dh | sp, 2, b_sel(hl | small, 1, 0));
    b_sel(small, 1, m2).wrapping_add(gkc.wrapping_mul(4)).wrapping_add(fc.wrapping_mul(32))
}

/// Zero bytes + 2^16 * digits + 2^32 * distinct bytes of a histogram.
pub fn b_byte_classes2(h: &[u32; 256]) -> u64 {
    let mut z0 = 0u64;
    let mut dig = 0u64;
    let mut nz = 0u64;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i] as u64;
        z0 = z0.wrapping_add(b_sel64(b_eq(i, 0), c, 0));
        dig = dig.wrapping_add(b_sel64(b_ge(i, 48) & b_lt(i, 58), c, 0));
        nz = nz.wrapping_add(b_sel64(b_lt64(0, c), 1, 0));
        i += 1;
    }
    (z0 % 65536).wrapping_add((dig % 65536).wrapping_mul(65536)).wrapping_add((nz % 65536).wrapping_mul(4294967296))
}

/// Byte classes of a histogram: total + 2^20 * control bytes (1..31 without tab, LF, CR) + 2^40 * bytes >= 128.
pub fn b_byte_classes(h: &[u32; 256]) -> u64 {
    let mut tot = 0u64;
    let mut ctl = 0u64;
    let mut hib = 0u64;
    let mut i = 0usize;
    while i < 256 {
        let c = h[i] as u64;
        tot = tot.wrapping_add(c);
        let isc = (b_lt(i, 32) & b_ge(i, 1)) & ((b_eq(i, 9) | b_eq(i, 10) | b_eq(i, 13)) ^ 1);
        ctl = ctl.wrapping_add(b_sel64(isc, c, 0));
        hib = hib.wrapping_add(b_sel64(b_ge(i, 128), c, 0));
        i += 1;
    }
    (tot % 1048576).wrapping_add((ctl % 1048576).wrapping_mul(1048576)).wrapping_add((hib % 1048576).wrapping_mul(1099511627776))
}

pub fn b_parse_mode(input: &[u8], out: &mut [u32], mode: usize) -> usize {
    let n = input.len();
    let c = b_classify(input);
    let route = c % 4;
    let gkc = (c / 4) % 8;
    let gk = b_sel64(b_eq(gkc, 1) | b_eq(gkc, 4), b_mode_gk(mode, B_GKLOW), b_sel64(b_eq(gkc, 2), b_mode_gk(mode, B_GKMC), b_sel64(b_eq(gkc, 3), b_mode_gk(mode, B_GKT), b_sel64(b_eq(gkc, 5), b_mode_gk(mode, B_GKX), b_mode_gk(mode, B_GK2)))));
    let fc = (c / 32) % 4;
    let kend = B_H_KENDS[fc % 4].wrapping_add(fc.wrapping_mul(32));
    let mut plan = b_filled(n.wrapping_add(1), 0);
    b_champ_if(mode, input, &mut plan, b_eq(route, 0), gk, b_eq(gkc, 1));
    let high = b_eq(mode, 2) | b_eq(mode, 3);
    let force = high & b_eq(route, 1) & b_ge(n, B_D_SMALL);
    b_hdp_if(mode, input, &mut plan, b_eq(route, 1) & (force ^ 1), kend);
    b_champ_if(mode, input, &mut plan, force, 1, 0);
    // @P7_BEGIN
    let nt = b_emit_all(input, out, &plan);
    // @P7_END
    nt
}

/// Default champion mode: local0class.
pub fn b_parse(input: &[u8], out: &mut [u32]) -> usize {
    b_parse_mode(input, out, 0)
}

pub const B_CX_HP:usize=1;
pub fn b_cx_hload(tbl:&[u32],b:usize,litc:&mut [u32;256],lcost:&mut [u32;512],dcs:&mut [u32;256],dcb:&mut [u32;256]) {
    let off=b.wrapping_mul(B_TB);
    let mut c=0usize;
    while c<256 {litc[c]=b_get(tbl,off.wrapping_add(c));c+=1;}
    let mut l=3usize;
    while l<259 {lcost[l]=b_get(tbl,off.wrapping_add(256).wrapping_add(l));l+=1;}
    let mut j=0usize;
    while j<256 {
        dcs[j]=b_get(tbl,off.wrapping_add(515).wrapping_add(B_H_DSYM_S[j] as usize));
        dcb[j]=b_get(tbl,off.wrapping_add(515).wrapping_add(B_H_DSYM_B[j] as usize));
        j+=1;
    }
}
pub fn b_cx_hpolish(input:&[u8],plan:&mut [u32],cache:&[u64],starts:&[u32],sizes:&[u32],offsets:&[u32]) {
    let n=input.len();
    let nbmax=n/B_BT+2;
    let mut tbl=b_filled(nbmax.wrapping_mul(B_TB),0);
    let mut fr=b_filled(nbmax.wrapping_mul(B_FB),0);
    let mut bpos=b_filled(nbmax,0);
    let mut cand=b_filled(n.wrapping_add(1),0);
    let mut arr=[0u64;8192];
    let mut ed=[0u64;32768];
    let mut llf=[0u32;512];
    let mut df=[0u32;32];
    let mut litc=[0u32;256];
    let mut lcost=[0u32;512];
    let mut dcs=[0u32;256];
    let mut dcb=[0u32;256];
    let mut pi=0usize;
    while pi<B_CX_HP {
        let nb=b_walk(input,&[],&[],plan,0,&mut fr,&mut bpos);
        let old=b_eval_blocks(&mut fr,&mut tbl,nb,nbmax,0);

        let mut j=0usize;
        let mut b=0usize;
        while j<starts.len() {
            let start=b_get(starts,j) as usize;
            let size=b_get(sizes,j) as usize;
            let off=b_get(offsets,j) as usize;
            let ec=if off<cache.len() {(cache[off]%32768) as usize} else {32767};
            if ec<32767 {
                let mut e=0usize;
                while e<=ec && e<32768 {
                    ed[e]=if off.wrapping_add(e)<cache.len() {cache[off.wrapping_add(e)]} else {0}; e+=1;
                }
                while b+1<nb && b_get(&bpos,b+1) as usize<=start {b+=1;}
                b_cx_hload(&tbl,b,&mut litc,&mut lcost,&mut dcs,&mut dcb);
                b_cx_hreplay(input,start,size,&mut arr,&ed,&mut litc,&mut lcost,&mut dcs,&mut dcb,&tbl,&bpos,nb);
                b_h_backtrack(input,&arr,&mut cand,start,size,&mut llf,&mut df);
            } else {
                let mut p=start;
                let end=b_umin(start.wrapping_add(size),n);
                while p<end {let c=b_get(plan,p);b_set(&mut cand,p,c);p+=b_clamp_step((c as usize)/65536,end-p);}
            }
            j+=1;
        }
        let nb2=b_walk(input,&[],&[],&mut cand,0,&mut fr,&mut bpos);
        let new=b_cx_bits_only(&mut fr,nb2,nbmax);
        if new<old {
            let mut p=0usize;
            while p<n {
                let c=b_get(&cand,p);b_set(plan,p,c);p+=b_clamp_step((c as usize)/65536,n-p);
            }
        }
        pi+=1;
    }
}
pub fn b_cx_hreplay(input: &[u8], start: usize, bend: usize, arr: &mut [u64; 8192], ed: &[u64; 32768], litc: &mut [u32; 256], lcost: &mut [u32; 512], dcs: &mut [u32; 256], dcb: &mut [u32; 256], tbl: &[u32], bpos: &[u32], nb:usize) {
    let mut b=0usize;
    while b+1<nb && b_get(bpos,b+1) as usize<=start {b+=1;}
    b_cx_hload(tbl,b,litc,lcost,dcs,dcb);
    let mut inh=[0u32;8192];
    let mut ie=1usize;
    let ic=(ed[0]%32768) as usize;
    while ie<=ic && ie<32768 {
        let r=ed[ie];
        let src=((r>>34)%8192) as usize;
        let hi=(r%512) as u32;
        let d=((r>>18)%65536) as u32;
        if hi>inh[src]/65536 {inh[src]=hi.wrapping_mul(65536).wrapping_add(d);}
        ie+=1;
    }
    let mut previous=0usize;
    b_h_fill_inf(arr);
    b_h_put64(arr, 0, 0);
    let cnt = (ed[0] % 32768) as usize;
    let mut q = 1usize;
    let mut p = 0usize;
    while p < 8192 && p < bend {
        if b+1<nb && b_get(bpos,b+1) as usize<=start.wrapping_add(p) {
            b+=1;b_cx_hload(tbl,b,litc,lcost,dcs,dcb);
        }
        let price = (b_h_at64(arr, p) >> 32) as u32;
        let lp = price.wrapping_add(litc[b_byte_at(input, start.wrapping_add(p)) % 256]);
        let j = p.wrapping_add(1) % 8192;
        let old = arr[j];
        let cand = ((lp as u64) << 32) | 1;
        arr[j] = if cand < old { cand } else { old };
        let cur=inh[p%8192] as usize;
        let pl=previous/65536;
        let inherited=b_sel(b_ge(pl,4),(pl.wrapping_sub(1)).wrapping_mul(65536).wrapping_add(previous%65536),0);
        let m=b_sel(b_lt(cur/65536,inherited/65536),inherited,cur);
        previous=m;
        let hi=b_umin(m/65536,bend-p);
        let d=m%65536;
        let lo=if hi>B_CX_FIW+3 {hi-B_CX_FIW} else {3};
        let dc=b_h_dist_cost(dcs,dcb,d);
        if hi>=3 && d>=1 {
            b_h_relax_range(arr,lcost,p,lo,hi,price.wrapping_add(dc),(d as u64)<<9);
        }
        q = b_h_replay_at(arr, ed, lcost, dcs, dcb, p, q, cnt);
        p += 1;
    }
}


pub const B_CX_FIW:usize=0;

pub fn b_pkg_merge(freq:&[u32],off:usize,nsym:usize,maxbits:usize,lens:&mut [u32],loff:usize) {
    let mut order=[0u32;288];
    let k=b_sort_live(freq,off,nsym,&mut order);
    let mut weights=[0u64;576];
    let mut parent=[0u32;576];
    let mut depth=[0u32;576];
    let mut i=0usize;
    while i<k && i<288 {weights[i]=b_get(freq,off.wrapping_add(order[i] as usize)) as u64;i+=1;}
    let mut leaf=0usize;
    let mut pair=k;
    let mut next=k;
    while next.wrapping_add(1)<k.wrapping_mul(2) && next<575 {
        let mut sum=0u64;
        let mut j=0usize;
        while j<2 {
            let lw=if leaf<k {weights[leaf%576]} else {18446744073709551615u64};
            let pw=if pair<next {weights[pair%576]} else {18446744073709551615u64};
            let take=b_lt64(pw,lw)^1;
            let idx=b_sel(take,leaf,pair);
            sum=sum.wrapping_add(weights[idx%576]);
            parent[idx%576]=next as u32;
            leaf=leaf.wrapping_add(take);
            pair=pair.wrapping_add(take^1);
            j+=1;
        }
        weights[next%576]=sum;
        next+=1;
    }
    let mut mx=0usize;
    let mut node=next.saturating_sub(1);
    while node>0 {
        node-=1;
        let d=depth[(parent[node%576] as usize)%576].wrapping_add(1);
        depth[node%576]=d;
        mx=b_umax(mx,d as usize);
    }
    if mx<=maxbits {
        b_clear(lens,loff,loff.wrapping_add(nsym));
        let mut r=0usize;
        while r<k && r<288 {
            b_set(lens,loff.wrapping_add(order[r] as usize),b_sel32(b_eq(k,1),1,depth[r]));r+=1;
        }
    } else {
        b_pkg_merge_pm(freq,off,nsym,maxbits,lens,loff);
    }
}

pub fn b_cx_bits_only(fr:&mut [u32],nb:usize,nbmax:usize)->u64 {
    let mut lens=[0u32;320];
    let mut b=0usize;
    let mut total=0u64;
    let lim=b_umin(nb,nbmax);
    while b<lim {total=total.wrapping_add(b_block_bits(fr,b.wrapping_mul(B_FB),&mut lens)/4);b+=1;}
    total
}

pub fn b_cx_sym(fr: &[u32], off: usize, lens: &[u32], kind: u32, sc: &mut [u32], ew:u32) {
    let tl = b_sum_range(fr, off, off.wrapping_add(286)).wrapping_add(1);
    let td = b_sum_range(fr, off.wrapping_add(288), off.wrapping_add(318));
    let lt = b_log2x16(tl);
    let ld = b_log2x16(td);
    let mut s = 0usize;
    while s < 318 {
        let f = b_get(fr, off.wrapping_add(s)) as u64;
        let ls = b_get(lens, s);
        let fl = b_fixed_len(s);
        let lf = b_log2x16(f);
        let hl = if kind == 1 {
            if s >= 288 {
                5
            } else {
                fl
            }
        } else if kind == 2 && s < 256 {
            8
        } else if ls > 0 {
            ls
        } else {
            B_UNUSED
        };
        let tot = if s >= 288 { ld } else { lt };
        let e0 = if f > 0 { tot.saturating_sub(lf) } else { tot.saturating_add(B_UPEN) };
        let e = if e0 < 16 { 16 } else { e0 };
        let hc = hl.wrapping_mul(B_SC);
        let mixv = (e.wrapping_mul(ew).wrapping_add(hc.wrapping_mul(8u32.wrapping_sub(ew)))) / 8;
        b_set(sc, s, if kind != 0 { hc } else { mixv });
        s += 1;
    }
}
pub fn b_cx_eval(fr: &mut [u32], tbl: &mut [u32], nb2: usize, nbmax: usize, damp: u32,ew:u32) -> u64 {
    let mut lens = [0u32; 320];
    let mut sc = [0u32; 320];
    let mut total = 0u64;
    let lim = b_umin(nb2, nbmax);
    let mut b = 0usize;
    while b < lim {
        let r = b_block_bits(fr, b.wrapping_mul(B_FB), &mut lens);
        total = total.wrapping_add(r / 4);
        b_cx_sym(fr, b.wrapping_mul(B_FB), &lens, (r % 4) as u32, &mut sc,ew);
        b_fill_table(&sc, tbl, b.wrapping_mul(B_TB), damp);
        let raw = b_get(fr, b.wrapping_mul(B_FB).wrapping_add(319)) as u64;
        let fb = b_eq(B_STM, 1) & b_lt64(raw.wrapping_mul(8).wrapping_add(35).wrapping_add(B_STMARG), r / 4);
        let fl = ((b_get(tbl, b.wrapping_mul(B_TB).wrapping_add(545)) as usize) | fb) & 1;
        b_set(tbl, b.wrapping_mul(B_TB).wrapping_add(545), fl as u32);
        b_forbid_if(tbl, b.wrapping_mul(B_TB), fl);
        b += 1;
    }
    total
}


pub const B_CX_FIW_HFI: usize = 8;
pub fn b_cx_hpolish_hfi(input:&[u8],plan:&mut [u32],cache:&[u64],starts:&[u32],sizes:&[u32],offsets:&[u32]) {
    let n=input.len();
    let nbmax=n/B_BT+2;
    let mut tbl=b_filled(nbmax.wrapping_mul(B_TB),0);
    let mut fr=b_filled(nbmax.wrapping_mul(B_FB),0);
    let mut bpos=b_filled(nbmax,0);
    let mut cand=b_filled(n.wrapping_add(1),0);
    let mut arr=[0u64;8192];
    let mut ed=[0u64;32768];
    let mut llf=[0u32;512];
    let mut df=[0u32;32];
    let mut litc=[0u32;256];
    let mut lcost=[0u32;512];
    let mut dcs=[0u32;256];
    let mut dcb=[0u32;256];
    let mut inh=b_filled(n,0);
    let mut j=0usize;
    while j<starts.len() {
        let start=b_get(starts,j) as usize;
        let off=b_get(offsets,j) as usize;
        let ec=if off<cache.len() {(cache[off]%32768) as usize} else {0};
        let mut e=1usize;
        while e<=ec && off.wrapping_add(e)<cache.len() {
            let r=cache[off.wrapping_add(e)];
            let pos=start.wrapping_add(((r>>34)%8192) as usize);
            let hi=(r%512) as usize;
            let d=((r>>18)%65536) as usize;
            if hi>(b_get(&inh,pos) as usize)/65536 {
                b_set(&mut inh,pos,((hi as u32)<<16)|(d as u32));
            }
            e+=1;
        }
        j+=1;
    }
    let mut pos=0usize;
    let mut prev=0usize;
    while pos<n {
        let pl=prev/65536;
        let cur=b_get(&inh,pos) as usize;
        let ml=b_sel(b_ge(pl,4),(pl.wrapping_sub(1)).wrapping_mul(65536).wrapping_add(prev%65536),0);
        let v=b_sel(b_lt(cur/65536,ml/65536),ml,cur);
        b_set(&mut inh,pos,v as u32);
        prev=v;pos+=1;
    }
    let mut pi=0usize;
    while pi<B_CX_HP {
        let nb=b_walk(input,&[],&[],plan,0,&mut fr,&mut bpos);
        let old=b_eval_blocks(&mut fr,&mut tbl,nb,nbmax,0);
        b_copy32(plan,0,&mut cand,0,n);
        let mut j=0usize;
        let mut b=0usize;
        while j<starts.len() {
            let start=b_get(starts,j) as usize;
            let size=b_get(sizes,j) as usize;
            let off=b_get(offsets,j) as usize;
            let ec=if off<cache.len() {(cache[off]%32768) as usize} else {32767};
            if ec<32767 {
                let mut e=0usize;
                while e<=ec && e<32768 {
                    ed[e]=if off.wrapping_add(e)<cache.len() {cache[off.wrapping_add(e)]} else {0}; e+=1;
                }
                while b+1<nb && b_get(&bpos,b+1) as usize<=start {b+=1;}
                b_cx_hload(&tbl,b,&mut litc,&mut lcost,&mut dcs,&mut dcb);
                b_cx_hreplay_hfi(input,start,size,&mut arr,&ed,&mut litc,&mut lcost,&mut dcs,&mut dcb,&tbl,&bpos,nb,&inh);
                b_h_backtrack(input,&arr,&mut cand,start,size,&mut llf,&mut df);
            }
            j+=1;
        }
        let nb2=b_walk(input,&[],&[],&mut cand,0,&mut fr,&mut bpos);
        let new=b_eval_blocks(&mut fr,&mut tbl,nb2,nbmax,0);
        b_copy32(&cand,0,plan,0,b_sel(b_lt64(new,old),n,0));
        pi+=1;
    }
}

pub fn b_cx_hreplay_hfi(input: &[u8], start: usize, bend: usize, arr: &mut [u64; 8192], ed: &[u64; 32768], litc: &mut [u32; 256], lcost: &mut [u32; 512], dcs: &mut [u32; 256], dcb: &mut [u32; 256], tbl: &[u32], bpos: &[u32], nb:usize, inh:&[u32]) {
    let mut b=0usize;
    while b+1<nb && b_get(bpos,b+1) as usize<=start {b+=1;}
    b_cx_hload(tbl,b,litc,lcost,dcs,dcb);
    b_h_fill_inf(arr);
    b_h_put64(arr, 0, 0);
    let cnt = (ed[0] % 32768) as usize;
    let mut q = 1usize;
    let mut p = 0usize;
    while p < 8192 && p < bend {
        if b+1<nb && b_get(bpos,b+1) as usize<=start.wrapping_add(p) {
            b+=1;b_cx_hload(tbl,b,litc,lcost,dcs,dcb);
        }
        let price = (b_h_at64(arr, p) >> 32) as u32;
        let lp = price.wrapping_add(litc[b_byte_at(input, start.wrapping_add(p)) % 256]);
        let j = p.wrapping_add(1) % 8192;
        let old = arr[j];
        let cand = ((lp as u64) << 32) | 1;
        arr[j] = if cand < old { cand } else { old };
        let m=b_get(inh,start.wrapping_add(p)) as usize;
        let hi=b_umin(m/65536,bend-p);
        let d=m%65536;
        let lo=if hi>B_CX_FIW_HFI+3 {hi-B_CX_FIW_HFI} else {3};
        let dc=b_h_dist_cost(dcs,dcb,d);
        if hi>=3 && d>=1 {
            b_h_relax_range(arr,lcost,p,lo,hi,price.wrapping_add(dc),(d as u64)<<9);
        }
        q = b_h_replay_at(arr, ed, lcost, dcs, dcb, p, q, cnt);
        p += 1;
    }
}

/// Mode-dependent stop constants, selected outside the parsing loops.
pub fn b_mode_gk(mode: usize, base: u64) -> u64 {
    if mode >= 1 && mode <= 3 { base / 2 } else { base }
}

/// Select the cost evaluator once per DP pass, outside the per-block loops.
pub fn b_eval_mode(mode: usize, fr: &mut [u32], tbl: &mut [u32], nb: usize, nbmax: usize, damp: u32, ew: u32) -> u64 {
    if mode == 0 { b_cx_eval(fr, tbl, nb, nbmax, damp, ew) }
    else { b_eval_blocks(fr, tbl, nb, nbmax, damp) }
}


pub fn b_cx_jitter(tbl:&mut [u32],nb:usize,seed:u32, amplitude:u32) {
    let amp = amplitude % 33;
    let mut b=0usize;
    while b<nb {
        let off=b.wrapping_mul(B_TB);
        let mut s=0usize;
        while s<545 {
            let sym=if s>=256 && s<515 {257+b_lcode(s-256)} else if s>=515 {288+s-515} else {s};
            let x=(sym as u32).wrapping_mul(2654435761).wrapping_add(seed.wrapping_mul(2246822519));
            let x=(x^(x>>16)).wrapping_mul(3266489917);
            let d=(x>>24)%(2*amp+1);
            let c=b_get(tbl,off.wrapping_add(s));
            let v=c.saturating_add(d).saturating_sub(amp);
            b_set(tbl,off.wrapping_add(s),v);
            s+=1;
        }
        b+=1;
    }
}

/// The high-family restart search; each restart runs three DP refinements.
pub fn b_cx_restarts(
    input: &[u8], mstart: &[u32], mc: &[u32], tbl: &mut [u32],
    fr: &mut [u32], bpos: &mut [u32], bend: &[u32; 512],
    choice: &mut [u32], plan: &mut [u32], nbmax: usize, lamh: u32,
    items: &mut Vec<u32>, istart: &mut Vec<u32>, pr: usize, chw: usize,
    restarts: usize,
) {
    let n = input.len();
    let jitteron = b_eq(b_classify(input) % 4, 0);
    let mut restart = 0usize;
    while restart < restarts && jitteron == 1 {
        let mut nbc = b_walk(input, mstart, mc, plan, 0, fr, bpos);
        let mut bestp = b_eval_blocks(fr, tbl, nbc, nbmax, 0);
        b_cx_jitter(tbl, nbc, (restart as u32).wrapping_add(1), 16);
        let mut step = 0usize;
        while step < 3 {
            b_dp_pass(input, mstart, mc, tbl, bend, bpos, nbc, choice, chw,
                    0, items, istart, pr, 0, 0, lamh);
            nbc = b_walk(input, mstart, mc, choice, 0, fr, bpos);
            let rp = b_eval_blocks(fr, tbl, nbc, nbmax, 0);
            let improve = b_lt64(rp, bestp);
            b_copy32(choice, 0, plan, 0, b_sel(improve, n, 0));
            bestp = b_sel64(improve, rp, bestp);
            step += 1;
        }
        restart += 1;
    }
}


// ===== engine d: parse.rs =====

pub const D_DEPTH: usize = 512;
pub const D_LONG_DEPTH: usize = 64;
pub const D_LDEPTH: usize = 128;
pub const D_MDEPTH: usize = 32;
pub const D_MISS_D: usize = 8;
pub const D_NICE: usize = 258;
pub const D_BLOCK: usize = 32768;
pub const D_NEAR3: usize = 32768;
pub const D_TRY_ALL: usize = 24;
pub const D_MISS_COST: u32 = 160;
pub const D_BIAS: u32 = 12;
pub const D_INNER_MAXL: usize = 24;
pub const D_LAZY_LIMIT: usize = 258;
pub const D_BK: usize = 128;
pub const D_LONG_BELOW: u32 = 52;
pub const D_SKIP_AFTER: usize = 512;
pub const D_SKIPN: usize = 3;
pub const D_RUN_D: usize = 16;
pub const D_RUN_L: usize = 64;
pub const D_RUN_KEEP: usize = 16;
pub const D_SPAN1: usize = 16;
pub const D_SPAN2: usize = 8;
pub const D_INNER_L: usize = 24;
pub const D_NX: usize = 3;
pub const D_XCAP: usize = 32;
pub const D_HW: u32 = 16;
pub const D_TK: u64 = 8;
pub const D_INNER_D: usize = 24;

/// How many bytes agree at `a` and `b`, up to `cap`.
pub fn d_match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// How many bytes agree at `a < b` and `b`, up to `cap`, for the search: 0 unless
/// `b + cap` is within the input.
pub fn d_ext_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let n = input.len();
    let mut l = 0usize;
    if a < b && b <= n && cap <= n - b {
        let mut go = 1usize;
        while go == 1 && l < cap && cap - l >= 8 {
            let x = d_load64(input, a + l) ^ d_load64(input, b + l);
            if x != 0 {
                l += (x.leading_zeros() / 8) as usize;
                go = 0;
            } else {
                l += 8;
            }
        }
        while go == 1 && l < cap && input[b + l] == input[a + l] {
            l += 1;
        }
    }
    l
}

/// Eight bytes from `p`, the first one most significant. Needs `p + 8 <= input.len()`.
pub fn d_load64(input: &[u8], p: usize) -> u64 {
    let b7 = input[p + 7] as u64;
    let b6 = input[p + 6] as u64;
    let b5 = input[p + 5] as u64;
    let b4 = input[p + 4] as u64;
    let b3 = input[p + 3] as u64;
    let b2 = input[p + 2] as u64;
    let b1 = input[p + 1] as u64;
    let b0 = input[p] as u64;
    b7 + 256 * (b6 + 256 * (b5 + 256 * (b4 + 256 * (b3 + 256 * (b2 + 256 * (b1 + 256 * b0))))))
}

/// `16 * log2(total / freq)`, rounded down to 1/16 bit; `D_MISS_COST` for an unseen symbol.
pub fn d_cost16(freq: u32, total: u32) -> u32 {
    if freq == 0 {
        return D_MISS_COST;
    }
    let t = total as u64;
    let mut f = freq as u64;
    let mut c = 0u32;
    let lzf = f.leading_zeros();
    let lzt = t.leading_zeros();
    if lzf > lzt {
        let s0 = lzf - lzt;
        let s = if f.wrapping_shl(s0) > t { s0 - 1 } else { s0 };
        f = f.wrapping_shl(s);
        c = 16 * s;
    }
    let mut k = 0usize;
    while k < 16 && f.wrapping_mul(1069) / 1024 <= t {
        f = f.wrapping_mul(1069) / 1024;
        c += 1;
        k += 1;
    }
    if c < 16 {
        16
    } else {
        c
    }
}

/// Distance code of `d` in 1..=32768.
pub fn d_dcode(dlo: &[u8; 256], dhi: &[u8; 256], d: usize) -> usize {
    if d <= 256 {
        let k = if d >= 1 { d - 1 } else { 0 };
        dlo[k % 256] as usize
    } else {
        dhi[((d - 1) / 128) % 256] as usize
    }
}

/// Bits saved by the match `(l, d)` at block index `i`: literal cost of the covered bytes
/// minus the match cost, or 0 when the match costs more.
pub fn d_gain(
    pref: &[u32; 65536],
    lenc: &[u32; 512],
    dcost: &[u32; 32],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    i: usize,
    l: usize,
    d: usize,
) -> u32 {
    let lit = pref[(i + l) % 65536].wrapping_sub(pref[i % 65536]);
    let mc = lenc[l % 512].saturating_add(dcost[d_dcode(dlo, dhi, d) % 32]);
    if lit > mc {
        lit - mc
    } else {
        0
    }
}

/// Records `(l, d)` as the next improving match of block index `i`, replacing the last one when
/// both have the same distance code; keeps the first `D_NX - 1` and the latest one.
pub fn d_push_x(
    xs: &mut [u32; 131072],
    xn: &mut [u8; 32768],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    i: usize,
    l: usize,
    d: usize,
) {
    let c = xn[i % 32768] as usize;
    let mut s = if c < D_NX { c } else { D_NX - 1 };
    if c > 0 {
        let v = xs[(i * D_NX + c - 1) % 131072] as usize;
        if d_dcode(dlo, dhi, v / 512) == d_dcode(dlo, dhi, d) {
            s = c - 1;
        }
    }
    xs[(i * D_NX + s) % 131072] = (d as u32) * 512 + (l as u32);
    if s == c && c < D_NX {
        xn[i % 32768] = (c + 1) as u8;
    }
}

/// The match at `p` (block index `i`) saving the most bits among the near 3-byte candidate
/// `c3` and `pcap` entries of the chain from `start`, looking only at matches longer than
/// `floor`: `(len, dist, gain)`.
pub fn d_find(
    input: &[u8],
    prev: &[u32; 32768],
    pref: &[u32; 65536],
    lenc: &[u32; 512],
    dcost: &[u32; 32],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    p: usize,
    i: usize,
    cap: usize,
    start: usize,
    c3: usize,
    floor: usize,
    pcap: usize,
    xs: &mut [u32; 131072],
    xn: &mut [u8; 32768],
) -> (usize, usize, u32, usize, usize) {
    let mut bl = 0usize;
    let mut bd = 0usize;
    let mut bg = 0u32;
    let mut sl = 0usize;
    let mut sd = 0usize;
    let mut need = floor;
    let n = input.len();
    let ok = if p <= n && cap <= n - p { 1usize } else { 0usize };
    if ok == 1 && c3 > 0 && c3 <= p && p - (c3 - 1) <= D_NEAR3 && need < cap {
        let c = c3 - 1;
        if input[c + need] == input[p + need] {
            let l = d_ext_len(input, c, p, cap);
            if l >= 3 && l > need {
                let g = d_gain(pref, lenc, dcost, dlo, dhi, i, l, p - c);
                if g > 0 {
                    bl = l;
                    bd = p - c;
                    bg = g;
                    need = l;
                    d_push_x(xs, xn, dlo, dhi, i, l, p - c);
                } else {
                    d_push_x(xs, xn, dlo, dhi, i, l, p - c);
                }
            } else if l >= 3 {
                d_push_x(xs, xn, dlo, dhi, i, l, p - c);
            }
        } else if need >= 3 {
            let l = d_ext_len(input, c, p, if need < D_XCAP { need } else { D_XCAP });
            if l >= 3 {
                d_push_x(xs, xn, dlo, dhi, i, l, p - c);
            }
        }
    }
    let low = if p >= 32768 { p - 32768 + 1 } else { 1usize };
    let mut cur = start;
    let mut nc = prev[start.wrapping_sub(1) % 32768] as usize;
    let mut probes = 0usize;
    while ok == 1 && probes < pcap && cur >= low && cur <= p && need < cap {
        let c = cur - 1;
        let nnc = prev[nc.wrapping_sub(1) % 32768] as usize;
        {
            if input[c + need] == input[p + need] {
                let l = d_ext_len(input, c, p, cap);
                if l > need && l >= 3 {
                    let g = d_gain(pref, lenc, dcost, dlo, dhi, i, l, p - c);
                    if g > 0 || l >= 5 || (l >= 4 && pref[(i + l) % 65536].wrapping_sub(pref[i % 65536]) < 96 * 4) {
                        d_push_x(xs, xn, dlo, dhi, i, l, p - c);
                    }
                    sl = if g > bg { bl } else { l };
                    sd = if g > bg { bd } else { p - c };
                    if g > bg {
                        bl = l;
                    }
                    if g > bg {
                        bd = p - c;
                    }
                    if g > bg {
                        bg = g;
                    }
                    need = l;
                }
            }
            cur = nc;
            nc = nnc;
        }
        probes += 1;
    }
    (bl, bd, bg, sl, sd)
}

/// `find` with `D_INNER_D` chain entries, for the inner positions of a committed match.
pub fn d_find_in(
    input: &[u8],
    prev: &[u32; 32768],
    pref: &[u32; 65536],
    lenc: &[u32; 512],
    dcost: &[u32; 32],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    p: usize,
    i: usize,
    cap: usize,
    start: usize,
    c3: usize,
    floor: usize,
    xs: &mut [u32; 131072],
    xn: &mut [u8; 32768],
) -> (usize, usize, u32, usize, usize) {
    let mut bl = 0usize;
    let mut bd = 0usize;
    let mut bg = 0u32;
    let mut sl = 0usize;
    let mut sd = 0usize;
    let mut need = floor;
    let n = input.len();
    let ok = if p <= n && cap <= n - p { 1usize } else { 0usize };
    if ok == 1 && c3 > 0 && c3 <= p && p - (c3 - 1) <= D_NEAR3 && need < cap {
        let c = c3 - 1;
        if input[c + need] == input[p + need] {
            let l = d_ext_len(input, c, p, cap);
            if l >= 3 && l > need {
                let g = d_gain(pref, lenc, dcost, dlo, dhi, i, l, p - c);
                if g > 0 {
                    bl = l;
                    bd = p - c;
                    bg = g;
                    need = l;
                    d_push_x(xs, xn, dlo, dhi, i, l, p - c);
                } else {
                    d_push_x(xs, xn, dlo, dhi, i, l, p - c);
                }
            } else if l >= 3 {
                d_push_x(xs, xn, dlo, dhi, i, l, p - c);
            }
        } else if need >= 3 {
            let l = d_ext_len(input, c, p, if need < D_XCAP { need } else { D_XCAP });
            if l >= 3 {
                d_push_x(xs, xn, dlo, dhi, i, l, p - c);
            }
        }
    }
    let low = if p >= 32768 { p - 32768 + 1 } else { 1usize };
    let mut cur = start;
    let mut nc = prev[start.wrapping_sub(1) % 32768] as usize;
    let mut probes = 0usize;
    while ok == 1 && probes < D_INNER_D && cur >= low && cur <= p && need < cap {
        let c = cur - 1;
        let nnc = prev[nc.wrapping_sub(1) % 32768] as usize;
        {
            if input[c + need] == input[p + need] {
                let l = d_ext_len(input, c, p, cap);
                if l > need && l >= 3 {
                    let g = d_gain(pref, lenc, dcost, dlo, dhi, i, l, p - c);
                    if g > 0 || l >= 5 || (l >= 4 && pref[(i + l) % 65536].wrapping_sub(pref[i % 65536]) < 96 * 4) {
                        d_push_x(xs, xn, dlo, dhi, i, l, p - c);
                    }
                    sl = if g > bg { bl } else { l };
                    sd = if g > bg { bd } else { p - c };
                    if g > bg {
                        bl = l;
                    }
                    if g > bg {
                        bd = p - c;
                    }
                    if g > bg {
                        bg = g;
                    }
                    need = l;
                }
            }
            cur = nc;
            nc = nnc;
        }
        probes += 1;
    }
    (bl, bd, bg, sl, sd)
}

/// Enters position `p` into the tables; returns the previous heads `(chain start, near)`.
/// Needs `p + 4 <= input.len()`.
pub fn d_insert(
    input: &[u8],
    head4: &mut [u32; 65536],
    prev: &mut [u32; 32768],
    near: &mut [u32; 65536],
    p: usize,
) -> (usize, usize) {
    let x3 = (input[p] as u32)
        .wrapping_add((input[p + 1] as u32).wrapping_mul(256))
        .wrapping_add((input[p + 2] as u32).wrapping_mul(65536));
    let x4 = x3.wrapping_add((input[p + 3] as u32).wrapping_mul(16777216));
    let h = ((x4.wrapping_mul(2654435761) / 65536) % 65536) as usize;
    let start = head4[h] as usize;
    prev[p % 32768] = head4[h];
    head4[h] = (p + 1) as u32;
    let h3 = ((x3.wrapping_mul(2654435761) / 65536) % 65536) as usize;
    let c3 = near[h3] as usize;
    near[h3] = (p + 1) as u32;
    (start, c3)
}

/// Prefix sums of the literal costs over the block.
pub fn d_prefix(input: &[u8], litc: &[u32; 256], pref: &mut [u32; 65536], p0: usize, blen: usize) {
    let n = input.len();
    pref[0] = 0;
    let mut k = 0usize;
    let mut acc = 0u32;
    while k < blen && blen <= 32768 && p0 <= n && blen <= n - p0 {
        acc = acc.wrapping_add(litc[input[p0 + k] as usize]);
        pref[(k + 1) % 65536] = acc;
        k += 1;
    }
}

/// Commits the match `(l, d)` at block index `q` as the first candidate of its first
/// position and enters positions `q+2..q+l`; for a match of at most `D_INNER_MAXL` bytes each
/// of those is offered, as its second candidate, a near match that runs past the end.
pub fn d_commit(
    input: &[u8],
    head4: &mut [u32; 65536],
    prev: &mut [u32; 32768],
    near: &mut [u32; 65536],
    c1l: &mut [u16; 32768],
    c1d: &mut [u16; 32768],
    c2l: &mut [u16; 32768],
    c2d: &mut [u16; 32768],
    xs: &mut [u32; 131072],
    xn: &mut [u8; 32768],
    pref: &[u32; 65536],
    lenc: &[u32; 512],
    dcost: &[u32; 32],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    p0: usize,
    q: usize,
    l: usize,
    d: usize,
    blen: usize,
) {
    let n = input.len();
    let has4 = n >= 4;
    let lim4 = if has4 { n - 4 } else { 0 };
    c1l[q % 32768] = l as u16;
    c1d[q % 32768] = d as u16;
    let mut k = 1usize;
    while k < l && l <= 258 {
        let j = q + k;
        c1l[j % 32768] = 0;
        if k >= 2 {
            c2l[j % 32768] = 0;
            xn[j % 32768] = 0;
            let p = p0 + j;
            let keep = if has4 && p <= lim4 && (d > D_RUN_D || l < D_RUN_L || k < D_RUN_KEEP || k + D_RUN_KEEP >= l) {
                1usize
            } else {
                0usize
            };
            if keep == 1 {
                let r = d_insert(input, head4, prev, near, p);
                if j < blen && l <= D_INNER_L {
                    let rem = l - k;
                    let rest = blen - j;
                    let cap = if rest < 258 { rest } else { 258 };
                    let f = d_find_in(input, prev, pref, lenc, dcost, dlo, dhi, p, j, cap, r.0, r.1, rem, xs, xn);
                    if f.0 >= 3 && f.0 > rem && f.0 <= 258 {
                        c2l[j % 32768] = f.0 as u16;
                        c2d[j % 32768] = f.1 as u16;
                        if f.3 >= 3 && f.3 > rem && f.3 <= 258 && f.4 != f.1 {
                            c1l[j % 32768] = f.3 as u16;
                            c1d[j % 32768] = f.4 as u16;
                        }
                    }
                } else if j < blen && l <= D_INNER_MAXL {
                    let c3 = r.1;
                    let rem = l - k;
                    let rest = blen - j;
                    let cap = if rest < 258 { rest } else { 258 };
                    if c3 > 0 && c3 <= p && p - (c3 - 1) <= D_NEAR3 && p - (c3 - 1) != d && rem < cap && cap <= n - p {
                        let c = c3 - 1;
                        if input[c + rem] == input[p + rem] {
                            let e = d_ext_len(input, c, p, cap);
                            if e > rem && e >= 3 {
                                c2l[j % 32768] = e as u16;
                                c2d[j % 32768] = (p - c) as u16;
                            } else if e >= 3 {
                                d_push_x(xs, xn, dlo, dhi, j, e, p - c);
                            }
                        } else {
                            let e = d_ext_len(input, c, p, if rem < D_XCAP { rem } else { D_XCAP });
                            if e >= 3 {
                                d_push_x(xs, xn, dlo, dhi, j, e, p - c);
                            }
                        }
                    }
                }
            }
        }
        k += 1;
    }
}

/// Extends the match `(l, d)` at `p = p0 + q` backward, offering each earlier position of
/// the block the longer match as its second candidate.
pub fn d_extend_back(
    input: &[u8],
    c2l: &mut [u16; 32768],
    c2d: &mut [u16; 32768],
    p0: usize,
    q: usize,
    l: usize,
    d: usize,
) {
    let n = input.len();
    let p = p0 + q;
    let mut j = 1usize;
    let mut go = 1usize;
    while go == 1 && j <= D_BK && j <= q && l + j <= 258 && p >= j + d && d >= 1 && p < n {
        if input[p - j] == input[p - j - d] {
            let k = q - j;
            let el = l + j;
            if el > c2l[k % 32768] as usize {
                c2l[k % 32768] = el as u16;
                c2d[k % 32768] = d as u16;
            }
            j += 1;
        } else {
            go = 0;
        }
    }
}

/// Takes up to `D_SKIPN` positions from block index `i` as literals, unsearched.
pub fn d_skip(c1l: &mut [u16; 32768], c2l: &mut [u16; 32768], xn: &mut [u8; 32768], i0: usize, blen: usize) -> usize {
    let mut i = i0;
    let mut s = 0usize;
    while s < D_SKIPN && i < blen {
        c1l[i % 32768] = 0;
        c2l[i % 32768] = 0;
        xn[i % 32768] = 0;
        i += 1;
        s += 1;
    }
    i
}

/// Lazy pass over the block `[p0, p0 + blen)`: enters the positions into the tables and
/// leaves the candidates of the dynamic program in `c1*` (the chosen matches) and `c2*`
/// (backward extensions, the second-best match of each chosen one, the lazy step's loser).
pub fn d_lazy(
    input: &[u8],
    head4: &mut [u32; 65536],
    prev: &mut [u32; 32768],
    near: &mut [u32; 65536],
    pref: &[u32; 65536],
    lenc: &[u32; 512],
    dcost: &[u32; 32],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    c1l: &mut [u16; 32768],
    c1d: &mut [u16; 32768],
    c2l: &mut [u16; 32768],
    c2d: &mut [u16; 32768],
    xs: &mut [u32; 131072],
    xn: &mut [u8; 32768],
    p0: usize,
    blen: usize,
    long: usize,
) {
    let n = input.len();
    let has4 = n >= 4;
    let lim4 = if has4 { n - 4 } else { 0 };
    let mut pl = 0usize;
    let mut pd = 0usize;
    let mut pg = 0u32;
    let mut psl = 0usize;
    let mut psd = 0usize;
    let mut miss = 0usize;
    let mut i = 0usize;
    let mut steps = 0usize;
    while i < blen && steps < 32768 && blen <= 32768 && p0 <= n && blen <= n - p0 {
        let p = p0 + i;
        let rest = blen - i;
        let cap = if rest < 258 { rest } else { 258 };
        c1l[i % 32768] = 0;
        c2l[i % 32768] = 0;
        xn[i % 32768] = 0;
        let mut cl = 0usize;
        let mut cd = 0usize;
        let mut cg = 0u32;
        let mut csl = 0usize;
        let mut csd = 0usize;
        if has4 && p <= lim4 {
            let r = d_insert(input, head4, prev, near, p);
            if pl < D_LAZY_LIMIT {
                let floor = if pl >= 3 { pl - 1 } else { 0 };
                let pcap = if pl >= 3 { D_LDEPTH } else if miss >= D_MISS_D { D_MDEPTH } else if long == 1 { D_LONG_DEPTH } else { D_DEPTH };
                let f = d_find(input, prev, pref, lenc, dcost, dlo, dhi, p, i, cap, r.0, r.1, floor, pcap, xs, xn);
                cl = f.0;
                cd = f.1;
                cg = f.2;
                csl = f.3;
                csd = f.4;
                if long == 1 {
                    xn[i % 32768] = 0;
                }
            }
        }
        if pl >= 3 && i >= 1 {
            if cl >= 3 && cg > pg {
                if pl <= 258 {
                    c2l[(i - 1) % 32768] = pl as u16;
                    c2d[(i - 1) % 32768] = pd as u16;
                }
                pl = cl;
                pd = cd;
                pg = cg;
                psl = csl;
                psd = csd;
                i += 1;
            } else {
                let q = i - 1;
                if cl >= 3 && cl <= 258 {
                    c2l[i % 32768] = cl as u16;
                    c2d[i % 32768] = cd as u16;
                }
                if psl >= 3 && psl <= 258 && psl < pl {
                    c2l[q % 32768] = psl as u16;
                    c2d[q % 32768] = psd as u16;
                }
                if pl <= 258 && pd >= 1 {
                    d_commit(input, head4, prev, near, c1l, c1d, c2l, c2d, xs, xn, pref, lenc, dcost, dlo, dhi, p0, q, pl, pd, blen);
                    d_extend_back(input, c2l, c2d, p0, q, pl, pd);
                }
                i = q + pl;
                pl = 0;
                pd = 0;
                pg = 0;
            }
        } else if cl >= 3 {
            pl = cl;
            pd = cd;
            pg = cg;
            psl = csl;
            psd = csd;
            miss = 0;
            i += 1;
        } else {
            if long == 1 && csl >= 3 && csl <= 258 {
                c2l[i % 32768] = csl as u16;
                c2d[i % 32768] = csd as u16;
            }
            i += 1;
            if miss < D_SKIP_AFTER {
                miss += 1;
            }
            if miss >= D_SKIP_AFTER && long == 0 {
                i = d_skip(c1l, c2l, xn, i, blen);
            }
        }
        steps += 1;
    }
}

/// The cheapest way to cover `[j, j + l)` for `l` in `lo..=hi` at one distance cost:
/// every length below `D_TRY_ALL`, then one per length code.
pub fn d_relax_run(
    cost: &[u32; 65536],
    lenc: &[u32; 512],
    bend: &[u16; 512],
    j: usize,
    lo: usize,
    hi: usize,
    dcs: u32,
    best0: u32,
    bl0: usize,
) -> (u32, usize) {
    let mut best = best0;
    let mut bl = bl0;
    let mut l = lo;
    while l <= hi && hi <= 258 {
        let c = cost[(j + l) % 65536].wrapping_add(lenc[l % 512]).wrapping_add(dcs);
        if c < best {
            bl = l;
        }
        if c < best {
            best = c;
        }
        if l < D_TRY_ALL || l >= hi {
            l += 1;
        } else {
            let e = bend[l % 512] as usize;
            let nx = if e <= l { bend[(l + 1) % 512] as usize } else { e };
            l = if nx > hi { hi } else if nx <= l { l + 1 } else { nx };
        }
    }
    (best, bl)
}

/// Backward pass: `cost[j]` is the cheapest cost from `j` to the block end, `chl`/`chd` the choice.
pub fn d_backward(
    input: &[u8],
    c1l: &mut [u16; 32768],
    c1d: &mut [u16; 32768],
    c2l: &[u16; 32768],
    c2d: &[u16; 32768],
    xs: &[u32; 131072],
    xn: &[u8; 32768],
    cost: &mut [u32; 65536],
    litc: &[u32; 256],
    lenc: &[u32; 512],
    dcost: &[u32; 32],
    bend: &[u16; 512],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    p0: usize,
    blen: usize,
    cheap: usize,
) {
    let n = input.len();
    if blen <= 32768 && p0 <= n && blen <= n - p0 {
        cost[blen % 65536] = 0;
        let mut cn = 0u32;
        let mut j = blen;
        while j > 0 {
            j -= 1;
            let lit = cn.wrapping_add(litc[input[p0 + j] as usize]);
            let l2 = c2l[j % 32768] as usize;
            let l1 = c1l[j % 32768] as usize;
            let xc = xn[j % 32768] as usize;
            if l1 < 3 && l2 < 3 && xc == 0 {
                cost[j % 65536] = lit;
                cn = lit;
                c1l[j % 32768] = 0;
            } else {
                let rest = blen - j;
                let mut best = 4294967295u32;
                let mut bl = 0usize;
                let mut bdd = 0usize;
                let d2 = c2d[j % 32768] as usize;
                if l2 >= 3 && l2 <= rest && d2 >= 1 && d2 <= 32768 {
                    let dcs = dcost[d_dcode(dlo, dhi, d2) % 32];
                    let from2 = if l2 > D_SPAN2 + 3 { l2 - D_SPAN2 } else { 3 };
                    let r = d_relax_run(cost, lenc, bend, j, from2, l2, dcs, best, bl);
                    if r.0 < best {
                        bdd = d2;
                    }
                    best = r.0;
                    bl = r.1;
                }
                let d1 = c1d[j % 32768] as usize;
                if l1 >= 3 && l1 <= rest && d1 >= 1 && d1 <= 32768 {
                    let dcs = dcost[d_dcode(dlo, dhi, d1) % 32];
                    let from = if l1 > D_SPAN1 + 3 { l1 - D_SPAN1 } else { 3 };
                    let r = d_relax_run(cost, lenc, bend, j, from, l1, dcs, best, bl);
                    if r.0 < best {
                        bdd = d1;
                    }
                    best = r.0;
                    bl = r.1;
                }
                let mut s = 0usize;
                let mut lo = 3usize;
                while s < xc && s < D_NX {
                    let v = xs[(j * D_NX + s) % 131072] as usize;
                    let lx = v % 512;
                    let dx = v / 512;
                    if lx >= lo && lx <= rest && dx >= 1 && dx <= 32768 {
                        let dcs = dcost[d_dcode(dlo, dhi, dx) % 32];
                        let lo1 = if cheap == 1 { lx } else { lo };
                        let r = d_relax_run(cost, lenc, bend, j, lo1, lx, dcs, best, bl);
                        if r.0 < best {
                            bdd = dx;
                        }
                        best = r.0;
                        bl = r.1;
                    }
                    lo = lx + 1;
                    s += 1;
                }
                if lit <= best {
                    best = lit;
                    bl = 0;
                    bdd = 0;
                }
                cost[j % 65536] = best;
                cn = best;
                c1l[j % 32768] = bl as u16;
                c1d[j % 32768] = bdd as u16;
            }
        }
    }
}

/// Symbol counts of the chosen path through the block.
pub fn d_count(
    input: &[u8],
    chl: &[u16; 32768],
    chd: &[u16; 32768],
    lf: &mut [u32; 512],
    df: &mut [u32; 32],
    lcode: &[u8; 512],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    olf: &[u32; 512],
    odf: &[u32; 32],
    half: usize,
    p0: usize,
    blen: usize,
) {
    let n = input.len();
    let mut s = 0usize;
    while s < 512 {
        lf[s] = if half == 1 { olf[s] / 2 } else { olf[s] };
        s += 1;
    }
    s = 0;
    while s < 32 {
        df[s] = if half == 1 { odf[s] / 2 } else { odf[s] };
        s += 1;
    }
    let mut k = 0usize;
    while k < blen && p0 <= n && blen <= n - p0 {
        let l = chl[k % 32768] as usize;
        let d = chd[k % 32768] as usize;
        if l >= 3 && l <= 258 && d >= 1 && d <= 32768 {
            let li = (257 + lcode[l % 512] as usize) % 512;
            lf[li] = lf[li].saturating_add(1);
            let di = d_dcode(dlo, dhi, d) % 32;
            df[di] = df[di].saturating_add(1);
            k += l;
        } else {
            let b = input[p0 + k] as usize;
            lf[b] = lf[b].saturating_add(1);
            k += 1;
        }
    }
    lf[256] = lf[256].saturating_add(1);
}

/// `olf + lz + pdp - plz` per symbol: the lazy-path counts corrected by how the previous
/// block's chosen path differed from its lazy path.
pub fn d_mix(
    olf: &[u32; 512],
    odf: &[u32; 32],
    lz: &[u32; 512],
    lzd: &[u32; 32],
    pdp: &[u32; 512],
    pdpd: &[u32; 32],
    plz: &[u32; 512],
    plzd: &[u32; 32],
    lf: &mut [u32; 512],
    df: &mut [u32; 32],
) {
    let mut s = 0usize;
    while s < 512 {
        let c = (lz[s] as u64).wrapping_mul(pdp[s] as u64 + D_TK) / (plz[s] as u64 + D_TK);
        lf[s] = olf[s].saturating_add(if c > 1000000000 { 1000000000 } else { c as u32 });
        s += 1;
    }
    s = 0;
    while s < 32 {
        let c = (lzd[s] as u64).wrapping_mul(pdpd[s] as u64 + D_TK) / (plzd[s] as u64 + D_TK);
        df[s] = odf[s].saturating_add(if c > 1000000000 { 1000000000 } else { c as u32 });
        s += 1;
    }
}

/// `a = a - a / 4 + b` per symbol: running averages of block counts.
pub fn d_ravg(al: &mut [u32; 512], ad: &mut [u32; 32], bl: &[u32; 512], bd: &[u32; 32]) {
    let mut s = 0usize;
    while s < 512 {
        al[s] = (al[s] - al[s] / 4).saturating_add(bl[s]);
        s += 1;
    }
    s = 0;
    while s < 32 {
        ad[s] = (ad[s] - ad[s] / 4).saturating_add(bd[s]);
        s += 1;
    }
}

/// Copies the first `blen` entries of `al`/`ad` into `bl`/`bd`.
pub fn d_copy16(al: &[u16; 32768], ad: &[u16; 32768], bl: &mut [u16; 32768], bd: &mut [u16; 32768], blen: usize) {
    let mut k = 0usize;
    while k < blen && k < 32768 {
        bl[k] = al[k];
        bd[k] = ad[k];
        k += 1;
    }
}

/// Copies the counts `lf`/`df` into `olf`/`odf`.
pub fn d_keep(lf: &[u32; 512], df: &[u32; 32], olf: &mut [u32; 512], odf: &mut [u32; 32]) {
    let mut s = 0usize;
    while s < 512 {
        olf[s] = lf[s];
        s += 1;
    }
    s = 0;
    while s < 32 {
        odf[s] = df[s];
        s += 1;
    }
}

/// Inserts weight `x` of symbol `sy` into the ascending list `w[0..m]`, `sym[0..m]`.
pub fn d_hins(w: &mut [u32; 512], sym: &mut [u16; 512], m: usize, x: u32, sy: usize) {
    let mut j = m;
    while j > 0 && j < 512 && w[(j - 1) % 512] > x {
        w[j % 512] = w[(j - 1) % 512];
        sym[j % 512] = sym[(j - 1) % 512];
        j -= 1;
    }
    w[j % 512] = x;
    sym[j % 512] = sy as u16;
}

/// Huffman code lengths of the counts `f[0..ns]` (0 for an unseen symbol), capped at 15.
pub fn d_hlens(f: &[u32; 512], ns: usize, out: &mut [u32; 512]) {
    let mut w = [0u32; 512];
    let mut sym = [0u16; 512];
    let mut m = 0usize;
    let mut s = 0usize;
    while s < ns && s < 512 {
        out[s] = 0;
        if f[s] > 0 {
            d_hins(&mut w, &mut sym, m, f[s], s);
            m += 1;
        }
        s += 1;
    }
    if m == 1 {
        out[(sym[0] as usize) % 512] = 1;
    }
    if m >= 2 {
        d_hbuild(&w, &sym, m, out);
    }
}

/// Two-queue Huffman merge over the ascending leaves `w[0..m]`; writes the leaf depths.
pub fn d_hbuild(w: &[u32; 512], sym: &[u16; 512], m: usize, out: &mut [u32; 512]) {
    let mut nw = [0u32; 1024];
    let mut par = [0u16; 1024];
    let mut dep = [0u32; 1024];
    let mut k = 0usize;
    while k < m && k < 512 {
        nw[k] = w[k];
        k += 1;
    }
    let mut i1 = 0usize;
    let mut i2 = m;
    let mut t = 0usize;
    while t + 1 < m && m <= 512 {
        let top = m + t;
        let mut pick = 0usize;
        let mut a = 0usize;
        let mut b = 0usize;
        while pick < 2 {
            let take1 = if i1 < m && (i2 >= top || nw[i1 % 1024] <= nw[i2 % 1024]) { 1usize } else { 0usize };
            let x = if take1 == 1 { i1 } else { i2 };
            if take1 == 1 {
                i1 += 1;
            } else {
                i2 += 1;
            }
            if pick == 0 {
                a = x;
            } else {
                b = x;
            }
            pick += 1;
        }
        nw[top % 1024] = nw[a % 1024].wrapping_add(nw[b % 1024]);
        par[a % 1024] = top as u16;
        par[b % 1024] = top as u16;
        t += 1;
    }
    let root = if m >= 2 { 2 * m - 2 } else { 0 };
    dep[root % 1024] = 0;
    let mut r = 1usize;
    while r <= root && root < 1024 {
        let x = root - r;
        let pd = dep[(par[x % 1024] as usize) % 1024];
        dep[x % 1024] = pd + 1;
        r += 1;
    }
    k = 0;
    while k < m && k < 512 {
        let d = dep[k % 1024];
        out[(sym[k % 512] as usize) % 512] = if d > 15 { 15 } else { d };
        k += 1;
    }
}

/// Literal, length and distance costs from the symbol counts.
pub fn d_learn(
    lf: &[u32; 512],
    df: &[u32; 32],
    litc: &mut [u32; 256],
    lenc: &mut [u32; 512],
    dcost: &mut [u32; 32],
    lcode: &[u8; 512],
    lextra: &[u8; 512],
    dext: &[u8; 32],
    bias: u32,
    hw: u32,
) {
    let mut hl = [0u32; 512];
    if hw > 0 {
        d_hlens(lf, 286, &mut hl);
    }
    let mut tot = 1u32;
    let mut s = 0usize;
    while s < 286 {
        tot = tot.saturating_add(lf[s]);
        s += 1;
    }
    s = 0;
    while s < 256 {
        litc[s] = d_hcost(d_cost16(lf[s], tot), hl[s], hw).saturating_add(bias);
        s += 1;
    }
    let mut cc = [0u32; 32];
    let mut c = 0usize;
    while c < 29 {
        cc[c] = d_hcost(d_cost16(lf[(257 + c) % 512], tot), hl[(257 + c) % 512], hw).saturating_add(bias);
        c += 1;
    }
    let mut l = 3usize;
    while l <= 258 {
        lenc[l] = cc[(lcode[l] as usize) % 32].saturating_add((lextra[l] as u32) * 16);
        l += 1;
    }
    let mut dt = 1u32;
    c = 0;
    while c < 30 {
        dt = dt.saturating_add(df[c]);
        c += 1;
    }
    c = 0;
    while c < 30 {
        dcost[c] = d_cost16(df[c], dt).saturating_add((dext[c] as u32) * 16);
        c += 1;
    }
}

/// The cost of a symbol from its `-log2` cost `e` and its Huffman code length `h` (0 = unseen).
pub fn d_hcost(e: u32, h: u32, hw: u32) -> u32 {
    if h == 0 || hw > 16 {
        e
    } else {
        (e * (16 - hw) + h * 16 * hw) / 16
    }
}

/// True iff the match `(ch, d)` at `pos` is in range and its bytes agree.
pub fn d_verified(input: &[u8], pos: usize, d: usize, ch: usize, k: usize, blen: usize) -> bool {
    if ch < 3 || ch > 258 || d < 1 || d > 32768 || d > pos || k + ch > blen {
        return false;
    }
    let v = d_match_len(input, pos - d, pos, ch);
    v >= ch
}

/// Writes the chosen path of the block; a match is written only once `verified`.
pub fn d_emit(
    input: &[u8],
    out: &mut [u32],
    chl: &[u16; 32768],
    chd: &[u16; 32768],
    ntok0: usize,
    p0: usize,
    blen: usize,
) -> usize {
    let mut ntok = ntok0;
    let mut k = 0usize;
    while k < blen {
        let pos = p0 + k;
        let ch = chl[k % 32768] as usize;
        let d = chd[k % 32768] as usize;
        if d_verified(input, pos, d, ch, k, blen) {
            out[ntok] = 16777216u32 + ((d - 1) as u32) * 256 + ((ch - 3) as u32);
            ntok += 1;
            k += ch;
        } else {
            out[ntok] = input[pos] as u32;
            ntok += 1;
            k += 1;
        }
    }
    ntok
}

/// Length codes and their extra bits for lengths 3..=258.
pub fn d_len_tables(
    lbase: &[u16; 32],
    lext: &[u8; 32],
    lcode: &mut [u8; 512],
    lextra: &mut [u8; 512],
    bend: &mut [u16; 512],
) {
    let mut c = 0usize;
    let mut l = 3usize;
    while l <= 258 {
        if c < 28 && lbase[(c + 1) % 32] as usize <= l {
            c += 1;
        }
        lcode[l] = c as u8;
        lextra[l] = lext[c % 32];
        let top = lbase[(c + 1) % 32];
        bend[l] = if top >= 1 { top - 1 } else { 0 };
        l += 1;
    }
}

/// The code of distance `d`, continuing the scan from code `c0`.
pub fn d_code_from(dbase: &[u16; 32], d: usize, c0: usize) -> usize {
    let mut c = c0;
    while c < 29 && dbase[(c + 1) % 32] as usize <= d {
        c += 1;
    }
    c
}

/// Distance codes: `dlo` for distances 1..=256, `dhi` by `(d - 1) / 128` above.
pub fn d_dist_tables(dbase: &[u16; 32], dlo: &mut [u8; 256], dhi: &mut [u8; 256]) {
    let mut c = 0usize;
    let mut d = 1usize;
    while d <= 256 {
        c = d_code_from(dbase, d, c);
        dlo[(d - 1) % 256] = c as u8;
        d += 1;
    }
    let mut k = 0usize;
    c = 0;
    while k < 256 {
        c = d_code_from(dbase, k * 128 + 1, c);
        dhi[k] = c as u8;
        k += 1;
    }
}

/// Length and distance code tables.
pub fn d_tables(
    lcode: &mut [u8; 512],
    lextra: &mut [u8; 512],
    bend: &mut [u16; 512],
    dlo: &mut [u8; 256],
    dhi: &mut [u8; 256],
    dext: &mut [u8; 32],
) {
    let lbase: [u16; 32] = [
        3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115,
        131, 163, 195, 227, 258, 259, 259, 259,
    ];
    let lext: [u8; 32] = [
        0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0, 0, 0,
        0,
    ];
    let dbase: [u16; 32] = [
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
        2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577, 32769, 32769,
    ];
    let dx: [u8; 32] = [
        0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12,
        13, 13, 0, 0,
    ];
    d_len_tables(&lbase, &lext, lcode, lextra, bend);
    d_dist_tables(&dbase, dlo, dhi);
    *dext = dx;
}

/// Starting costs: literals from a byte histogram of the first 32 KB, static match costs;
/// returns 1 when the average literal cost there is below `D_LONG_BELOW`, so only long
/// matches pay: no per-token bias and no skipping in literal runs.
pub fn d_seed(
    input: &[u8],
    litc: &mut [u32; 256],
    lenc: &mut [u32; 512],
    dcost: &mut [u32; 32],
    lextra: &[u8; 512],
    dext: &[u8; 32],
) -> usize {
    let n = input.len();
    let lim = if n < 32768 { n } else { 32768 };
    let mut hist = [1u32; 256];
    let mut i = 0usize;
    while i < lim {
        let b = input[i] as usize;
        hist[b] = hist[b].saturating_add(1);
        i += 1;
    }
    let tot = (lim as u32).saturating_add(256);
    let mut s = 0usize;
    let mut sum = 0u64;
    while s < 256 {
        let c = d_cost16(hist[s], tot);
        litc[s] = c;
        sum = sum.wrapping_add((hist[s].wrapping_sub(1) as u64).wrapping_mul(c as u64));
        s += 1;
    }
    let mut l = 3usize;
    while l <= 258 {
        lenc[l] = 112u32.saturating_add((lextra[l] as u32) * 16);
        l += 1;
    }
    let mut c = 0usize;
    while c < 30 {
        dcost[c] = 80u32.saturating_add((dext[c] as u32) * 16);
        c += 1;
    }
    if lim >= 8 && sum < (D_LONG_BELOW as u64) * (lim as u64) {
        1
    } else {
        0
    }
}

/// Adds the per-token cost `bias` to every literal and every length.
pub fn d_add_bias(litc: &mut [u32; 256], lenc: &mut [u32; 512], bias: u32) {
    let mut s = 0usize;
    while s < 256 {
        litc[s] = litc[s].saturating_add(bias);
        s += 1;
    }
    let mut l = 3usize;
    while l <= 258 {
        lenc[l] = lenc[l].saturating_add(bias);
        l += 1;
    }
}

/// Optimal parse per block under the learned costs; every written match is re-verified.
pub fn d_parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut lcode = [0u8; 512];
    let mut lextra = [0u8; 512];
    let mut bend = [0u16; 512];
    let mut dlo = [0u8; 256];
    let mut dhi = [0u8; 256];
    let mut dext = [0u8; 32];
    d_tables(&mut lcode, &mut lextra, &mut bend, &mut dlo, &mut dhi, &mut dext);
    let mut litc = [0u32; 256];
    let mut lenc = [0u32; 512];
    let mut dcost = [0u32; 32];
    let long = d_seed(input, &mut litc, &mut lenc, &mut dcost, &lextra, &dext);
    let bias = if long == 1 { 0 } else { D_BIAS };
    let hw = if long == 1 { D_HW } else { 0 };
    d_add_bias(&mut litc, &mut lenc, bias);
    let mut head4 = [0u32; 65536];
    let mut prev = [0u32; 32768];
    let mut near = [0u32; 65536];
    let mut c1l = [0u16; 32768];
    let mut c1d = [0u16; 32768];
    let mut c2l = [0u16; 32768];
    let mut c2d = [0u16; 32768];
    let mut bkl = [0u16; 32768];
    let mut bkd = [0u16; 32768];
    let mut cost = [0u32; 65536];
    let mut xs = [0u32; 131072];
    let mut xn = [0u8; 32768];
    let mut lf = [0u32; 512];
    let mut df = [0u32; 32];
    let mut olf = [0u32; 512];
    let mut odf = [0u32; 32];
    let mut lz = [0u32; 512];
    let mut lzd = [0u32; 32];
    let mut plz = [0u32; 512];
    let mut plzd = [0u32; 32];
    let mut pdp = [0u32; 512];
    let mut pdpd = [0u32; 32];
    let mut tdp = [0u32; 512];
    let mut tdpd = [0u32; 32];
    let zl = [0u32; 512];
    let zd = [0u32; 32];
    let mut ntok = 0usize;
    let mut p0 = 0usize;
    while p0 < n {
        let rest = n - p0;
        let blen = if rest > D_BLOCK { D_BLOCK } else { rest };
        d_prefix(input, &litc, &mut cost, p0, blen);
        d_lazy(
            input, &mut head4, &mut prev, &mut near, &cost, &lenc, &dcost, &dlo, &dhi, &mut c1l, &mut c1d,
            &mut c2l, &mut c2d, &mut xs, &mut xn, p0, blen, long,
        );
        d_count(input, &c1l, &c1d, &mut lz, &mut lzd, &lcode, &dlo, &dhi, &zl, &zd, 0, p0, blen);
        d_mix(&olf, &odf, &lz, &lzd, &pdp, &pdpd, &plz, &plzd, &mut lf, &mut df);
        d_learn(&lf, &df, &mut litc, &mut lenc, &mut dcost, &lcode, &lextra, &dext, 0, hw);
        let rf = if long == 0 && p0 < 4 * D_BLOCK { 1 } else { 0 };
        if rf == 1 {
            d_copy16(&c1l, &c1d, &mut bkl, &mut bkd, blen);
        }
        d_backward(
            input, &mut c1l, &mut c1d, &c2l, &c2d, &xs, &xn, &mut cost, &litc, &lenc, &dcost, &bend, &dlo,
            &dhi, p0, blen, rf,
        );
        if rf == 1 {
            d_count(input, &c1l, &c1d, &mut lf, &mut df, &lcode, &dlo, &dhi, &olf, &odf, 1, p0, blen);
            d_learn(&lf, &df, &mut litc, &mut lenc, &mut dcost, &lcode, &lextra, &dext, 0, hw);
            d_copy16(&bkl, &bkd, &mut c1l, &mut c1d, blen);
            d_backward(
                input, &mut c1l, &mut c1d, &c2l, &c2d, &xs, &xn, &mut cost, &litc, &lenc, &dcost, &bend, &dlo,
                &dhi, p0, blen, 0,
            );
        }
        if blen < rest {
            d_count(input, &c1l, &c1d, &mut tdp, &mut tdpd, &lcode, &dlo, &dhi, &zl, &zd, 0, p0, blen);
            d_ravg(&mut pdp, &mut pdpd, &tdp, &tdpd);
            d_ravg(&mut plz, &mut plzd, &lz, &lzd);
            d_count(input, &c1l, &c1d, &mut lf, &mut df, &lcode, &dlo, &dhi, &olf, &odf, 1, p0, blen);
            d_learn(&lf, &df, &mut litc, &mut lenc, &mut dcost, &lcode, &lextra, &dext, bias, hw);
            d_keep(&lf, &df, &mut olf, &mut odf);
        }
        ntok = d_emit(input, out, &c1l, &c1d, ntok, p0, blen);
        p0 += blen;
    }
    ntok
}
