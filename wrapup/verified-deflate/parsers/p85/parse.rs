//! The slot: cost-aware lazy matching refined by a block-wise optimal parse.
//!
//! * A lazy pass walks each block with a 4-byte hash chain and a single-entry 3-byte
//!   table, choosing matches by the bits they save under a learned cost model.
//! * Every chosen match is extended backward over the bytes before it; those longer
//!   starts, the runner-up of each search, the matches the lazy step rejected, near
//!   matches that run past a short chosen one and the chosen ones become the candidates
//!   of a backward dynamic program over the block under the same costs.
//! * Inside a literal run the chain walk is shallow, and after a long run every fourth
//!   position is searched.
//! * Costs: every literal byte, length code and distance code has a cost in 1/16 bits,
//!   taken from the symbol counts of the previous block's chosen path.
//! * The emission re-verifies every chosen match with `match_len` before writing it.
//!
//! Dials are set for about 1.65× the incumbent. On corpus-stage1, 3 measured reps:
//! 1.65× balanced time, 34.06% mean size (4,906,237 bytes). The proof does not
//! mention these values.
//!
//! Tokens: `t < 256` literal, else `2^24 + (dist-1)*256 + (len-3)`.

pub const DEPTH: usize = 128;
pub const LDEPTH: usize = 56;
pub const MDEPTH: usize = 32;
pub const MISS_D: usize = 2;
pub const NICE: usize = 258;
pub const BLOCK: usize = 32768;
pub const NEAR3: usize = 32768;
pub const TRY_ALL: usize = 40;
pub const MISS_COST: u32 = 160;
pub const BIAS: u32 = 12;
pub const INNER_MAXL: usize = 64;
pub const LAZY_LIMIT: usize = 258;
pub const BK: usize = 128;
pub const LONG_BELOW: u32 = 52;
pub const SKIP_AFTER: usize = 128;
pub const SKIPN: usize = 3;
pub const RUN_D: usize = 16;
pub const RUN_L: usize = 64;
pub const RUN_KEEP: usize = 16;
pub const SPAN1: usize = 24;
pub const SPAN2: usize = 8;
pub const INNER_L: usize = 28;
pub const INNER_D: usize = 16;

/// How many bytes agree at `a` and `b`, up to `cap`.
pub fn match_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let mut l = 0usize;
    while l < cap && input[b + l] == input[a + l] {
        l += 1;
    }
    l
}

/// How many bytes agree at `a < b` and `b`, up to `cap`, for the search: 0 unless
/// `b + cap` is within the input.
pub fn ext_len(input: &[u8], a: usize, b: usize, cap: usize) -> usize {
    let n = input.len();
    let mut l = 0usize;
    if a < b && b <= n && cap <= n - b {
        let mut go = 1usize;
        while go == 1 && l < cap && cap - l >= 8 {
            let x = load64(input, a + l) ^ load64(input, b + l);
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
pub fn load64(input: &[u8], p: usize) -> u64 {
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

/// `16 * log2(total / freq)`, rounded down to 1/16 bit; `MISS_COST` for an unseen symbol.
pub fn cost16(freq: u32, total: u32) -> u32 {
    if freq == 0 {
        return MISS_COST;
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
pub fn dcode(dlo: &[u8; 256], dhi: &[u8; 256], d: usize) -> usize {
    if d <= 256 {
        let k = if d >= 1 { d - 1 } else { 0 };
        dlo[k % 256] as usize
    } else {
        dhi[((d - 1) / 128) % 256] as usize
    }
}

/// Bits saved by the match `(l, d)` at block index `i`: literal cost of the covered bytes
/// minus the match cost, or 0 when the match costs more.
pub fn gain(
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
    let mc = lenc[l % 512].saturating_add(dcost[dcode(dlo, dhi, d) % 32]);
    if lit > mc {
        lit - mc
    } else {
        0
    }
}

/// The match at `p` (block index `i`) saving the most bits among the near 3-byte candidate
/// `c3` and `pcap` entries of the chain from `start`, looking only at matches longer than
/// `floor`: `(len, dist, gain)`.
pub fn find(
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
) -> (usize, usize, u32, usize, usize) {
    let mut bl = 0usize;
    let mut bd = 0usize;
    let mut bg = 0u32;
    let mut sl = 0usize;
    let mut sd = 0usize;
    let mut need = floor;
    let n = input.len();
    let ok = if p <= n && cap <= n - p { 1usize } else { 0usize };
    if ok == 1 && c3 > 0 && c3 <= p && p - (c3 - 1) <= NEAR3 && need < cap {
        let c = c3 - 1;
        if input[c + need] == input[p + need] {
            let l = ext_len(input, c, p, cap);
            if l >= 3 && l > need {
                let g = gain(pref, lenc, dcost, dlo, dhi, i, l, p - c);
                if g > 0 {
                    bl = l;
                    bd = p - c;
                    bg = g;
                    need = l;
                }
            }
        }
    }
    let mut cur = start;
    let mut probes = 0usize;
    while ok == 1 && probes < pcap && cur > 0 && cur <= p {
        let c = cur - 1;
        if p - c <= 32768 && need < cap {
            if input[c + need] == input[p + need] {
                let l = ext_len(input, c, p, cap);
                if l > need && l >= 3 {
                    let g = gain(pref, lenc, dcost, dlo, dhi, i, l, p - c);
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
            if need >= NICE {
                cur = 0;
            } else {
                cur = prev[c % 32768] as usize;
            }
        } else {
            cur = 0;
        }
        probes += 1;
    }
    (bl, bd, bg, sl, sd)
}

/// `find` with `INNER_D` chain entries, for the inner positions of a committed match.
pub fn find_in(
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
) -> (usize, usize, u32, usize, usize) {
    let mut bl = 0usize;
    let mut bd = 0usize;
    let mut bg = 0u32;
    let mut sl = 0usize;
    let mut sd = 0usize;
    let mut need = floor;
    let n = input.len();
    let ok = if p <= n && cap <= n - p { 1usize } else { 0usize };
    if ok == 1 && c3 > 0 && c3 <= p && p - (c3 - 1) <= NEAR3 && need < cap {
        let c = c3 - 1;
        if input[c + need] == input[p + need] {
            let l = ext_len(input, c, p, cap);
            if l >= 3 && l > need {
                let g = gain(pref, lenc, dcost, dlo, dhi, i, l, p - c);
                if g > 0 {
                    bl = l;
                    bd = p - c;
                    bg = g;
                    need = l;
                }
            }
        }
    }
    let mut cur = start;
    let mut probes = 0usize;
    while ok == 1 && probes < INNER_D && cur > 0 && cur <= p {
        let c = cur - 1;
        if p - c <= 32768 && need < cap {
            if input[c + need] == input[p + need] {
                let l = ext_len(input, c, p, cap);
                if l > need && l >= 3 {
                    let g = gain(pref, lenc, dcost, dlo, dhi, i, l, p - c);
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
            if need >= NICE {
                cur = 0;
            } else {
                cur = prev[c % 32768] as usize;
            }
        } else {
            cur = 0;
        }
        probes += 1;
    }
    (bl, bd, bg, sl, sd)
}

/// Enters position `p` into the tables; returns the previous heads `(chain start, near)`.
/// Needs `p + 4 <= input.len()`.
pub fn insert(
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
pub fn prefix(input: &[u8], litc: &[u32; 256], pref: &mut [u32; 65536], p0: usize, blen: usize) {
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
/// position and enters positions `q+2..q+l`; for a match of at most `INNER_MAXL` bytes each
/// of those is offered, as its second candidate, a near match that runs past the end.
pub fn commit(
    input: &[u8],
    head4: &mut [u32; 65536],
    prev: &mut [u32; 32768],
    near: &mut [u32; 65536],
    c1l: &mut [u16; 32768],
    c1d: &mut [u16; 32768],
    c2l: &mut [u16; 32768],
    c2d: &mut [u16; 32768],
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
            let p = p0 + j;
            let keep = if has4 && p <= lim4 && (d > RUN_D || l < RUN_L || k < RUN_KEEP || k + RUN_KEEP >= l) {
                1usize
            } else {
                0usize
            };
            if keep == 1 {
                let r = insert(input, head4, prev, near, p);
                if j < blen && l <= INNER_L {
                    let rem = l - k;
                    let rest = blen - j;
                    let cap = if rest < 258 { rest } else { 258 };
                    let f = find_in(input, prev, pref, lenc, dcost, dlo, dhi, p, j, cap, r.0, r.1, rem);
                    if f.0 >= 3 && f.0 > rem && f.0 <= 258 {
                        c2l[j % 32768] = f.0 as u16;
                        c2d[j % 32768] = f.1 as u16;
                        if f.3 >= 3 && f.3 > rem && f.3 <= 258 && f.4 != f.1 {
                            c1l[j % 32768] = f.3 as u16;
                            c1d[j % 32768] = f.4 as u16;
                        }
                    }
                } else if j < blen && l <= INNER_MAXL {
                    let c3 = r.1;
                    let rem = l - k;
                    let rest = blen - j;
                    let cap = if rest < 258 { rest } else { 258 };
                    if c3 > 0 && c3 <= p && p - (c3 - 1) <= NEAR3 && p - (c3 - 1) != d && rem < cap && cap <= n - p {
                        let c = c3 - 1;
                        if input[c + rem] == input[p + rem] {
                            let e = ext_len(input, c, p, cap);
                            if e > rem && e >= 3 {
                                c2l[j % 32768] = e as u16;
                                c2d[j % 32768] = (p - c) as u16;
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
pub fn extend_back(
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
    while go == 1 && j <= BK && j <= q && l + j <= 258 && p >= j + d && d >= 1 && p < n {
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

/// Takes up to `SKIPN` positions from block index `i` as literals, unsearched.
pub fn skip(c1l: &mut [u16; 32768], c2l: &mut [u16; 32768], i0: usize, blen: usize) -> usize {
    let mut i = i0;
    let mut s = 0usize;
    while s < SKIPN && i < blen {
        c1l[i % 32768] = 0;
        c2l[i % 32768] = 0;
        i += 1;
        s += 1;
    }
    i
}

/// Lazy pass over the block `[p0, p0 + blen)`: enters the positions into the tables and
/// leaves the candidates of the dynamic program in `c1*` (the chosen matches) and `c2*`
/// (backward extensions, the second-best match of each chosen one, the lazy step's loser).
pub fn lazy(
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
        let mut cl = 0usize;
        let mut cd = 0usize;
        let mut cg = 0u32;
        let mut csl = 0usize;
        let mut csd = 0usize;
        if has4 && p <= lim4 {
            let r = insert(input, head4, prev, near, p);
            if pl < LAZY_LIMIT {
                let floor = if pl >= 3 { pl - 1 } else { 0 };
                let pcap = if pl >= 3 { LDEPTH } else if miss >= MISS_D { MDEPTH } else { DEPTH };
                let f = find(input, prev, pref, lenc, dcost, dlo, dhi, p, i, cap, r.0, r.1, floor, pcap);
                cl = f.0;
                cd = f.1;
                cg = f.2;
                csl = f.3;
                csd = f.4;
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
                    commit(input, head4, prev, near, c1l, c1d, c2l, c2d, pref, lenc, dcost, dlo, dhi, p0, q, pl, pd, blen);
                    extend_back(input, c2l, c2d, p0, q, pl, pd);
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
            i += 1;
            if miss < SKIP_AFTER {
                miss += 1;
            }
            if miss >= SKIP_AFTER && long == 0 {
                i = skip(c1l, c2l, i, blen);
            }
        }
        steps += 1;
    }
}

/// The cheapest way to cover `[j, j + l)` for `l` in `lo..=hi` at one distance cost:
/// every length below `TRY_ALL`, then one per length code.
pub fn relax_run(
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
    let mut steps = 0usize;
    while l <= hi && hi <= 258 && steps < 300 {
        let c = cost[(j + l) % 65536].wrapping_add(lenc[l % 512]).wrapping_add(dcs);
        if c < best {
            bl = l;
        }
        if c < best {
            best = c;
        }
        if l < TRY_ALL || l >= hi {
            l += 1;
        } else {
            let e = bend[l % 512] as usize;
            let nx = if e <= l { bend[(l + 1) % 512] as usize } else { e };
            l = if nx > hi { hi } else if nx <= l { l + 1 } else { nx };
        }
        steps += 1;
    }
    (best, bl)
}

/// Backward pass: `cost[j]` is the cheapest cost from `j` to the block end, `chl`/`chd` the choice.
pub fn backward(
    input: &[u8],
    c1l: &mut [u16; 32768],
    c1d: &mut [u16; 32768],
    c2l: &[u16; 32768],
    c2d: &[u16; 32768],
    cost: &mut [u32; 65536],
    litc: &[u32; 256],
    lenc: &[u32; 512],
    dcost: &[u32; 32],
    bend: &[u16; 512],
    dlo: &[u8; 256],
    dhi: &[u8; 256],
    p0: usize,
    blen: usize,
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
            if l1 < 3 && l2 < 3 {
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
                    let dcs = dcost[dcode(dlo, dhi, d2) % 32];
                    let from2 = if l2 > SPAN2 + 3 { l2 - SPAN2 } else { 3 };
                    let r = relax_run(cost, lenc, bend, j, from2, l2, dcs, best, bl);
                    if r.0 < best {
                        bdd = d2;
                    }
                    best = r.0;
                    bl = r.1;
                }
                let d1 = c1d[j % 32768] as usize;
                if l1 >= 3 && l1 <= rest && d1 >= 1 && d1 <= 32768 {
                    let dcs = dcost[dcode(dlo, dhi, d1) % 32];
                    let from = if l1 > SPAN1 + 3 { l1 - SPAN1 } else { 3 };
                    let r = relax_run(cost, lenc, bend, j, from, l1, dcs, best, bl);
                    if r.0 < best {
                        bdd = d1;
                    }
                    best = r.0;
                    bl = r.1;
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
pub fn count(
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
            let di = dcode(dlo, dhi, d) % 32;
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

/// Copies the counts `lf`/`df` into `olf`/`odf`.
pub fn keep(lf: &[u32; 512], df: &[u32; 32], olf: &mut [u32; 512], odf: &mut [u32; 32]) {
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

/// Literal, length and distance costs from the symbol counts.
pub fn learn(
    lf: &[u32; 512],
    df: &[u32; 32],
    litc: &mut [u32; 256],
    lenc: &mut [u32; 512],
    dcost: &mut [u32; 32],
    lcode: &[u8; 512],
    lextra: &[u8; 512],
    dext: &[u8; 32],
    bias: u32,
) {
    let mut tot = 1u32;
    let mut s = 0usize;
    while s < 286 {
        tot = tot.saturating_add(lf[s]);
        s += 1;
    }
    s = 0;
    while s < 256 {
        litc[s] = cost16(lf[s], tot).saturating_add(bias);
        s += 1;
    }
    let mut cc = [0u32; 32];
    let mut c = 0usize;
    while c < 29 {
        cc[c] = cost16(lf[(257 + c) % 512], tot).saturating_add(bias);
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
        dcost[c] = cost16(df[c], dt).saturating_add((dext[c] as u32) * 16);
        c += 1;
    }
}

/// True iff the match `(ch, d)` at `pos` is in range and its bytes agree.
pub fn verified(input: &[u8], pos: usize, d: usize, ch: usize, k: usize, blen: usize) -> bool {
    if ch < 3 || ch > 258 || d < 1 || d > 32768 || d > pos || k + ch > blen {
        return false;
    }
    let v = match_len(input, pos - d, pos, ch);
    v >= ch
}

/// Writes the chosen path of the block; a match is written only once `verified`.
pub fn emit(
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
    ntok
}

/// Length codes and their extra bits for lengths 3..=258.
pub fn len_tables(
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
pub fn code_from(dbase: &[u16; 32], d: usize, c0: usize) -> usize {
    let mut c = c0;
    while c < 29 && dbase[(c + 1) % 32] as usize <= d {
        c += 1;
    }
    c
}

/// Distance codes: `dlo` for distances 1..=256, `dhi` by `(d - 1) / 128` above.
pub fn dist_tables(dbase: &[u16; 32], dlo: &mut [u8; 256], dhi: &mut [u8; 256]) {
    let mut c = 0usize;
    let mut d = 1usize;
    while d <= 256 {
        c = code_from(dbase, d, c);
        dlo[(d - 1) % 256] = c as u8;
        d += 1;
    }
    let mut k = 0usize;
    c = 0;
    while k < 256 {
        c = code_from(dbase, k * 128 + 1, c);
        dhi[k] = c as u8;
        k += 1;
    }
}

/// Length and distance code tables.
pub fn tables(
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
    len_tables(&lbase, &lext, lcode, lextra, bend);
    dist_tables(&dbase, dlo, dhi);
    *dext = dx;
}

/// Starting costs: literals from a byte histogram of the first 32 KB, static match costs.
pub fn seed(
    input: &[u8],
    litc: &mut [u32; 256],
    lenc: &mut [u32; 512],
    dcost: &mut [u32; 32],
    lextra: &[u8; 512],
    dext: &[u8; 32],
) {
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
    while s < 256 {
        litc[s] = cost16(hist[s], tot);
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
}

/// Adds the per-token cost `bias` to every literal and every length.
pub fn add_bias(litc: &mut [u32; 256], lenc: &mut [u32; 512], bias: u32) {
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

/// 1 when the average literal cost over the first 32 KB is below `LONG_BELOW`, so only long
/// matches pay: no per-token bias and no skipping in literal runs.
pub fn avg_lit(input: &[u8], litc: &[u32; 256]) -> usize {
    let n = input.len();
    let lim = if n < 32768 { n } else { 32768 };
    let mut s = 0u64;
    let mut i = 0usize;
    while i < lim {
        s = s.wrapping_add(litc[input[i] as usize] as u64);
        i += 1;
    }
    if lim >= 8 && s < (LONG_BELOW as u64) * (lim as u64) {
        1
    } else {
        0
    }
}

/// Optimal parse per block under the learned costs; every written match is re-verified.
pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut lcode = [0u8; 512];
    let mut lextra = [0u8; 512];
    let mut bend = [0u16; 512];
    let mut dlo = [0u8; 256];
    let mut dhi = [0u8; 256];
    let mut dext = [0u8; 32];
    tables(&mut lcode, &mut lextra, &mut bend, &mut dlo, &mut dhi, &mut dext);
    let mut litc = [0u32; 256];
    let mut lenc = [0u32; 512];
    let mut dcost = [0u32; 32];
    seed(input, &mut litc, &mut lenc, &mut dcost, &lextra, &dext);
    let long = avg_lit(input, &litc);
    let bias = if long == 1 { 0 } else { BIAS };
    add_bias(&mut litc, &mut lenc, bias);
    let mut head4 = [0u32; 65536];
    let mut prev = [0u32; 32768];
    let mut near = [0u32; 65536];
    let mut c1l = [0u16; 32768];
    let mut c1d = [0u16; 32768];
    let mut c2l = [0u16; 32768];
    let mut c2d = [0u16; 32768];
    let mut cost = [0u32; 65536];
    let mut lf = [0u32; 512];
    let mut df = [0u32; 32];
    let mut olf = [0u32; 512];
    let mut odf = [0u32; 32];
    let mut ntok = 0usize;
    let mut p0 = 0usize;
    while p0 < n {
        let rest = n - p0;
        let blen = if rest > BLOCK { BLOCK } else { rest };
        prefix(input, &litc, &mut cost, p0, blen);
        lazy(
            input, &mut head4, &mut prev, &mut near, &cost, &lenc, &dcost, &dlo, &dhi, &mut c1l, &mut c1d,
            &mut c2l, &mut c2d, p0, blen, long,
        );
        count(input, &c1l, &c1d, &mut lf, &mut df, &lcode, &dlo, &dhi, &olf, &odf, 0, p0, blen);
        learn(&lf, &df, &mut litc, &mut lenc, &mut dcost, &lcode, &lextra, &dext, 0);
        backward(
            input, &mut c1l, &mut c1d, &c2l, &c2d, &mut cost, &litc, &lenc, &dcost, &bend, &dlo,
            &dhi, p0, blen,
        );
        if blen < rest {
            count(input, &c1l, &c1d, &mut lf, &mut df, &lcode, &dlo, &dhi, &olf, &odf, 1, p0, blen);
            learn(&lf, &df, &mut litc, &mut lenc, &mut dcost, &lcode, &lextra, &dext, bias);
            keep(&lf, &df, &mut olf, &mut odf);
        }
        ntok = emit(input, out, &c1l, &c1d, ntok, p0, blen);
        p0 += blen;
    }
    ntok
}
