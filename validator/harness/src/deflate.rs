//! Tokens to DEFLATE bytes.
//!
//! This file is **trusted and fixed**. It is not part of any slot, it is
//! identical for the baseline and for every submission, and a miner cannot
//! change it. That is what makes the score a fair comparison: two token streams
//! for the same input go through exactly the same entropy coder, so the only
//! thing the number measures is the quality of the parse.
//!
//! It is also why the *proof* obligation stops at the token stream. Huffman
//! coding is a bijection that this file implements once; the miner never touches
//! it and therefore never has to prove anything about it. Extending the
//! competition to the entropy layer would mean a second slot with its own
//! contract, and is deliberately out of scope for the MVP.
//!
//! RFC 1951 §3.2. Bits are packed least-significant-first; Huffman codes are
//! stored bit-reversed so that the same primitive emits them most-significant
//! first, which is the convention every DEFLATE encoder uses.

use crate::token;

const END_OF_BLOCK: usize = 256;
const NUM_LITLEN: usize = 288;
const NUM_DIST: usize = 30;
const NUM_CODELEN: usize = 19;
const MAX_BITS_LITLEN: u32 = 15;
const MAX_BITS_CODELEN: u32 = 7;

/// The order HCLEN lengths are written in. RFC 1951 §3.2.7.
const CL_ORDER: [usize; NUM_CODELEN] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

/// `(extra bits, base length)` for length codes 257..=285. RFC 1951 §3.2.5.
const LEN_TABLE: [(u32, u32); 29] = [
    (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10),
    (1, 11), (1, 13), (1, 15), (1, 17), (2, 19), (2, 23), (2, 27), (2, 31),
    (3, 35), (3, 43), (3, 51), (3, 59), (4, 67), (4, 83), (4, 99), (4, 115),
    (5, 131), (5, 163), (5, 195), (5, 227), (0, 258),
];

/// `(extra bits, base distance)` for distance codes 0..=29.
const DIST_TABLE: [(u32, u32); NUM_DIST] = [
    (0, 1), (0, 2), (0, 3), (0, 4), (1, 5), (1, 7), (2, 9), (2, 13),
    (3, 17), (3, 25), (4, 33), (4, 49), (5, 65), (5, 97), (6, 129), (6, 193),
    (7, 257), (7, 385), (8, 513), (8, 769), (9, 1025), (9, 1537), (10, 2049),
    (10, 3073), (11, 4097), (11, 6145), (12, 8193), (12, 12289), (13, 16385),
    (13, 24577),
];

fn len_code(len: u32) -> (usize, u32, u32) {
    let mut i = LEN_TABLE.len() - 1;
    while LEN_TABLE[i].1 > len {
        i -= 1;
    }
    (257 + i, LEN_TABLE[i].0, len - LEN_TABLE[i].1)
}

fn dist_code(dist: u32) -> (usize, u32, u32) {
    let mut i = DIST_TABLE.len() - 1;
    while DIST_TABLE[i].1 > dist {
        i -= 1;
    }
    (i, DIST_TABLE[i].0, dist - DIST_TABLE[i].1)
}

// ---------------------------------------------------------------------------
// Bit writer
// ---------------------------------------------------------------------------

pub struct BitWriter {
    out: Vec<u8>,
    acc: u64,
    nbits: u32,
}

impl BitWriter {
    fn new() -> Self {
        BitWriter { out: Vec::new(), acc: 0, nbits: 0 }
    }

    /// `n` bits of `v`, least-significant first.
    fn put(&mut self, v: u32, n: u32) {
        debug_assert!(n <= 32 && (n == 32 || v < (1u32 << n)));
        self.acc |= (v as u64) << self.nbits;
        self.nbits += n;
        while self.nbits >= 8 {
            self.out.push(self.acc as u8);
            self.acc >>= 8;
            self.nbits -= 8;
        }
    }

    fn align(&mut self) {
        if self.nbits > 0 {
            self.out.push(self.acc as u8);
            self.acc = 0;
            self.nbits = 0;
        }
    }

    fn finish(mut self) -> Vec<u8> {
        self.align();
        self.out
    }
}

// ---------------------------------------------------------------------------
// Length-limited Huffman codes
// ---------------------------------------------------------------------------

/// Package-merge: optimal code lengths subject to `max_bits`.
///
/// Chosen over zlib's build-then-repair because it is short enough to read and
/// cannot silently produce an over-long code on an adversarial frequency
/// distribution — which a miner controls, since they choose the parse.
fn package_merge(freqs: &[u32], max_bits: u32) -> Vec<u8> {
    let n = freqs.len();
    let mut lengths = vec![0u8; n];
    let live: Vec<usize> = (0..n).filter(|&i| freqs[i] > 0).collect();

    match live.len() {
        0 => return lengths,
        // A one-symbol alphabet still needs a one-bit code: a zero-length code
        // is not representable, and decoders reject an incomplete table.
        1 => {
            lengths[live[0]] = 1;
            return lengths;
        }
        _ => {}
    }

    let mut sorted = live.clone();
    sorted.sort_by_key(|&i| (freqs[i], i));

    // A "package" is a multiset of symbols; we track only its weight and which
    // symbols it contains, as a bitmask over `sorted` positions would be too
    // large, so we keep index lists. `sorted.len() <= 288`, so this is cheap.
    #[derive(Clone)]
    struct Pkg {
        weight: u64,
        syms: Vec<u32>,
    }

    let leaves: Vec<Pkg> = sorted
        .iter()
        .enumerate()
        .map(|(pos, &i)| Pkg { weight: freqs[i] as u64, syms: vec![pos as u32] })
        .collect();

    let mut current = leaves.clone();
    for _ in 1..max_bits {
        // Package pairs, then merge with the original leaves.
        let mut packaged: Vec<Pkg> = Vec::with_capacity(current.len() / 2 + leaves.len());
        let mut i = 0;
        while i + 1 < current.len() {
            let mut syms = current[i].syms.clone();
            syms.extend_from_slice(&current[i + 1].syms);
            packaged.push(Pkg { weight: current[i].weight + current[i + 1].weight, syms });
            i += 2;
        }
        // Merge two sorted lists.
        let mut merged = Vec::with_capacity(packaged.len() + leaves.len());
        let (mut a, mut b) = (0, 0);
        while a < leaves.len() || b < packaged.len() {
            let take_leaf = b >= packaged.len()
                || (a < leaves.len() && leaves[a].weight <= packaged[b].weight);
            if take_leaf {
                merged.push(leaves[a].clone());
                a += 1;
            } else {
                merged.push(packaged[b].clone());
                b += 1;
            }
        }
        current = merged;
    }

    // The first `2*live - 2` packages are the solution; a symbol's code length
    // is how many of them contain it.
    let take = 2 * live.len() - 2;
    let mut counts = vec![0u32; live.len()];
    for pkg in current.iter().take(take) {
        for &s in &pkg.syms {
            counts[s as usize] += 1;
        }
    }
    for (pos, &sym) in sorted.iter().enumerate() {
        lengths[sym] = counts[pos] as u8;
    }
    lengths
}

/// Canonical codes from code lengths, bit-reversed for `BitWriter::put`.
/// RFC 1951 §3.2.2.
fn canonical(lengths: &[u8], max_bits: u32) -> Vec<u32> {
    let mut bl_count = vec![0u32; max_bits as usize + 1];
    for &l in lengths {
        if l > 0 {
            bl_count[l as usize] += 1;
        }
    }
    let mut next = vec![0u32; max_bits as usize + 2];
    let mut code = 0u32;
    for bits in 1..=max_bits as usize {
        code = (code + bl_count[bits - 1]) << 1;
        next[bits] = code;
    }
    let mut codes = vec![0u32; lengths.len()];
    for (i, &l) in lengths.iter().enumerate() {
        if l > 0 {
            let c = next[l as usize];
            next[l as usize] += 1;
            codes[i] = reverse_bits(c, l as u32);
        }
    }
    codes
}

fn reverse_bits(mut v: u32, n: u32) -> u32 {
    let mut r = 0u32;
    for _ in 0..n {
        r = (r << 1) | (v & 1);
        v >>= 1;
    }
    r
}

// ---------------------------------------------------------------------------
// Code-length alphabet (the HCLEN section of a dynamic header)
// ---------------------------------------------------------------------------

/// Run-length encode the concatenated lit/len and distance code lengths into the
/// 19-symbol code-length alphabet. RFC 1951 §3.2.7.
fn rle_lengths(all: &[u8]) -> Vec<(u8, u32, u32)> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < all.len() {
        let v = all[i];
        let mut run = 1;
        while i + run < all.len() && all[i + run] == v {
            run += 1;
        }
        if v == 0 {
            while run >= 3 {
                if run >= 11 {
                    let take = run.min(138);
                    out.push((18u8, (take - 11) as u32, 7));
                    run -= take;
                    i += take;
                } else {
                    let take = run.min(10);
                    out.push((17u8, (take - 3) as u32, 3));
                    run -= take;
                    i += take;
                }
            }
            for _ in 0..run {
                out.push((0u8, 0, 0));
                i += 1;
            }
        } else {
            out.push((v, 0, 0));
            i += 1;
            run -= 1;
            while run >= 3 {
                let take = run.min(6);
                out.push((16u8, (take - 3) as u32, 2));
                run -= take;
                i += take;
            }
            for _ in 0..run {
                out.push((v, 0, 0));
                i += 1;
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Blocks
// ---------------------------------------------------------------------------

struct Block {
    litlen_freq: [u32; NUM_LITLEN],
    dist_freq: [u32; NUM_DIST],
    /// `(litlen symbol, extra, extra bits, dist symbol or usize::MAX, dextra, dextra bits)`
    items: Vec<(u16, u32, u32, u16, u32, u32)>,
    raw_len: usize,
}

impl Block {
    fn new() -> Self {
        Block {
            litlen_freq: [0; NUM_LITLEN],
            dist_freq: [0; NUM_DIST],
            items: Vec::new(),
            raw_len: 0,
        }
    }

    fn push_literal(&mut self, b: u8) {
        self.litlen_freq[b as usize] += 1;
        self.items.push((b as u16, 0, 0, u16::MAX, 0, 0));
        self.raw_len += 1;
    }

    fn push_match(&mut self, dist: u32, len: u32) {
        let (lc, lextra, lval) = len_code(len);
        let (dc, dextra, dval) = dist_code(dist);
        self.litlen_freq[lc] += 1;
        self.dist_freq[dc] += 1;
        self.items.push((lc as u16, lval, lextra, dc as u16, dval, dextra));
        self.raw_len += len as usize;
    }

    /// Bits a dynamic block would cost, header included. Used to choose between
    /// dynamic, fixed and stored.
    fn dynamic_cost(&self, ll: &[u8], dl: &[u8], cl: &[u8], rle: &[(u8, u32, u32)]) -> u64 {
        let mut bits: u64 = 3 + 5 + 5 + 4 + 3 * hclen(cl) as u64;
        for &(sym, _, extra) in rle {
            bits += cl[sym as usize] as u64 + extra as u64;
        }
        for &(s, _, le, d, _, de) in &self.items {
            bits += ll[s as usize] as u64 + le as u64;
            if d != u16::MAX {
                bits += dl[d as usize] as u64 + de as u64;
            }
        }
        bits + ll[END_OF_BLOCK] as u64
    }

    fn fixed_cost(&self) -> u64 {
        let (ll, dl) = fixed_tables();
        let mut bits: u64 = 3;
        for &(s, _, le, d, _, de) in &self.items {
            bits += ll[s as usize] as u64 + le as u64;
            if d != u16::MAX {
                bits += dl[d as usize] as u64 + de as u64;
            }
        }
        bits + ll[END_OF_BLOCK] as u64
    }
}

fn hclen(cl: &[u8]) -> usize {
    let mut n = NUM_CODELEN;
    while n > 4 && cl[CL_ORDER[n - 1]] == 0 {
        n -= 1;
    }
    n
}

fn fixed_tables() -> ([u8; NUM_LITLEN], [u8; NUM_DIST]) {
    let mut ll = [0u8; NUM_LITLEN];
    for (i, slot) in ll.iter_mut().enumerate() {
        *slot = match i {
            0..=143 => 8,
            144..=255 => 9,
            256..=279 => 7,
            _ => 8,
        };
    }
    (ll, [5u8; NUM_DIST])
}

// ---------------------------------------------------------------------------
// The encoder
// ---------------------------------------------------------------------------

/// How many tokens go into one block. Fixed, and the same for everyone, so that
/// block splitting is not part of what is being competed on.
pub const BLOCK_TOKENS: usize = 16384;

/// Encode a token stream as a raw DEFLATE stream.
///
/// Returns `Err` if the stream is malformed — a distance reaching before the
/// start of the output, a length out of range, a token outside the encoding.
/// The competition's proof is exactly the statement that this never happens, but
/// the check is here regardless: the harness must not depend on the proof being
/// sound in order to stay memory-safe and terminating.
pub fn encode(tokens: &[u32], input_len: usize) -> Result<Vec<u8>, String> {
    let mut blocks: Vec<Block> = Vec::new();
    let mut cur = Block::new();
    let mut produced = 0usize;

    for (i, &t) in tokens.iter().enumerate() {
        match token::decode(t) {
            token::Token::Literal(b) => {
                cur.push_literal(b);
                produced += 1;
            }
            token::Token::Match { dist, len } => {
                if dist as usize > produced {
                    return Err(format!(
                        "token {i}: distance {dist} reaches before the start of the output ({produced} bytes so far)"
                    ));
                }
                cur.push_match(dist, len);
                produced += len as usize;
            }
            token::Token::Invalid => return Err(format!("token {i}: {t} is not a legal token")),
        }
        if cur.items.len() >= BLOCK_TOKENS && i + 1 < tokens.len() {
            blocks.push(std::mem::replace(&mut cur, Block::new()));
        }
    }
    blocks.push(cur);

    if produced != input_len {
        return Err(format!(
            "the token stream produces {produced} bytes, but the input is {input_len}"
        ));
    }

    let mut w = BitWriter::new();
    let nblocks = blocks.len();
    for (bi, b) in blocks.iter().enumerate() {
        let last = bi + 1 == nblocks;
        write_block(&mut w, b, last);
    }
    Ok(w.finish())
}

fn write_block(w: &mut BitWriter, b: &Block, last: bool) {
    // Dynamic tables.
    let mut lf = b.litlen_freq;
    lf[END_OF_BLOCK] += 1;
    let mut ll = package_merge(&lf, MAX_BITS_LITLEN);
    let mut dl = package_merge(&b.dist_freq, MAX_BITS_LITLEN);
    // A block with no matches still has to name at least one distance code.
    if dl.iter().all(|&x| x == 0) {
        dl[0] = 1;
    }

    let hlit = {
        let mut n = NUM_LITLEN;
        while n > 257 && ll[n - 1] == 0 {
            n -= 1;
        }
        n
    };
    let hdist = {
        let mut n = NUM_DIST;
        while n > 1 && dl[n - 1] == 0 {
            n -= 1;
        }
        n
    };
    ll.truncate(hlit.max(257));
    ll.resize(NUM_LITLEN, 0);
    let mut all: Vec<u8> = Vec::with_capacity(hlit + hdist);
    all.extend_from_slice(&ll[..hlit]);
    all.extend_from_slice(&dl[..hdist]);
    let rle = rle_lengths(&all);
    let mut clf = [0u32; NUM_CODELEN];
    for &(sym, _, _) in &rle {
        clf[sym as usize] += 1;
    }
    let cl = package_merge(&clf, MAX_BITS_CODELEN);

    let dyn_bits = b.dynamic_cost(&ll, &dl, &cl, &rle);
    let fix_bits = b.fixed_cost();
    let stored_bits = 3 + 32 + 8 * b.raw_len as u64;

    if stored_bits < dyn_bits.min(fix_bits) && b.raw_len < 65536 {
        // Cheaper to store the bytes. Only reachable for incompressible input,
        // and only when the block happens to be all literals.
        if b.items.iter().all(|&(_, _, _, d, _, _)| d == u16::MAX) {
            w.put(last as u32, 1);
            w.put(0, 2);
            w.align();
            let n = b.raw_len as u32;
            w.put(n & 0xffff, 16);
            w.put(!n & 0xffff, 16);
            for &(s, _, _, _, _, _) in &b.items {
                w.put(s as u32, 8);
            }
            return;
        }
    }

    if fix_bits <= dyn_bits {
        let (fll, fdl) = fixed_tables();
        let llc = canonical(&fll, MAX_BITS_LITLEN);
        let dlc = canonical(&fdl, MAX_BITS_LITLEN);
        w.put(last as u32, 1);
        w.put(1, 2);
        emit_items(w, b, &fll, &llc, &fdl, &dlc);
        return;
    }

    let llc = canonical(&ll, MAX_BITS_LITLEN);
    let dlc = canonical(&dl, MAX_BITS_LITLEN);
    let clc = canonical(&cl, MAX_BITS_CODELEN);

    w.put(last as u32, 1);
    w.put(2, 2);
    w.put((hlit - 257) as u32, 5);
    w.put((hdist - 1) as u32, 5);
    let hc = hclen(&cl);
    w.put((hc - 4) as u32, 4);
    for &idx in CL_ORDER.iter().take(hc) {
        w.put(cl[idx] as u32, 3);
    }
    for &(sym, extra, nextra) in &rle {
        w.put(clc[sym as usize], cl[sym as usize] as u32);
        if nextra > 0 {
            w.put(extra, nextra);
        }
    }
    emit_items(w, b, &ll, &llc, &dl, &dlc);
}

fn emit_items(w: &mut BitWriter, b: &Block, ll: &[u8], llc: &[u32], dl: &[u8], dlc: &[u32]) {
    for &(s, lextra, lbits, d, dextra, dbits) in &b.items {
        w.put(llc[s as usize], ll[s as usize] as u32);
        if lbits > 0 {
            w.put(lextra, lbits);
        }
        if d != u16::MAX {
            w.put(dlc[d as usize], dl[d as usize] as u32);
            if dbits > 0 {
                w.put(dextra, dbits);
            }
        }
    }
    w.put(llc[END_OF_BLOCK], ll[END_OF_BLOCK] as u32);
}
