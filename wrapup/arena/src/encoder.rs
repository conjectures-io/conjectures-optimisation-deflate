//! The pinned encoder (`validator/measure/src/deflate.rs`) made incremental.
//!
//! Same blocks (16384 tokens), same block-type choice, same package-merge code
//! lengths, so a whole token stream pushed in any batches and finished gives the
//! exact bytes of `pinned::encode`. Added: the bit writer survives between calls,
//! sync/full flushes (an empty stored block, as zlib's `Z_SYNC_FLUSH`), and
//! [`Huffman::Fast`], a package-merge that builds the same package lists but
//! counts leaves through child indices instead of cloning symbol vectors.

use crate::token;

const END_OF_BLOCK: usize = 256;
const NUM_LITLEN: usize = 288;
const NUM_DIST: usize = 30;
const NUM_CODELEN: usize = 19;
const MAX_BITS_LITLEN: u32 = 15;
const MAX_BITS_CODELEN: u32 = 7;

/// Tokens per block, as in the pinned encoder.
pub const BLOCK_TOKENS: usize = crate::pinned::BLOCK_TOKENS;

const CL_ORDER: [usize; NUM_CODELEN] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

const LEN_TABLE: [(u32, u32); 29] = [
    (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10),
    (1, 11), (1, 13), (1, 15), (1, 17), (2, 19), (2, 23), (2, 27), (2, 31),
    (3, 35), (3, 43), (3, 51), (3, 59), (4, 67), (4, 83), (4, 99), (4, 115),
    (5, 131), (5, 163), (5, 195), (5, 227), (0, 258),
];

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

/// Which package-merge builds the code lengths. Both give identical lengths.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Huffman {
    /// The pinned implementation, clones and all: the gate's timing.
    Pinned,
    /// The same algorithm without per-package allocations.
    Fast,
}

/// A flush that ends the current block and byte-aligns the output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flush {
    /// `Z_SYNC_FLUSH`: back-references may still reach before the flush point.
    Sync,
    /// `Z_FULL_FLUSH`: they may not, so a decoder can restart here.
    Full,
}

// ── Bit writer ────────────────────────────────────────────────────────────────

struct BitWriter {
    out: Vec<u8>,
    acc: u64,
    nbits: u32,
}

impl BitWriter {
    fn new() -> Self {
        BitWriter { out: Vec::new(), acc: 0, nbits: 0 }
    }

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
}

// ── Length-limited Huffman codes ──────────────────────────────────────────────

/// Verbatim from the pinned encoder.
fn package_merge_pinned(freqs: &[u32], max_bits: u32) -> Vec<u8> {
    let n = freqs.len();
    let mut lengths = vec![0u8; n];
    let live: Vec<usize> = (0..n).filter(|&i| freqs[i] > 0).collect();

    match live.len() {
        0 => return lengths,
        1 => {
            lengths[live[0]] = 1;
            return lengths;
        }
        _ => {}
    }

    let mut sorted = live.clone();
    sorted.sort_by_key(|&i| (freqs[i], i));

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
        let mut packaged: Vec<Pkg> = Vec::with_capacity(current.len() / 2 + leaves.len());
        let mut i = 0;
        while i + 1 < current.len() {
            let mut syms = current[i].syms.clone();
            syms.extend_from_slice(&current[i + 1].syms);
            packaged.push(Pkg { weight: current[i].weight + current[i + 1].weight, syms });
            i += 2;
        }
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

/// The pinned package-merge with the same lists in the same order; a package
/// names its two children in the level below instead of carrying their symbols,
/// and leaf counts are pushed down level by level.
fn package_merge_fast(freqs: &[u32], max_bits: u32) -> Vec<u8> {
    const LEAF: u32 = u32::MAX;

    #[derive(Clone, Copy)]
    struct Item {
        weight: u64,
        /// A leaf's sorted position, or a package's first child.
        a: u32,
        /// `LEAF`, or a package's second child.
        b: u32,
    }

    let n = freqs.len();
    let mut lengths = vec![0u8; n];
    let mut sorted: Vec<usize> = (0..n).filter(|&i| freqs[i] > 0).collect();
    match sorted.len() {
        0 => return lengths,
        1 => {
            lengths[sorted[0]] = 1;
            return lengths;
        }
        _ => {}
    }
    sorted.sort_by_key(|&i| (freqs[i], i));
    let m = sorted.len();

    let leaves: Vec<Item> = sorted
        .iter()
        .enumerate()
        .map(|(pos, &i)| Item { weight: freqs[i] as u64, a: pos as u32, b: LEAF })
        .collect();

    let mut levels: Vec<Vec<Item>> = Vec::with_capacity(max_bits as usize);
    levels.push(leaves.clone());
    for _ in 1..max_bits {
        let cur = levels.last().expect("levels starts non-empty");
        let mut merged = Vec::with_capacity(cur.len() / 2 + m);
        let (mut a, mut b) = (0usize, 0usize);
        let npk = cur.len() / 2;
        while a < m || b < npk {
            let take_leaf = b >= npk
                || (a < m && leaves[a].weight <= cur[2 * b].weight + cur[2 * b + 1].weight);
            if take_leaf {
                merged.push(leaves[a]);
                a += 1;
            } else {
                merged.push(Item {
                    weight: cur[2 * b].weight + cur[2 * b + 1].weight,
                    a: (2 * b) as u32,
                    b: (2 * b + 1) as u32,
                });
                b += 1;
            }
        }
        levels.push(merged);
    }

    let take = 2 * m - 2;
    let mut counts = vec![0u32; m];
    let top = levels.len() - 1;
    let mut mult = vec![0u32; levels[top].len()];
    for slot in mult.iter_mut().take(take) {
        *slot = 1;
    }
    for k in (0..levels.len()).rev() {
        let mut below = if k > 0 { vec![0u32; levels[k - 1].len()] } else { Vec::new() };
        for (i, it) in levels[k].iter().enumerate() {
            let c = mult[i];
            if c == 0 {
                continue;
            }
            if it.b == LEAF {
                counts[it.a as usize] += c;
            } else {
                below[it.a as usize] += c;
                below[it.b as usize] += c;
            }
        }
        mult = below;
    }
    for (pos, &sym) in sorted.iter().enumerate() {
        lengths[sym] = counts[pos] as u8;
    }
    lengths
}

fn package_merge(h: Huffman, freqs: &[u32], max_bits: u32) -> Vec<u8> {
    match h {
        Huffman::Pinned => package_merge_pinned(freqs, max_bits),
        Huffman::Fast => package_merge_fast(freqs, max_bits),
    }
}

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

// ── Blocks ────────────────────────────────────────────────────────────────────

struct Block {
    litlen_freq: [u32; NUM_LITLEN],
    dist_freq: [u32; NUM_DIST],
    items: Vec<(u16, u32, u32, u16, u32, u32)>,
    raw_len: usize,
}

impl Block {
    fn new() -> Self {
        Block {
            litlen_freq: [0; NUM_LITLEN],
            dist_freq: [0; NUM_DIST],
            items: Vec::with_capacity(BLOCK_TOKENS),
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

fn write_block(w: &mut BitWriter, b: &Block, last: bool, h: Huffman) {
    let mut lf = b.litlen_freq;
    lf[END_OF_BLOCK] += 1;
    let mut ll = package_merge(h, &lf, MAX_BITS_LITLEN);
    let mut dl = package_merge(h, &b.dist_freq, MAX_BITS_LITLEN);
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
    let cl = package_merge(h, &clf, MAX_BITS_CODELEN);

    let dyn_bits = b.dynamic_cost(&ll, &dl, &cl, &rle);
    let fix_bits = b.fixed_cost();
    let stored_bits = 3 + 32 + 8 * b.raw_len as u64;

    if stored_bits < dyn_bits.min(fix_bits) && b.raw_len < 65536 {
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

// ── The incremental encoder ───────────────────────────────────────────────────

/// Raw DEFLATE from tokens pushed in any batches.
pub struct Encoder {
    w: BitWriter,
    cur: Block,
    /// A full block whose `last` bit is unknown until the next token or `finish`.
    held: Option<Block>,
    /// Bytes the accepted tokens decode to.
    produced: u64,
    /// Bytes a back-reference may reach: reset by a full flush.
    window: u64,
    huffman: Huffman,
    finished: bool,
}

impl Encoder {
    pub fn new(huffman: Huffman) -> Self {
        Encoder {
            w: BitWriter::new(),
            cur: Block::new(),
            held: None,
            produced: 0,
            window: 0,
            huffman,
            finished: false,
        }
    }

    /// Bytes the tokens pushed so far decode to.
    pub fn produced(&self) -> u64 {
        self.produced
    }

    fn release_held(&mut self) {
        if let Some(b) = self.held.take() {
            write_block(&mut self.w, &b, false, self.huffman);
        }
    }

    /// Append tokens; `Err` on an illegal token or one reaching before the window.
    pub fn push(&mut self, toks: &[u32]) -> Result<(), String> {
        assert!(!self.finished, "push after finish");
        for &t in toks {
            match token::decode(t) {
                token::Token::Literal(b) => {
                    self.release_held();
                    self.cur.push_literal(b);
                    self.produced += 1;
                    self.window += 1;
                }
                token::Token::Match { dist, len } => {
                    if dist as u64 > self.window {
                        return Err(format!(
                            "token at output byte {}: distance {dist} reaches before the window ({} bytes)",
                            self.produced, self.window
                        ));
                    }
                    self.release_held();
                    self.cur.push_match(dist, len);
                    self.produced += len as u64;
                    self.window += len as u64;
                }
                token::Token::Invalid => return Err(format!("{t} is not a legal token")),
            }
            if self.cur.items.len() >= BLOCK_TOKENS {
                self.held = Some(std::mem::replace(&mut self.cur, Block::new()));
            }
        }
        Ok(())
    }

    /// End the current block and byte-align with an empty stored block.
    pub fn flush(&mut self, mode: Flush) {
        assert!(!self.finished, "flush after finish");
        self.release_held();
        if !self.cur.items.is_empty() {
            let b = std::mem::replace(&mut self.cur, Block::new());
            write_block(&mut self.w, &b, false, self.huffman);
        }
        self.w.put(0, 1);
        self.w.put(0, 2);
        self.w.align();
        self.w.put(0, 16);
        self.w.put(0xffff, 16);
        if mode == Flush::Full {
            self.window = 0;
        }
    }

    /// Write the final block and byte-align. Nothing may follow.
    pub fn finish(&mut self) {
        assert!(!self.finished, "finish twice");
        let b = match self.held.take() {
            Some(b) => b,
            None => std::mem::replace(&mut self.cur, Block::new()),
        };
        write_block(&mut self.w, &b, true, self.huffman);
        self.w.align();
        self.finished = true;
    }

    /// Completed output bytes since the last call.
    pub fn take(&mut self) -> Vec<u8> {
        std::mem::take(&mut self.w.out)
    }
}

/// One-shot encode, the counterpart of `pinned::encode`.
pub fn encode(tokens: &[u32], input_len: usize, huffman: Huffman) -> Result<Vec<u8>, String> {
    let mut e = Encoder::new(huffman);
    e.push(tokens)?;
    if e.produced() != input_len as u64 {
        return Err(format!(
            "the token stream produces {} bytes, but the input is {input_len}",
            e.produced()
        ));
    }
    e.finish();
    Ok(e.take())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lcg(seed: &mut u64) -> u32 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (*seed >> 33) as u32
    }

    #[test]
    fn fast_package_merge_matches_pinned() {
        let mut s = 7u64;
        for case in 0..3000 {
            let n = [2usize, 3, 19, 30, 288][case % 5];
            let max_bits = if n == 19 { 7 } else { 15 };
            let mut f = vec![0u32; n];
            for x in f.iter_mut() {
                let r = lcg(&mut s);
                *x = match r % 4 {
                    0 => 0,
                    1 => r % 3,
                    2 => r % 1000,
                    _ => (r % 7) * 100_000 + 1,
                };
            }
            if case % 11 == 0 {
                // Fibonacci-ish weights force the length limit to bind.
                let (mut a, mut b) = (1u32, 1u32);
                for x in f.iter_mut() {
                    *x = a;
                    let c = a.saturating_add(b);
                    a = b;
                    b = c;
                }
            }
            assert_eq!(
                package_merge_pinned(&f, max_bits),
                package_merge_fast(&f, max_bits),
                "case {case}: {f:?}"
            );
        }
    }
}
