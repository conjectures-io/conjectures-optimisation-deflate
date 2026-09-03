//! Unconstrained reference parsers, for measuring **where the headroom is**.
//!
//! Nothing here is a submission, nothing here is scored, and nothing here obeys
//! [`RULES.md`](../../../miner/RULES.md): these parsers use iterators, slices,
//! allocation and whatever else is convenient, because their only job is to
//! answer a measurement question the competition's own numbers cannot answer on
//! their own.
//!
//! ## The question
//!
//! `libdeflate` level 12 is some way under the best accepted submission, and the
//! obvious reading of that gap is "this is what is left to win". That reading is
//! wrong, because the gap has three components and a miner can only reach one of
//! them:
//!
//! | component | reachable by a miner? |
//! |---|---|
//! | a better **parse** | **yes** — that is the slot |
//! | better **block splitting** | no — `deflate.rs` uses fixed 16384-token blocks |
//! | a better **entropy coder** | no — `deflate.rs` is trusted and pinned |
//!
//! So the decomposition is done by construction. Every parser here emits the
//! competition's own token encoding and is scored through the *same* trusted
//! `deflate::encode`. Whatever bytes they reach is therefore, by definition,
//! reachable through the slot — it is a parse, and nothing else changed. The
//! part of the gap they do *not* close is the part that lives in the harness.
//!
//! ## The ladder
//!
//! * [`greedy`] — hash chains, arbitrary depth. What a submission already does,
//!   with the proof-friendliness constraints removed.
//! * [`lazy`] — greedy plus lazy matching: defer a match by one byte when the
//!   next position has a longer one. zlib's own trick, and the cheapest real
//!   improvement over greedy.
//! * [`optimal`] — a shortest-path parse over the whole file under an iterated
//!   bit-cost model. This is the zopfli/libdeflate class of parser and it is the
//!   practical ceiling for *parsing alone*.

use crate::deflate;
use crate::token;

const MIN_MATCH: usize = 3;
const MAX_MATCH: usize = 258;
const WINDOW: usize = 32768;
const HASH_BITS: u32 = 15;
const HASH_SIZE: usize = 1 << HASH_BITS;

/// Unused symbols get a code length of 0 from package-merge, which would read as
/// "free" to a shortest-path search. Charge them more than the longest real code
/// instead, so the parse is never rewarded for reaching a symbol that does not
/// exist yet.
const UNUSED_SYMBOL_BITS: u32 = 16;

// ---------------------------------------------------------------------------
// Match finding
// ---------------------------------------------------------------------------

/// `head`/`prev` hash chains over the whole input, built in one pass so that a
/// query at `pos` sees every earlier position and no later one.
struct Chains {
    prev: Vec<i32>,
}

fn hash3(b: &[u8], pos: usize) -> usize {
    let v = ((b[pos] as u32) << 16) | ((b[pos + 1] as u32) << 8) | (b[pos + 2] as u32);
    (v.wrapping_mul(2654435761) >> (32 - HASH_BITS)) as usize
}

fn build_chains(b: &[u8]) -> Chains {
    let n = b.len();
    let mut head = vec![-1i32; HASH_SIZE];
    let mut prev = vec![-1i32; n];
    if n >= MIN_MATCH {
        for pos in 0..=(n - MIN_MATCH) {
            let h = hash3(b, pos);
            prev[pos] = head[h];
            head[h] = pos as i32;
        }
    }
    Chains { prev }
}

fn match_len(b: &[u8], a: usize, c: usize, cap: usize) -> usize {
    let mut n = 0;
    while n < cap && b[a + n] == b[c + n] {
        n += 1;
    }
    n
}

/// The longest match at `pos`, as `(len, dist)`, or `(0, 0)` if there is none.
/// `nice` stops the walk early once a match that long is found.
fn best_match(b: &[u8], ch: &Chains, pos: usize, depth: usize, nice: usize) -> (usize, usize) {
    let n = b.len();
    if pos + MIN_MATCH > n {
        return (0, 0);
    }
    let cap = (n - pos).min(MAX_MATCH);
    let floor = pos.saturating_sub(WINDOW);
    let (mut best_len, mut best_dist) = (0usize, 0usize);
    let mut cur = ch.prev[pos];
    let mut probes = 0usize;
    while cur >= 0 && probes < depth {
        let c = cur as usize;
        if c < floor {
            break;
        }
        // Cheap reject: the candidate can only win if it matches the byte that
        // would extend the current best. `best_len < cap` is what makes that
        // byte exist -- at `best_len == cap` there is nothing left to extend
        // into and the walk is already done.
        if best_len == 0 || (best_len < cap && b[c + best_len] == b[pos + best_len]) {
            let l = match_len(b, pos, c, cap);
            if l > best_len {
                best_len = l;
                best_dist = pos - c;
                if l >= nice || l >= cap {
                    break;
                }
            }
        }
        cur = ch.prev[c];
        probes += 1;
    }
    if best_len < MIN_MATCH {
        (0, 0)
    } else {
        (best_len, best_dist)
    }
}

/// For every length `l`, the **smallest** distance that achieves a match of at
/// least `l` at `pos`. Written into `dist_for_len[MIN_MATCH..=cap]`; `0` means no
/// match of that length exists.
///
/// A candidate at distance `d` with maximal length `L` also achieves every
/// length below `L` at the same distance, so recording it only at `L` and then
/// sweeping downwards is enough — which is what keeps this `O(depth + MAX_MATCH)`
/// per position rather than `O(depth * MAX_MATCH)`.
fn dists_by_length(b: &[u8], ch: &Chains, pos: usize, depth: usize, dist_for_len: &mut [u32]) -> usize {
    let n = b.len();
    dist_for_len[..=MAX_MATCH].fill(0);
    if pos + MIN_MATCH > n {
        return 0;
    }
    let cap = (n - pos).min(MAX_MATCH);
    let floor = pos.saturating_sub(WINDOW);
    let mut longest = 0usize;
    let mut cur = ch.prev[pos];
    let mut probes = 0usize;
    while cur >= 0 && probes < depth {
        let c = cur as usize;
        if c < floor {
            break;
        }
        let l = match_len(b, pos, c, cap);
        if l >= MIN_MATCH {
            let d = (pos - c) as u32;
            if dist_for_len[l] == 0 || d < dist_for_len[l] {
                dist_for_len[l] = d;
            }
            if l > longest {
                longest = l;
            }
        }
        cur = ch.prev[c];
        probes += 1;
    }
    // Sweep: the best distance for `l` is the best for `l`, or the best for
    // anything longer.
    let mut l = longest;
    while l > MIN_MATCH {
        let carry = dist_for_len[l];
        if carry != 0 && (dist_for_len[l - 1] == 0 || carry < dist_for_len[l - 1]) {
            dist_for_len[l - 1] = carry;
        }
        l -= 1;
    }
    longest
}

// ---------------------------------------------------------------------------
// Greedy and lazy
// ---------------------------------------------------------------------------

/// Greedy: at each position take the longest match, else a literal.
pub fn greedy(b: &[u8], depth: usize) -> Vec<u32> {
    let ch = build_chains(b);
    let mut out = Vec::with_capacity(b.len() / 2 + 1);
    let mut pos = 0usize;
    while pos < b.len() {
        let (l, d) = best_match(b, &ch, pos, depth, MAX_MATCH);
        if l >= MIN_MATCH {
            out.push(token::encode_match(d as u32, l as u32));
            pos += l;
        } else {
            out.push(b[pos] as u32);
            pos += 1;
        }
    }
    out
}

/// Lazy matching: emit a literal instead of a match when the *next* position has
/// a strictly longer one. zlib's condition, and the cheapest real win over
/// greedy.
pub fn lazy(b: &[u8], depth: usize) -> Vec<u32> {
    let ch = build_chains(b);
    let mut out = Vec::with_capacity(b.len() / 2 + 1);
    let mut pos = 0usize;
    while pos < b.len() {
        let (l, d) = best_match(b, &ch, pos, depth, MAX_MATCH);
        if l >= MIN_MATCH {
            if l < MAX_MATCH && pos + 1 < b.len() {
                let (l2, _) = best_match(b, &ch, pos + 1, depth, MAX_MATCH);
                if l2 > l {
                    out.push(b[pos] as u32);
                    pos += 1;
                    continue;
                }
            }
            out.push(token::encode_match(d as u32, l as u32));
            pos += l;
        } else {
            out.push(b[pos] as u32);
            pos += 1;
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Optimal parse
// ---------------------------------------------------------------------------

/// Bit costs for one pass of the shortest-path parse: what the *trusted encoder*
/// would charge for each symbol, given the frequencies of the previous pass.
struct Costs {
    litlen: Vec<u32>,
    dist: Vec<u32>,
}

impl Costs {
    fn from_freqs(litlen_freq: &[u32], dist_freq: &[u32]) -> Costs {
        let (ll, dl) = deflate::code_lengths(litlen_freq, dist_freq);
        let bits = |lengths: &[u8]| -> Vec<u32> {
            lengths
                .iter()
                .map(|&n| if n == 0 { UNUSED_SYMBOL_BITS } else { n as u32 })
                .collect()
        };
        Costs { litlen: bits(&ll), dist: bits(&dl) }
    }

    fn literal(&self, b: u8) -> u32 {
        self.litlen[b as usize]
    }

    fn matched(&self, len: u32, dist: u32) -> u32 {
        let (ls, lextra) = deflate::len_symbol(len);
        let (ds, dextra) = deflate::dist_symbol(dist);
        self.litlen[ls] + lextra + self.dist[ds] + dextra
    }
}

fn freqs_of(tokens: &[u32]) -> (Vec<u32>, Vec<u32>) {
    let mut litlen = vec![0u32; deflate::LITLEN_SYMBOLS];
    let mut dist = vec![0u32; deflate::DIST_SYMBOLS];
    for &t in tokens {
        match token::decode(t) {
            token::Token::Literal(b) => litlen[b as usize] += 1,
            token::Token::Match { dist: d, len } => {
                litlen[deflate::len_symbol(len).0] += 1;
                dist[deflate::dist_symbol(d).0] += 1;
            }
            token::Token::Invalid => {}
        }
    }
    (litlen, dist)
}

/// One shortest-path pass: the cheapest parse of the whole input under `costs`.
///
/// Backward dynamic program — `cost[i]` is the cheapest encoding of `b[i..]` —
/// because that makes the reconstruction a forward walk over the choices.
fn shortest_path(b: &[u8], ch: &Chains, depth: usize, costs: &Costs) -> Vec<u32> {
    let n = b.len();
    let mut cost = vec![u64::MAX; n + 1];
    let mut take_len = vec![0u16; n + 1];
    let mut take_dist = vec![0u32; n + 1];
    cost[n] = 0;

    let mut dist_for_len = vec![0u32; MAX_MATCH + 1];
    let mut pos = n;
    while pos > 0 {
        pos -= 1;
        let mut best = cost[pos + 1].saturating_add(costs.literal(b[pos]) as u64);
        let mut best_len = 0u16;
        let mut best_dist = 0u32;

        let longest = dists_by_length(b, ch, pos, depth, &mut dist_for_len);
        let mut l = MIN_MATCH;
        while l <= longest {
            let d = dist_for_len[l];
            if d != 0 {
                let rest = cost[pos + l];
                if rest != u64::MAX {
                    let c = rest + costs.matched(l as u32, d) as u64;
                    if c < best {
                        best = c;
                        best_len = l as u16;
                        best_dist = d;
                    }
                }
            }
            l += 1;
        }
        cost[pos] = best;
        take_len[pos] = best_len;
        take_dist[pos] = best_dist;
    }

    let mut out = Vec::with_capacity(n / 2 + 1);
    let mut pos = 0usize;
    while pos < n {
        let l = take_len[pos] as usize;
        if l >= MIN_MATCH {
            out.push(token::encode_match(take_dist[pos], l as u32));
            pos += l;
        } else {
            out.push(b[pos] as u32);
            pos += 1;
        }
    }
    out
}

/// A near-optimal parse: `iters` shortest-path passes, each one costed by the
/// symbol frequencies the previous pass produced.
///
/// The cost model is a chicken-and-egg problem — the cheapest parse depends on
/// the Huffman code, which depends on the parse — and iterating is the standard
/// answer (zopfli does the same). The first pass is costed from a lazy parse,
/// which is a much better start than a flat model.
///
/// Every candidate stream is measured through the real `deflate::encode`, and the
/// smallest *actual* output wins, so a pass that the cost model liked but the
/// encoder did not can never make the result worse.
pub fn optimal(b: &[u8], depth: usize, iters: usize) -> Vec<u32> {
    let ch = build_chains(b);
    let mut best = lazy(b, depth);
    let mut best_bytes = match deflate::encode(&best, b.len()) {
        Ok(v) => v.len(),
        Err(_) => usize::MAX,
    };
    let (mut lf, mut df) = freqs_of(&best);

    for _ in 0..iters {
        let costs = Costs::from_freqs(&lf, &df);
        let cand = shortest_path(b, &ch, depth, &costs);
        let bytes = match deflate::encode(&cand, b.len()) {
            Ok(v) => v.len(),
            Err(_) => continue,
        };
        let (nlf, ndf) = freqs_of(&cand);
        lf = nlf;
        df = ndf;
        if bytes < best_bytes {
            best_bytes = bytes;
            best = cand;
        }
    }
    best
}
