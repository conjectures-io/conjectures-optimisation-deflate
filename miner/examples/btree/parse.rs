//! # The slot: LZ77 parsing -- binary-tree match finder. Research spike, no
//! proof yet (see `Parse.lean` state below); `just extract` succeeds, `just
//! score`/`just prove` do not have a submission.toml/Parse.lean to work from.
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
//! ## What this is
//!
//! Per hash bucket, positions form a binary search tree ordered by suffix; a
//! bounded number of comparisons (`MAX_PROBES`) descend it, tracking the
//! common prefix length already proven on each side (`len0`/`len1`) so each
//! step only needs to *extend*, not recompare, the matched prefix. This is
//! the technique LZMA and libdeflate's own deep levels use to make many
//! comparisons per position affordable -- hash chains are a degenerate case
//! of the same idea with an unordered list instead of a tree.
//!
//! Measured against `hash-chains`/`lazy`/`optimal` on this repo's own corpora,
//! at `MAX_PROBES = 32` this did **not** pay for itself: worse ratio than
//! `lazy` for several times the cost, on every file tried so far. Likely
//! cause: unlike a hash chain, inserting a position into this tree costs a
//! full descent (not O(1)), and `parse` reinserts every position a match
//! skips over, so the time budget goes mostly to bookkeeping rather than
//! deeper search. Kept as a candidate anyway -- a different probe budget, or
//! skipping reinsertion inside long matches, might change that -- and because
//! a negative result is still useful context for what's on the frontier and
//! what only looks like it should be.
//!
//! ## Prover-friendly Rust -- the rules
//!
//! Same four rules as every other slot in this repo (guarded subtraction,
//! `%`-bounded indices, no labelled control flow, a decreasing loop counter
//! independent of the data). Not yet proved: the tree-descent loop below
//! redirects two different pending write targets (`idx0`/`which0` and
//! `idx1`/`which1`) as it walks, which is a new shape relative to the plain
//! hash-chain walk `hash-chains`/`lazy`/`optimal` all share, and needs its
//! own termination/invariant argument rather than a copy of theirs.

pub const MIN_MATCH: usize = 3;
pub const MAX_MATCH: usize = 258;
pub const WINDOW: usize = 32768;
pub const HASH_SIZE: usize = 32768;

/// How far down the tree to descend per position.
pub const MAX_PROBES: usize = 32;
/// Stop descending once a match at least this long is found.
pub const NICE_LEN: usize = 128;

pub fn hash3(a: u8, b: u8, c: u8) -> usize {
    let x = (a as u32)
        .wrapping_mul(2654435761)
        .wrapping_add((b as u32).wrapping_mul(2246822519))
        .wrapping_add((c as u32).wrapping_mul(3266489917));
    ((x >> 15) % 32768) as usize
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

/// Insert `pos` into the tree for its hash bucket and return the best match
/// found while doing so. `left`/`right` are child-pointer arrays indexed by
/// `p % 32768`, values are position+1 (0 = none), mirroring `head`/`prev`
/// elsewhere in this repo's slots.
pub fn bt_insert_and_search(
    input: &[u8],
    head: &mut [u32; 32768],
    left: &mut [u32; 32768],
    right: &mut [u32; 32768],
    pos: usize,
    cap: usize,
) -> (usize, usize) {
    let h = hash3(input[pos], input[pos + 1], input[pos + 2]);
    let mut cur = head[h] as usize;
    head[h] = (pos + 1) as u32;

    // idx0/which0 (idx1/which1): the child slot that will receive the next
    // tree node found to be, respectively, smaller and larger than `pos`'s
    // suffix. `which==0` means "write into left[idx]", `which==1` means
    // "write into right[idx]" -- a node's two children live in two different
    // fixed-size arrays here, so which array a pointer targets can change as
    // the walk descends.
    let mut idx0 = pos % 32768;
    let mut which0 = 0u8;
    let mut idx1 = pos % 32768;
    let mut which1 = 1u8;

    let mut len0 = 0usize;
    let mut len1 = 0usize;
    let mut best_len = 0usize;
    let mut best_dist = 0usize;
    let mut probes = 0usize;

    while probes < 32 && cur > 0 && cur <= pos {
        let cpos = cur - 1;
        if pos - cpos > 32768 {
            cur = 0;
        } else {
            let common = if len0 < len1 { len0 } else { len1 };
            let l = common + match_len(input, cpos + common, pos + common, cap - common);
            if l > best_len {
                best_len = l;
                best_dist = pos - cpos;
            }
            if l >= 128 || l >= cap {
                cur = 0;
            } else {
                let cslot = cpos % 32768;
                if input[cpos + l] < input[pos + l] {
                    if which0 == 0 {
                        left[idx0] = cur as u32;
                    } else {
                        right[idx0] = cur as u32;
                    }
                    idx0 = cslot;
                    which0 = 1;
                    cur = right[cslot] as usize;
                    len0 = l;
                } else {
                    if which1 == 0 {
                        left[idx1] = cur as u32;
                    } else {
                        right[idx1] = cur as u32;
                    }
                    idx1 = cslot;
                    which1 = 0;
                    cur = left[cslot] as usize;
                    len1 = l;
                }
            }
        }
        probes += 1;
    }
    // Whatever the walk didn't finish exploring gets dropped here rather than
    // carried forward -- a bounded-probe tree is necessarily an approximation
    // of a complete one, same trade `MAX_PROBES` makes for hash chains.
    if which0 == 0 {
        left[idx0] = 0;
    } else {
        right[idx0] = 0;
    }
    if which1 == 0 {
        left[idx1] = 0;
    } else {
        right[idx1] = 0;
    }
    (best_len, best_dist)
}

/// Greedy matching over the binary tree.
pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut head = [0u32; 32768];
    let mut left = [0u32; 32768];
    let mut right = [0u32; 32768];
    let mut ntok = 0usize;
    let mut pos = 0usize;
    let has3 = n >= 3;
    let lim = if has3 { n - 3 } else { 0 };
    while pos < n {
        let mut best_len = 0usize;
        let mut best_dist = 0usize;
        if has3 && pos <= lim {
            let mut cap = n - pos;
            if cap > 258 {
                cap = 258;
            }
            let found = bt_insert_and_search(input, &mut head, &mut left, &mut right, pos, cap);
            best_len = found.0;
            best_dist = found.1;
        }
        if best_len >= 3 {
            out[ntok] = 16777216u32 + ((best_dist - 1) as u32) * 256 + ((best_len - 3) as u32);
            ntok += 1;
            let end = pos + best_len;
            let mut k = pos + 1;
            while k < end && has3 && k <= lim {
                let mut kcap = n - k;
                if kcap > 258 {
                    kcap = 258;
                }
                let _ = bt_insert_and_search(input, &mut head, &mut left, &mut right, k, kcap);
                k += 1;
            }
            pos = end;
        } else {
            out[ntok] = input[pos] as u32;
            ntok += 1;
            pos += 1;
        }
    }
    ntok
}
