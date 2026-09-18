//! The slot: LZ77 parsing -- disabled. Emits every byte as a literal token,
//! never a match. Not a real submission; a measurement baseline for how much
//! of the pipeline's total compression the LZ77 stage is responsible for, by
//! comparison against `template`/`hash-chains`/`lazy`/`optimal` through the
//! same fixed downstream Huffman coder.
//!
//! Tokens: `t < 256` literal, else `2^24 + (dist-1)*256 + (len-3)`. This parser
//! never emits the second form.

pub const MIN_MATCH: usize = 3;
pub const MAX_MATCH: usize = 258;
pub const WINDOW: usize = 32768;
pub const HASH_SIZE: usize = 32768;

pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let n = input.len();
    let mut i = 0usize;
    while i < n {
        out[i] = input[i] as u32;
        i += 1;
    }
    n
}
