//! The proved parsers, as the competition accepted them (unmodified source).
//! Each writes LZ77 tokens: `t < 256` is the literal byte `t`;
//! `t = 2^24 + (dist - 1) * 256 + (len - 3)` copies `len` bytes from `dist` back
//! (`1 <= dist <= 32768`, `3 <= len <= 258`). `out.len()` must be at least
//! `input.len()`; the return value is the number of tokens written.

#[allow(dead_code, unused, clippy::all)]
#[path = "../parsers/p521/parse.rs"]
mod p521_src;
#[allow(dead_code, unused, clippy::all)]
#[path = "../parsers/p85/parse.rs"]
mod p85_src;
#[allow(dead_code, unused, clippy::all)]
#[path = "../parsers/p243/parse.rs"]
mod p243_src;

/// Competition submission #521 (2026-10-08).
pub fn p521(input: &[u8], out: &mut [u32]) -> usize {
    p521_src::parse(input, out)
}
/// Competition submission #85 (2026-09-29).
pub fn p85(input: &[u8], out: &mut [u32]) -> usize {
    p85_src::parse(input, out)
}
/// Competition submission #243 (2026-10-02).
pub fn p243(input: &[u8], out: &mut [u32]) -> usize {
    p243_src::parse(input, out)
}
