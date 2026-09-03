//! The token encoding, in Rust.
//!
//! This is the *same* function as `LZ77.emit` in `competition/lean/Lz77/Spec.lean`,
//! written twice because one copy has to run and the other has to be reasoned
//! about. Keeping them in step is a real obligation of the operator, and it is
//! the one place where the harness and the contract can silently disagree.
//!
//! The correspondence, line for line:
//!
//! | Lean (`Spec.lean`)                        | Rust (here)                    |
//! |-------------------------------------------|--------------------------------|
//! | `if t < 256 then some (acc ++ [t])`        | `t < 256 => Literal(t as u8)`  |
//! | `MATCH_BASE ≤ t ∧ t < TOK_LIMIT`           | `t >= MATCH_BASE && t < TOK_LIMIT` |
//! | `tokDist t = (t - MATCH_BASE) / 256 + 1`   | `r / 256 + 1`                  |
//! | `tokLen t  = (t - MATCH_BASE) % 256 + 3`   | `r % 256 + 3`                  |
//! | `if d ≤ acc.length then … else none`       | checked by `deflate::encode`   |
//! | otherwise `none`                           | `Invalid`                      |
//!
//! `round_trips_over_every_legal_match` below re-checks the arithmetic half of
//! that table exhaustively over every legal `(dist, len)`.

// The bounds and `encode_match` are documentation of the encoding as much as
// code: they are what a reader checks the table above against, and what the
// tests use. The encoder itself only needs `decode`.
#![allow(dead_code)]

/// Where match tokens start. `LZ77.MATCH_BASE`.
pub const MATCH_BASE: u32 = 16_777_216;
/// One past the last legal token. `LZ77.TOK_LIMIT`.
pub const TOK_LIMIT: u32 = 25_165_824;

pub const MIN_MATCH: u32 = 3;
pub const MAX_MATCH: u32 = 258;
pub const MAX_DIST: u32 = 32_768;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token {
    Literal(u8),
    Match { dist: u32, len: u32 },
    Invalid,
}

pub fn decode(t: u32) -> Token {
    if t < 256 {
        Token::Literal(t as u8)
    } else if t >= MATCH_BASE && t < TOK_LIMIT {
        let r = t - MATCH_BASE;
        Token::Match { dist: r / 256 + 1, len: r % 256 + 3 }
    } else {
        Token::Invalid
    }
}

/// `LZ77.mkMatch`. Only used by tests and by alternative parsers.
pub fn encode_match(dist: u32, len: u32) -> u32 {
    MATCH_BASE + (dist - 1) * 256 + (len - 3)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_over_every_legal_match() {
        for dist in 1..=MAX_DIST {
            for len in MIN_MATCH..=MAX_MATCH {
                let t = encode_match(dist, len);
                assert!(t >= MATCH_BASE && t < TOK_LIMIT, "dist {dist} len {len} out of range");
                assert_eq!(decode(t), Token::Match { dist, len });
            }
        }
    }

    #[test]
    fn literals_are_below_the_match_space() {
        for b in 0..=255u32 {
            assert_eq!(decode(b), Token::Literal(b as u8));
        }
        assert_eq!(decode(256), Token::Invalid);
        assert_eq!(decode(MATCH_BASE - 1), Token::Invalid);
        assert_eq!(decode(TOK_LIMIT), Token::Invalid);
    }
}
