//! Raw DEFLATE from a one-shot parser, streamed: the parser sees `history ‖ new
//! data ‖ lookahead` and only the tokens that start in the new data are kept.
//! The same algorithm as `wrapup/arena`'s `HistoryCompressor` (tests check the
//! output is identical).

use crate::encoder::{Blocks, Encoder, Flush, Huffman};
use crate::token;
use std::io;

pub(crate) const WINDOW: usize = 32768;
const LOOKAHEAD: usize = 4096;

pub(crate) type ParseFn = fn(&[u8], &mut [u32]) -> usize;

fn invalid(msg: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

pub(crate) struct Raw {
    parse: ParseFn,
    chunk: usize,
    enc: Encoder,
    /// `buf[start..start + hist]` has been encoded (history); the rest is pending.
    buf: Vec<u8>,
    start: usize,
    hist: usize,
    toks: Vec<u32>,
    commit: Vec<u32>,
}

impl Raw {
    pub(crate) fn new(parse: ParseFn, chunk: usize, adaptive: bool) -> Raw {
        assert!(chunk > 0);
        let blocks = if adaptive { Blocks::Adaptive } else { Blocks::Fixed };
        Raw {
            parse,
            chunk,
            enc: Encoder::with_blocks(Huffman::Fast, blocks),
            buf: Vec::new(),
            start: 0,
            hist: 0,
            toks: Vec::new(),
            commit: Vec::new(),
        }
    }

    fn pending(&self) -> usize {
        self.buf.len() - self.start - self.hist
    }

    pub(crate) fn write(&mut self, data: &[u8]) -> io::Result<()> {
        if self.start > 0 && self.start >= self.buf.len() / 2 {
            self.buf.drain(..self.start);
            self.start = 0;
        }
        self.buf.extend_from_slice(data);
        while self.pending() >= self.chunk + LOOKAHEAD {
            let end = self.start + self.hist + self.chunk + LOOKAHEAD;
            self.step(end, self.chunk)?;
        }
        Ok(())
    }

    fn drain_all(&mut self) -> io::Result<()> {
        while self.pending() > 0 {
            let p = self.pending();
            if p >= self.chunk + LOOKAHEAD {
                let end = self.start + self.hist + self.chunk + LOOKAHEAD;
                self.step(end, self.chunk)?;
            } else {
                let end = self.buf.len();
                self.step(end, p)?;
            }
        }
        Ok(())
    }

    /// Everything written so far becomes decodable; the history is kept.
    pub(crate) fn sync_flush(&mut self) -> io::Result<()> {
        self.drain_all()?;
        self.enc.flush(Flush::Sync);
        Ok(())
    }

    pub(crate) fn finish(&mut self) -> io::Result<()> {
        self.drain_all()?;
        self.enc.finish();
        Ok(())
    }

    /// Completed output since the last call.
    pub(crate) fn take(&mut self) -> Vec<u8> {
        self.enc.take()
    }

    fn step(&mut self, end: usize, limit: usize) -> io::Result<()> {
        let input = &self.buf[self.start..end];
        let n = input.len();
        let hist = self.hist;
        let limit = hist + limit;
        let exact = end == self.buf.len() && limit == n;
        if self.toks.len() < n {
            self.toks.resize(n, 0);
        }
        let k = (self.parse)(input, &mut self.toks[..n]);
        if k > n {
            return Err(invalid(format!("parser reported {k} tokens for {n} bytes")));
        }
        self.commit.clear();
        let mut pos = 0usize;
        let mut committed_to = hist;
        for &t in &self.toks[..k] {
            let (len, dist) = match token::decode(t) {
                token::Token::Literal(_) => (1usize, 0u32),
                token::Token::Match { dist, len } => (len as usize, dist),
                token::Token::Invalid => return Err(invalid(format!("illegal token {t}"))),
            };
            let next = pos + len;
            if next > n {
                return Err(invalid("a token runs past the input".to_string()));
            }
            if next <= hist {
                pos = next;
                continue;
            }
            if pos >= limit {
                break;
            }
            if pos < hist {
                // Starts in the history, ends in the new data: keep the remainder.
                let rem = next - hist;
                if rem >= 3 {
                    self.commit.push(token::encode_match(dist, rem as u32));
                } else {
                    for &b in &input[hist..next] {
                        self.commit.push(b as u32);
                    }
                }
            } else {
                self.commit.push(t);
            }
            pos = next;
            committed_to = next;
        }
        if committed_to <= hist || (exact && committed_to != n) {
            return Err(invalid(format!("tokens cover {committed_to} of {n} bytes")));
        }
        self.enc.push(&self.commit).map_err(invalid)?;
        let keep = committed_to.min(WINDOW);
        self.start += committed_to - keep;
        self.hist = keep;
        Ok(())
    }
}
