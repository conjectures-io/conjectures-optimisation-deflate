//! Compressing with a one-shot parser: whole buffer, independent chunks, or a
//! stream that carries a 32 KiB history across chunks.
//!
//! The history adapter never changes a parser. It calls `parse(history ‖ chunk ‖
//! lookahead)` and commits only the tokens that start at or after the history
//! and before the chunk's end; a match that starts in the history and runs past
//! it is trimmed to its remainder (same distance) or, if fewer than 3 bytes
//! remain, to literals. Tokens starting in the lookahead are dropped and their
//! bytes parsed again next time with fresh history. Every committed distance
//! points inside bytes the decoder already has, because it pointed inside the
//! parsed buffer and the buffer starts at bytes already emitted.

use crate::encoder::{Encoder, Flush, Huffman};
use crate::parser::Parser;
use crate::token;
use std::time::Instant;

pub const WINDOW: usize = 32768;
pub const MAX_MATCH: usize = 258;

/// Where the time went, and how much parsing the history cost.
#[derive(Clone, Debug, Default, serde::Serialize)]
pub struct Stats {
    pub parse_s: f64,
    pub encode_s: f64,
    /// Bytes handed to `parse`, history and lookahead included.
    pub parsed_bytes: u64,
    pub parse_calls: u64,
    pub committed_tokens: u64,
    /// Matches cut at the history boundary.
    pub trimmed: u64,
}

fn tok_len(t: u32) -> Result<(usize, u32), String> {
    match token::decode(t) {
        token::Token::Literal(_) => Ok((1, 0)),
        token::Token::Match { dist, len } => Ok((len as usize, dist)),
        token::Token::Invalid => Err(format!("{t} is not a legal token")),
    }
}

/// Parse `input` in one call and encode it: the competition's own setting.
pub fn compress_whole(p: &dyn Parser, input: &[u8], h: Huffman) -> Result<(Vec<u8>, Stats), String> {
    let mut st = Stats::default();
    let mut toks = vec![0u32; input.len().max(1)];
    let t0 = Instant::now();
    let n = p.parse(input, &mut toks[..input.len()])?;
    st.parse_s = t0.elapsed().as_secs_f64();
    st.parsed_bytes = input.len() as u64;
    st.parse_calls = 1;
    st.committed_tokens = n as u64;
    let t1 = Instant::now();
    let out = crate::encoder::encode(&toks[..n], input.len(), h)?;
    st.encode_s = t1.elapsed().as_secs_f64();
    Ok((out, st))
}

/// Each chunk parsed with no history. `members = true` gives one finished raw
/// DEFLATE stream per chunk (BGZF, ZIP entries); `false` gives one stream with a
/// full flush between chunks (`pigz --independent`).
pub fn compress_independent(
    p: &dyn Parser,
    input: &[u8],
    chunk: usize,
    h: Huffman,
    members: bool,
) -> Result<(Vec<Vec<u8>>, Stats), String> {
    assert!(chunk > 0);
    let mut st = Stats::default();
    let mut toks = vec![0u32; chunk.min(input.len()).max(1)];
    let mut outs = Vec::new();
    let mut enc = Encoder::new(h);
    let pieces: Vec<&[u8]> = if input.is_empty() { vec![&input[..0]] } else { input.chunks(chunk).collect() };
    let last = pieces.len() - 1;
    for (i, piece) in pieces.into_iter().enumerate() {
        let t0 = Instant::now();
        let n = p.parse(piece, &mut toks[..piece.len()])?;
        st.parse_s += t0.elapsed().as_secs_f64();
        st.parsed_bytes += piece.len() as u64;
        st.parse_calls += 1;
        st.committed_tokens += n as u64;
        let t1 = Instant::now();
        if members {
            outs.push(crate::encoder::encode(&toks[..n], piece.len(), h)?);
        } else {
            let before = enc.produced();
            enc.push(&toks[..n])?;
            if enc.produced() - before != piece.len() as u64 {
                return Err(format!("chunk {i}: tokens cover {} of {} bytes", enc.produced() - before, piece.len()));
            }
            if i == last {
                enc.finish();
            } else {
                enc.flush(Flush::Full);
            }
        }
        st.encode_s += t1.elapsed().as_secs_f64();
    }
    if !members {
        outs.push(enc.take());
    }
    Ok((outs, st))
}

#[derive(Clone, Copy, Debug)]
pub struct StreamConfig {
    /// New bytes committed per parse call.
    pub chunk: usize,
    /// Bytes parsed past the commit point and parsed again next call. At least
    /// `MAX_MATCH`, so a committed match is never cut short by the buffer end.
    pub lookahead: usize,
    pub huffman: Huffman,
}

impl StreamConfig {
    pub fn new(chunk: usize, huffman: Huffman) -> Self {
        StreamConfig { chunk, lookahead: 4096, huffman }
    }
}

/// A DEFLATE stream from a one-shot parser, history carried across chunks.
pub struct HistoryCompressor<'p> {
    parser: &'p dyn Parser,
    cfg: StreamConfig,
    enc: Encoder,
    /// `buf[start..start + hist]` is history (already encoded); the rest is pending.
    buf: Vec<u8>,
    start: usize,
    hist: usize,
    toks: Vec<u32>,
    commit: Vec<u32>,
    pub stats: Stats,
}

impl<'p> HistoryCompressor<'p> {
    pub fn new(parser: &'p dyn Parser, cfg: StreamConfig) -> Self {
        assert!(cfg.chunk > 0 && cfg.lookahead >= MAX_MATCH);
        HistoryCompressor {
            parser,
            cfg,
            enc: Encoder::new(cfg.huffman),
            buf: Vec::new(),
            start: 0,
            hist: 0,
            toks: Vec::new(),
            commit: Vec::new(),
            stats: Stats::default(),
        }
    }

    fn pending(&self) -> usize {
        self.buf.len() - self.start - self.hist
    }

    pub fn write(&mut self, data: &[u8]) -> Result<(), String> {
        if self.start > 0 && self.start >= self.buf.len() / 2 {
            self.buf.drain(..self.start);
            self.start = 0;
        }
        self.buf.extend_from_slice(data);
        while self.pending() >= self.cfg.chunk + self.cfg.lookahead {
            let end = self.start + self.hist + self.cfg.chunk + self.cfg.lookahead;
            self.step(end, self.cfg.chunk)?;
        }
        Ok(())
    }

    /// Commit everything pending, then flush the encoder.
    pub fn flush(&mut self, mode: Flush) -> Result<(), String> {
        self.drain_all()?;
        let t = Instant::now();
        self.enc.flush(mode);
        self.stats.encode_s += t.elapsed().as_secs_f64();
        if mode == Flush::Full {
            self.start = self.buf.len();
            self.hist = 0;
        }
        Ok(())
    }

    pub fn finish(&mut self) -> Result<(), String> {
        self.drain_all()?;
        let t = Instant::now();
        self.enc.finish();
        self.stats.encode_s += t.elapsed().as_secs_f64();
        Ok(())
    }

    /// Completed output since the last call.
    pub fn take(&mut self) -> Vec<u8> {
        self.enc.take()
    }

    fn drain_all(&mut self) -> Result<(), String> {
        while self.pending() > 0 {
            let p = self.pending();
            if p >= self.cfg.chunk + self.cfg.lookahead {
                let end = self.start + self.hist + self.cfg.chunk + self.cfg.lookahead;
                self.step(end, self.cfg.chunk)?;
            } else {
                let end = self.buf.len();
                self.step(end, p)?;
            }
        }
        Ok(())
    }

    /// Parse `buf[start..end]`; commit tokens starting in `[hist, hist + limit)`
    /// relative to `start`; the last committed token may run past `limit`.
    fn step(&mut self, end: usize, limit: usize) -> Result<(), String> {
        let input = &self.buf[self.start..end];
        let n = input.len();
        let hist = self.hist;
        let limit = hist + limit;
        let exact = end == self.buf.len() && limit == n;
        if self.toks.len() < n {
            self.toks.resize(n, 0);
        }
        let t0 = Instant::now();
        let k = self.parser.parse(input, &mut self.toks[..n])?;
        self.stats.parse_s += t0.elapsed().as_secs_f64();
        self.stats.parsed_bytes += n as u64;
        self.stats.parse_calls += 1;

        self.commit.clear();
        let mut pos = 0usize;
        let mut committed_to = hist;
        for &t in &self.toks[..k] {
            let (len, dist) = tok_len(t)?;
            let next = pos + len;
            if next > n {
                return Err(format!("{}: a token runs past the input ({next} > {n})", self.parser.name()));
            }
            if next <= hist {
                pos = next;
                continue;
            }
            if pos >= limit {
                break;
            }
            if pos < hist {
                let rem = next - hist;
                self.stats.trimmed += 1;
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
        if committed_to <= hist {
            return Err(format!("{}: no progress past byte {hist} of {n}", self.parser.name()));
        }
        if exact && committed_to != n {
            return Err(format!("{}: tokens cover {committed_to} of {n} bytes", self.parser.name()));
        }
        self.stats.committed_tokens += self.commit.len() as u64;
        let t1 = Instant::now();
        self.enc.push(&self.commit)?;
        self.stats.encode_s += t1.elapsed().as_secs_f64();

        let keep = committed_to.min(WINDOW);
        self.start += committed_to - keep;
        self.hist = keep;
        Ok(())
    }
}

/// Stream `input` through a [`HistoryCompressor`] in `write_size` pieces, with
/// an optional sync flush every `flush_every` input bytes.
pub fn compress_stream(
    p: &dyn Parser,
    input: &[u8],
    cfg: StreamConfig,
    write_size: usize,
    flush_every: Option<usize>,
) -> Result<(Vec<u8>, Stats), String> {
    let mut c = HistoryCompressor::new(p, cfg);
    let mut out = Vec::new();
    let mut since_flush = 0usize;
    for piece in input.chunks(write_size.max(1)) {
        c.write(piece)?;
        since_flush += piece.len();
        if let Some(every) = flush_every {
            if since_flush >= every {
                c.flush(Flush::Sync)?;
                since_flush = 0;
            }
        }
        out.extend(c.take());
    }
    c.finish()?;
    out.extend(c.take());
    Ok((out, c.stats.clone()))
}
