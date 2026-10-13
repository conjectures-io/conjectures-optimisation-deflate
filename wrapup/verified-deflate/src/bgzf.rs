//! BGZF (SAM/BAM specification §4.1): gzip members of at most 64 KiB, each
//! compressed on its own, with the block size in an extra field so readers can
//! seek. Output is readable by samtools, tabix and any gzip reader.

use crate::{deflate, Options};
use std::io::{self, Write};

/// Input bytes per block, as htslib writes them.
pub const BLOCK_INPUT: usize = 0xff00;
const MAX_BLOCK: usize = 65536;
const OVERHEAD: usize = 18 + 8;

/// The empty block every BGZF file ends with.
pub const EOF: [u8; 28] = [
    0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 0xff, 6, 0, 0x42, 0x43, 2, 0, 0x1b, 0, 3, 0, 0, 0, 0, 0, 0, 0,
    0, 0,
];

/// One block for `data`, or `None` if it does not fit in 64 KiB.
fn block(data: &[u8], options: Options) -> Option<Vec<u8>> {
    let raw = deflate(data, Options { chunk: BLOCK_INPUT, ..options });
    let total = raw.len() + OVERHEAD;
    if total > MAX_BLOCK {
        return None;
    }
    let mut out = Vec::with_capacity(total);
    out.extend_from_slice(&[0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 0xff, 6, 0, 0x42, 0x43, 2, 0]);
    out.extend_from_slice(&((total - 1) as u16).to_le_bytes());
    out.extend_from_slice(&raw);
    out.extend_from_slice(&crc32fast::hash(data).to_le_bytes());
    out.extend_from_slice(&(data.len() as u32).to_le_bytes());
    Some(out)
}

/// Blocks for `data`: a block that would not fit is split in half, as htslib does.
fn blocks(data: &[u8], options: Options, out: &mut Vec<u8>) {
    let mut todo = vec![data];
    while let Some(piece) = todo.pop() {
        match block(piece, options) {
            Some(b) => out.extend(b),
            None => {
                // A stored block always fits, so this terminates long before one byte.
                let (a, b) = piece.split_at(piece.len() / 2);
                todo.push(b);
                todo.push(a);
            }
        }
    }
}

/// A whole BGZF file for `data`, EOF block included.
pub fn compress(data: &[u8], options: impl Into<Options>) -> Vec<u8> {
    let options = options.into();
    let mut out = Vec::with_capacity(data.len() / 3 + 64);
    for piece in data.chunks(BLOCK_INPUT) {
        blocks(piece, options, &mut out);
    }
    out.extend_from_slice(&EOF);
    out
}

/// BGZF into a writer, a block at a time.
pub struct BgzfEncoder<W: Write> {
    w: Option<W>,
    options: Options,
    pending: Vec<u8>,
}

impl<W: Write> BgzfEncoder<W> {
    pub fn new(w: W, options: impl Into<Options>) -> Self {
        BgzfEncoder { w: Some(w), options: options.into(), pending: Vec::with_capacity(BLOCK_INPUT) }
    }

    fn emit(&mut self, all: bool) -> io::Result<()> {
        while self.pending.len() >= BLOCK_INPUT || (all && !self.pending.is_empty()) {
            let n = self.pending.len().min(BLOCK_INPUT);
            let mut out = Vec::new();
            blocks(&self.pending[..n], self.options, &mut out);
            self.w.as_mut().expect("writer present until finish").write_all(&out)?;
            self.pending.drain(..n);
        }
        Ok(())
    }

    /// Write what is pending and the EOF block, and return the writer.
    pub fn finish(mut self) -> io::Result<W> {
        self.emit(true)?;
        let mut w = self.w.take().expect("writer present until finish");
        w.write_all(&EOF)?;
        Ok(w)
    }
}

impl<W: Write> Write for BgzfEncoder<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.pending.extend_from_slice(buf);
        self.emit(false)?;
        Ok(buf.len())
    }

    /// Ends the current block early: a BGZF block boundary is a flush point.
    fn flush(&mut self) -> io::Result<()> {
        self.emit(true)?;
        self.w.as_mut().expect("writer present until finish").flush()
    }
}

impl<W: Write> Drop for BgzfEncoder<W> {
    fn drop(&mut self) {
        if self.w.is_some() {
            let _ = self.emit(true);
            if let Some(w) = self.w.as_mut() {
                let _ = w.write_all(&EOF);
            }
        }
    }
}
