//! # verified-deflate
//!
//! gzip, zlib and raw DEFLATE compression with LZ77 parsers that are **proved
//! correct in Lean**: for every possible input, the tokens a parser emits decode
//! back to that input. The parsers come from the conjectures.io DEFLATE
//! competition (2026); see `README.md` for where each one comes from, what is
//! proved and what is only tested, and measured results.
//!
//! The output is ordinary DEFLATE: gunzip, zlib, browsers, Python, `unzip` and
//! samtools read it unchanged. Nothing new is needed to decompress.
//!
//! ```
//! use std::io::Write;
//! use verified_deflate::{GzEncoder, Level};
//!
//! let mut gz = GzEncoder::new(Vec::new(), Level::Max);
//! gz.write_all(b"hello hello hello hello")?;
//! let compressed = gz.finish()?;
//! assert_eq!(&compressed[..2], &[0x1f, 0x8b]);
//! # Ok::<(), std::io::Error>(())
//! ```
//!
//! Input is compressed in chunks (1 MiB by default) that each see the previous
//! 32 KiB as history, so memory stays bounded (20–45 MiB) for any input size and
//! the result is a single continuous stream.

mod encoder;
mod stream;
mod token;

pub mod bgzf;
pub mod parsers;

use std::io::{self, Write};

/// How hard to compress. Each level is one proved parser.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Level {
    /// Submission #521: about 3.5% smaller than `gzip -9` on large files, at
    /// about 1.4× its speed (≈ 27 MB/s on one core of the test machine).
    Balanced,
    /// Submission #85: about 3.7% smaller than `gzip -9` on large files
    /// (≈ 16 MB/s); best of the three on logs.
    #[default]
    High,
    /// Submission #243: libdeflate level 12's size on web assets, archives and
    /// large files, within 0.5% of zopfli (≈ 6 MB/s).
    Max,
}

impl Level {
    pub const ALL: [Level; 3] = [Level::Balanced, Level::High, Level::Max];

    /// The competition submission behind this level.
    pub fn submission(self) -> u32 {
        match self {
            Level::Balanced => 521,
            Level::High => 85,
            Level::Max => 243,
        }
    }

    /// The parser behind this level.
    pub fn parser(self) -> fn(&[u8], &mut [u32]) -> usize {
        match self {
            Level::Balanced => parsers::p521,
            Level::High => parsers::p85,
            Level::Max => parsers::p243,
        }
    }

    /// gzip-style levels: 1–3 Balanced, 4–6 High, 7–9 Max.
    pub fn from_gzip(level: u32) -> Level {
        match level {
            0..=3 => Level::Balanced,
            4..=6 => Level::High,
            _ => Level::Max,
        }
    }
}

/// Compression settings beyond the level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Options {
    pub level: Level,
    /// Input bytes per parser call; 1 MiB is the measured setting. Token
    /// buffers take about 4× this, on top of each parser's own tables (peak
    /// 20–45 MiB in total at 1 MiB, independent of the input size). Chunking never costs more than a few bytes of output
    /// and protects against parsers that degrade on very large single buffers.
    pub chunk: usize,
    /// Choose block boundaries from the data (on by default). Off reproduces the
    /// competition's fixed 16,384-token blocks, about 0.8% larger.
    pub adaptive_blocks: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { level: Level::default(), chunk: 1 << 20, adaptive_blocks: true }
    }
}

impl From<Level> for Options {
    fn from(level: Level) -> Self {
        Options { level, ..Options::default() }
    }
}

/// Raw DEFLATE (RFC 1951) into a writer.
pub struct DeflateEncoder<W: Write> {
    raw: stream::Raw,
    w: Option<W>,
    finished: bool,
}

impl<W: Write> DeflateEncoder<W> {
    pub fn new(w: W, options: impl Into<Options>) -> Self {
        let o = options.into();
        assert!(o.chunk > 0, "chunk must be positive");
        DeflateEncoder {
            raw: stream::Raw::new(o.level.parser(), o.chunk, o.adaptive_blocks),
            w: Some(w),
            finished: false,
        }
    }

    fn emit(&mut self) -> io::Result<()> {
        let out = self.raw.take();
        if !out.is_empty() {
            self.get_mut().write_all(&out)?;
        }
        Ok(())
    }

    /// Write the final block, once; later writes are an error.
    pub fn try_finish(&mut self) -> io::Result<()> {
        if !self.finished {
            self.finished = true;
            self.raw.finish()?;
            self.emit()?;
        }
        Ok(())
    }

    /// Write the final block and return the writer.
    pub fn finish(mut self) -> io::Result<W> {
        self.try_finish()?;
        Ok(self.w.take().expect("writer present until finish"))
    }

    pub fn get_ref(&self) -> &W {
        self.w.as_ref().expect("writer present until finish")
    }

    pub fn get_mut(&mut self) -> &mut W {
        self.w.as_mut().expect("writer present until finish")
    }
}

impl<W: Write> Write for DeflateEncoder<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.finished {
            return Err(io::Error::other("write after finish"));
        }
        self.raw.write(buf)?;
        self.emit()?;
        Ok(buf.len())
    }

    /// A sync flush (as zlib's `Z_SYNC_FLUSH`): everything written so far can be
    /// decoded by the reader. Costs a few bytes and a block boundary.
    fn flush(&mut self) -> io::Result<()> {
        if !self.finished {
            self.raw.sync_flush()?;
            self.emit()?;
        }
        self.get_mut().flush()
    }
}

impl<W: Write> Drop for DeflateEncoder<W> {
    fn drop(&mut self) {
        // Best effort, as flate2 does; call `finish` to see errors.
        if self.w.is_some() {
            let _ = self.try_finish();
        }
    }
}

/// gzip (RFC 1952) into a writer. The header carries no name and mtime 0, so the
/// output depends only on the input and the options.
pub struct GzEncoder<W: Write> {
    inner: DeflateEncoder<W>,
    crc: crc32fast::Hasher,
    len: u64,
    started: bool,
    trailed: bool,
}

impl<W: Write> GzEncoder<W> {
    pub fn new(w: W, options: impl Into<Options>) -> Self {
        GzEncoder {
            inner: DeflateEncoder::new(w, options),
            crc: crc32fast::Hasher::new(),
            len: 0,
            started: false,
            trailed: false,
        }
    }

    fn header(&mut self) -> io::Result<()> {
        if !self.started {
            self.started = true;
            self.inner.get_mut().write_all(&[0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 0xff])?;
        }
        Ok(())
    }

    /// Write the final block and the trailer, once.
    pub fn try_finish(&mut self) -> io::Result<()> {
        if !self.trailed {
            self.header()?;
            self.inner.try_finish()?;
            self.trailed = true;
            let crc = self.crc.clone().finalize();
            let len = self.len as u32;
            let w = self.inner.get_mut();
            w.write_all(&crc.to_le_bytes())?;
            w.write_all(&len.to_le_bytes())?;
        }
        Ok(())
    }

    pub fn finish(mut self) -> io::Result<W> {
        self.try_finish()?;
        Ok(self.inner.w.take().expect("writer present until finish"))
    }

    pub fn get_ref(&self) -> &W {
        self.inner.get_ref()
    }
}

impl<W: Write> Write for GzEncoder<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.header()?;
        let n = self.inner.write(buf)?;
        self.crc.update(&buf[..n]);
        self.len += n as u64;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.header()?;
        self.inner.flush()
    }
}

impl<W: Write> Drop for GzEncoder<W> {
    fn drop(&mut self) {
        if self.inner.w.is_some() {
            let _ = self.try_finish();
        }
    }
}

/// zlib (RFC 1950) into a writer.
pub struct ZlibEncoder<W: Write> {
    inner: DeflateEncoder<W>,
    adler: adler2::Adler32,
    started: bool,
    trailed: bool,
}

impl<W: Write> ZlibEncoder<W> {
    pub fn new(w: W, options: impl Into<Options>) -> Self {
        ZlibEncoder { inner: DeflateEncoder::new(w, options), adler: adler2::Adler32::new(), started: false, trailed: false }
    }

    fn header(&mut self) -> io::Result<()> {
        if !self.started {
            self.started = true;
            // CMF 0x78 (deflate, 32 KiB window), FLEVEL 3 (maximum compression).
            self.inner.get_mut().write_all(&[0x78, 0xda])?;
        }
        Ok(())
    }

    /// Write the final block and the checksum, once.
    pub fn try_finish(&mut self) -> io::Result<()> {
        if !self.trailed {
            self.header()?;
            self.inner.try_finish()?;
            self.trailed = true;
            let sum = self.adler.checksum();
            self.inner.get_mut().write_all(&sum.to_be_bytes())?;
        }
        Ok(())
    }

    pub fn finish(mut self) -> io::Result<W> {
        self.try_finish()?;
        Ok(self.inner.w.take().expect("writer present until finish"))
    }

    pub fn get_ref(&self) -> &W {
        self.inner.get_ref()
    }
}

impl<W: Write> Write for ZlibEncoder<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.header()?;
        let n = self.inner.write(buf)?;
        self.adler.write_slice(&buf[..n]);
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.header()?;
        self.inner.flush()
    }
}

impl<W: Write> Drop for ZlibEncoder<W> {
    fn drop(&mut self) {
        if self.inner.w.is_some() {
            let _ = self.try_finish();
        }
    }
}

// The one-shot helpers write to a `Vec`, which cannot fail; an error here would
// mean a parser broke its proved contract, which the stream checks for anyway.

/// Raw DEFLATE of `data`.
pub fn deflate(data: &[u8], options: impl Into<Options>) -> Vec<u8> {
    let mut e = DeflateEncoder::new(Vec::with_capacity(data.len() / 3 + 64), options);
    e.write_all(data).expect("writing to a Vec cannot fail");
    e.finish().expect("writing to a Vec cannot fail")
}

/// gzip of `data`.
pub fn gzip(data: &[u8], options: impl Into<Options>) -> Vec<u8> {
    let mut e = GzEncoder::new(Vec::with_capacity(data.len() / 3 + 64), options);
    e.write_all(data).expect("writing to a Vec cannot fail");
    e.finish().expect("writing to a Vec cannot fail")
}

/// zlib of `data`.
pub fn zlib(data: &[u8], options: impl Into<Options>) -> Vec<u8> {
    let mut e = ZlibEncoder::new(Vec::with_capacity(data.len() / 3 + 64), options);
    e.write_all(data).expect("writing to a Vec cannot fail");
    e.finish().expect("writing to a Vec cannot fail")
}
