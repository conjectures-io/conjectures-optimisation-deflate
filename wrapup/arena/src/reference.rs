//! Existing DEFLATE implementations, as raw DEFLATE, for comparison.
//!
//! Each is linked in and called in memory on one thread, as the parsers are.
//! External command-line tools (pigz, 7z, zopflipng, bgzip ...) are run by the
//! scenario scripts instead.

use std::io::Write;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reference {
    MinizOxide(u8),
    Libdeflate(i32),
    /// The system zlib through flate2 (madler zlib, or whatever libz-sys found).
    Zlib(u32),
    Zopfli(u64),
}

impl Reference {
    pub fn name(&self) -> String {
        match self {
            Reference::MinizOxide(l) => format!("miniz_oxide-{l}"),
            Reference::Libdeflate(l) => format!("libdeflate-{l}"),
            Reference::Zlib(l) => format!("zlib-{l}"),
            Reference::Zopfli(i) => format!("zopfli-i{i}"),
        }
    }

    /// `miniz_oxide-6`, `libdeflate-12`, `zlib-9`, `zopfli-i15`.
    pub fn parse(spec: &str) -> Option<Reference> {
        let (kind, arg) = spec.rsplit_once('-')?;
        match kind {
            "miniz_oxide" | "miniz" => Some(Reference::MinizOxide(arg.parse().ok().filter(|l| *l <= 10)?)),
            "libdeflate" => Some(Reference::Libdeflate(arg.parse().ok().filter(|l| (0..=12).contains(l))?)),
            "zlib" => Some(Reference::Zlib(arg.parse().ok().filter(|l| *l <= 9)?)),
            "zopfli" => Some(Reference::Zopfli(arg.strip_prefix('i')?.parse().ok().filter(|i| *i > 0)?)),
            _ => None,
        }
    }

    pub fn compress(&self, input: &[u8]) -> Result<Vec<u8>, String> {
        match *self {
            Reference::MinizOxide(level) => Ok(miniz_oxide::deflate::compress_to_vec(input, level)),
            Reference::Libdeflate(level) => {
                let lvl = libdeflater::CompressionLvl::new(level).map_err(|e| format!("{e:?}"))?;
                let mut c = libdeflater::Compressor::new(lvl);
                let mut buf = vec![0u8; c.deflate_compress_bound(input.len())];
                let n = c.deflate_compress(input, &mut buf).map_err(|e| format!("libdeflate: {e:?}"))?;
                buf.truncate(n);
                Ok(buf)
            }
            Reference::Zlib(level) => {
                let mut e = flate2::write::DeflateEncoder::new(
                    Vec::with_capacity(input.len() / 2 + 64),
                    flate2::Compression::new(level),
                );
                e.write_all(input).map_err(|e| e.to_string())?;
                e.finish().map_err(|e| e.to_string())
            }
            Reference::Zopfli(iterations) => {
                let opts = zopfli::Options {
                    iteration_count: std::num::NonZeroU64::new(iterations).expect("checked in parse"),
                    ..Default::default()
                };
                let mut out = Vec::new();
                zopfli::compress(opts, zopfli::Format::Deflate, input, &mut out).map_err(|e| e.to_string())?;
                Ok(out)
            }
        }
    }
}

/// zlib streaming with a sync flush every `flush_every` input bytes, written in
/// `write_size` pieces: the reference for the flushing scenarios.
pub fn zlib_stream(input: &[u8], level: u32, write_size: usize, flush_every: Option<usize>) -> Result<Vec<u8>, String> {
    use flate2::{Compress, Compression, FlushCompress, Status};
    let mut c = Compress::new(Compression::new(level), false);
    let mut out: Vec<u8> = Vec::with_capacity(input.len() / 2 + 1024);
    let mut since = 0usize;
    // zlib has finished a call's work once all input is taken and output space is left.
    let run = |c: &mut Compress, data: &[u8], flush: FlushCompress, out: &mut Vec<u8>| -> Result<(), String> {
        let mut consumed = 0usize;
        loop {
            if out.capacity() - out.len() < 64 * 1024 {
                out.reserve(256 * 1024);
            }
            let before = c.total_in();
            c.compress_vec(&data[consumed..], out, flush).map_err(|e| e.to_string())?;
            consumed += (c.total_in() - before) as usize;
            if consumed == data.len() && out.capacity() > out.len() {
                return Ok(());
            }
        }
    };
    for piece in input.chunks(write_size.max(1)) {
        run(&mut c, piece, FlushCompress::None, &mut out)?;
        since += piece.len();
        if let Some(every) = flush_every {
            if since >= every {
                run(&mut c, &[], FlushCompress::Sync, &mut out)?;
                since = 0;
            }
        }
    }
    loop {
        if out.capacity() - out.len() < 64 * 1024 {
            out.reserve(256 * 1024);
        }
        if c.compress_vec(&[], &mut out, FlushCompress::Finish).map_err(|e| e.to_string())? == Status::StreamEnd {
            break;
        }
    }
    Ok(out)
}
