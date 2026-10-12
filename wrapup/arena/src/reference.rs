//! Existing DEFLATE implementations, as raw DEFLATE, for comparison.
//!
//! Each is linked in and called in memory on one thread, as the parsers are.
//! External command-line tools (pigz, 7z, zopflipng, bgzip ...) are run by the
//! scenario scripts instead.

use std::io::Write;

#[derive(Clone)]
pub enum Reference {
    MinizOxide(u8),
    Libdeflate(i32),
    /// The system zlib through flate2 (madler zlib, or whatever libz-sys found).
    Zlib(u32),
    Zopfli(u64),
    /// A zlib-API library loaded by path, at a level.
    So(std::sync::Arc<ZlibApi>, i32),
}

impl Reference {
    pub fn name(&self) -> String {
        match self {
            Reference::MinizOxide(l) => format!("miniz_oxide-{l}"),
            Reference::Libdeflate(l) => format!("libdeflate-{l}"),
            Reference::Zlib(l) => format!("zlib-{l}"),
            Reference::Zopfli(i) => format!("zopfli-i{i}"),
            Reference::So(api, l) => format!("{}-{l}", api.name),
        }
    }

    /// `miniz_oxide-6`, `libdeflate-12`, `zlib-9`, `zopfli-i15`, or
    /// `so:NAME=PATH@LEVEL` for a zlib-API library.
    pub fn parse(spec: &str) -> Option<Reference> {
        if let Some(rest) = spec.strip_prefix("so:") {
            let (name, rest) = rest.split_once('=')?;
            let (path, level) = rest.rsplit_once('@')?;
            let api = ZlibApi::load(name, std::path::Path::new(path)).ok()?;
            return Some(Reference::So(std::sync::Arc::new(api), level.parse().ok()?));
        }
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
            Reference::So(ref api, level) => api.compress(&[input], level, 15, false),
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

/// zlib with a sync flush after every message and a `window_bits` window
/// (8..=15): permessage-deflate with context takeover.
pub fn zlib_messages(msgs: &[&[u8]], level: u32, window_bits: u8) -> Result<Vec<u8>, String> {
    use flate2::{Compress, Compression, FlushCompress, Status};
    // zlib refuses an 8-bit raw window; it would silently use 9 bits anyway.
    let mut c = Compress::new_with_window_bits(Compression::new(level), false, window_bits.max(9));
    let mut out: Vec<u8> = Vec::with_capacity(msgs.iter().map(|m| m.len()).sum::<usize>() / 2 + 1024);
    for m in msgs {
        let mut consumed = 0usize;
        loop {
            if out.capacity() - out.len() < 64 * 1024 {
                out.reserve(256 * 1024);
            }
            let before = c.total_in();
            c.compress_vec(&m[consumed..], &mut out, FlushCompress::Sync).map_err(|e| e.to_string())?;
            consumed += (c.total_in() - before) as usize;
            if consumed == m.len() && out.capacity() > out.len() {
                break;
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

// ── Any zlib-API library, loaded by path ──────────────────────────────────────

/// A zlib-compatible shared library (zlib-ng in compat mode, Cloudflare or
/// Chromium zlib, a pinned madler zlib) opened with `RTLD_DEEPBIND`, so its
/// symbols cannot collide with the zlib this binary links.
pub struct ZlibApi {
    pub name: String,
    pub version: String,
    _lib: libloading::os::unix::Library,
    init2: unsafe extern "C" fn(*mut ZStream, i32, i32, i32, i32, i32, *const std::ffi::c_char, i32) -> i32,
    deflate: unsafe extern "C" fn(*mut ZStream, i32) -> i32,
    end: unsafe extern "C" fn(*mut ZStream) -> i32,
    version_ptr: *const std::ffi::c_char,
}

/// `z_stream` from zlib.h (identical in zlib-ng's compat build).
#[repr(C)]
pub struct ZStream {
    next_in: *const u8,
    avail_in: u32,
    total_in: std::ffi::c_ulong,
    next_out: *mut u8,
    avail_out: u32,
    total_out: std::ffi::c_ulong,
    msg: *const std::ffi::c_char,
    state: *mut std::ffi::c_void,
    zalloc: *const std::ffi::c_void,
    zfree: *const std::ffi::c_void,
    opaque: *mut std::ffi::c_void,
    data_type: i32,
    adler: std::ffi::c_ulong,
    reserved: std::ffi::c_ulong,
}

const Z_NO_FLUSH: i32 = 0;
const Z_SYNC_FLUSH: i32 = 2;
const Z_FINISH: i32 = 4;
const Z_OK: i32 = 0;
const Z_STREAM_END: i32 = 1;
const Z_BUF_ERROR: i32 = -5;
const RTLD_DEEPBIND: i32 = 0x8;

// SAFETY: the library handle and function pointers are immutable once loaded;
// each call creates and ends its own z_stream.
unsafe impl Send for ZlibApi {}
unsafe impl Sync for ZlibApi {}

impl ZlibApi {
    pub fn load(name: &str, path: &std::path::Path) -> Result<ZlibApi, String> {
        use libloading::os::unix::{Library, RTLD_LOCAL, RTLD_NOW};
        let lib = unsafe { Library::open(Some(path), RTLD_NOW | RTLD_LOCAL | RTLD_DEEPBIND) }
            .map_err(|e| format!("dlopen {}: {e}", path.display()))?;
        unsafe {
            let init2 = *lib.get(b"deflateInit2_\0").map_err(|e| e.to_string())?;
            let deflate = *lib.get(b"deflate\0").map_err(|e| e.to_string())?;
            let end = *lib.get(b"deflateEnd\0").map_err(|e| e.to_string())?;
            let ver: unsafe extern "C" fn() -> *const std::ffi::c_char =
                *lib.get(b"zlibVersion\0").map_err(|e| e.to_string())?;
            let version_ptr = ver();
            let version = std::ffi::CStr::from_ptr(version_ptr).to_string_lossy().into_owned();
            Ok(ZlibApi { name: name.to_string(), version, _lib: lib, init2, deflate, end, version_ptr })
        }
    }

    /// Raw DEFLATE of `pieces` in order; with `sync`, a sync flush after each piece.
    pub fn compress(&self, pieces: &[&[u8]], level: i32, window_bits: i32, sync: bool) -> Result<Vec<u8>, String> {
        let total: usize = pieces.iter().map(|p| p.len()).sum();
        let mut out: Vec<u8> = Vec::with_capacity(total / 2 + 4096);
        let mut z: ZStream = unsafe { std::mem::zeroed() };
        let rc = unsafe {
            (self.init2)(&mut z, level, 8, -window_bits, 8, 0, self.version_ptr, std::mem::size_of::<ZStream>() as i32)
        };
        if rc != Z_OK {
            return Err(format!("{}: deflateInit2 returned {rc}", self.name));
        }
        let run = |z: &mut ZStream, data: &[u8], flush: i32, out: &mut Vec<u8>| -> Result<(), String> {
            z.next_in = data.as_ptr();
            z.avail_in = data.len() as u32;
            loop {
                if out.capacity() - out.len() < 64 * 1024 {
                    out.reserve(256 * 1024);
                }
                let room = (out.capacity() - out.len()).min(u32::MAX as usize);
                z.next_out = unsafe { out.as_mut_ptr().add(out.len()) };
                z.avail_out = room as u32;
                let rc = unsafe { (self.deflate)(z, flush) };
                let wrote = room - z.avail_out as usize;
                unsafe { out.set_len(out.len() + wrote) };
                match rc {
                    Z_STREAM_END => return Ok(()),
                    Z_OK | Z_BUF_ERROR => {
                        if z.avail_in == 0 && z.avail_out != 0 && flush != Z_FINISH {
                            return Ok(());
                        }
                    }
                    e => return Err(format!("{}: deflate returned {e}", self.name)),
                }
            }
        };
        let res = (|| {
            for p in pieces {
                run(&mut z, p, if sync { Z_SYNC_FLUSH } else { Z_NO_FLUSH }, &mut out)?;
            }
            run(&mut z, &[], Z_FINISH, &mut out)
        })();
        unsafe { (self.end)(&mut z) };
        res.map(|_| out)
    }
}
