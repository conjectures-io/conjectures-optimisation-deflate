//! What can be measured, and the correctness checks every result goes through.

use crate::deflate;
use crate::loader::{Parser, PANICKED};
use crate::record::{sha256_tokens, MethodMeta};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// Where the driver puts the two files the engine reads out of a generated crate.
pub const LIB_IN_CRATE: &str = "target/release/libcandidate.so";
pub const SOURCE_IN_CRATE: &str = "src/parse.rs";

pub enum Kind {
    /// A dlopen'd `parse.rs`: the thing under test.
    Slot(Parser),
    /// A reference bar. Not provable, never on the Pareto front, context only.
    MinizOxide(u8),
    LibDeflate,
}

pub struct Method {
    pub name: String,
    pub kind: Kind,
    crate_dir: Option<PathBuf>,
    source_sha256: Option<String>,
    lib_sha256: Option<String>,
}

/// One execution of one method on one input.
pub struct Once {
    pub parse_s: f64,
    pub tokens: Option<u64>,
    pub tokens_sha256: Option<String>,
    pub compressed: Option<Vec<u8>>,
    pub encode_s: Option<f64>,
    pub error: Option<String>,
}

impl Once {
    fn failed(parse_s: f64, error: String) -> Once {
        Once { parse_s, tokens: None, tokens_sha256: None, compressed: None, encode_s: None, error: Some(error) }
    }
}

impl Method {
    /// `name=<crate-dir>`, where the crate is one the driver generated from
    /// `validator/measure/candidate/`.
    pub fn slot(name: &str, crate_dir: &Path) -> Result<Method, String> {
        let lib = crate_dir.join(LIB_IN_CRATE);
        let source = crate_dir.join(SOURCE_IN_CRATE);
        let read = |p: &Path| std::fs::read(p).map_err(|e| format!("read {}: {e}", p.display()));
        let source_sha256 = crate::record::sha256_hex(&read(&source)?);
        let lib_sha256 = crate::record::sha256_hex(&read(&lib)?);
        Ok(Method {
            name: name.to_string(),
            kind: Kind::Slot(Parser::load(&lib)?),
            crate_dir: Some(crate_dir.to_path_buf()),
            source_sha256: Some(source_sha256),
            lib_sha256: Some(lib_sha256),
        })
    }

    pub fn external(name: &str, kind: Kind) -> Method {
        Method { name: name.to_string(), kind, crate_dir: None, source_sha256: None, lib_sha256: None }
    }

    pub fn is_external(&self) -> bool {
        !matches!(self.kind, Kind::Slot(_))
    }

    pub fn meta(&self) -> MethodMeta {
        MethodMeta {
            external: self.is_external(),
            crate_dir: self.crate_dir.as_ref().map(|p| p.display().to_string()),
            source_sha256: self.source_sha256.clone(),
            lib_sha256: self.lib_sha256.clone(),
        }
    }

    /// `encode` asks for the compressed output as well; the timed part is the same either way.
    pub fn run_once(&self, input: &[u8], toks: &mut [u32], encode: bool) -> Once {
        match &self.kind {
            Kind::Slot(p) => {
                let t0 = Instant::now();
                let n = p.parse(input, toks);
                let parse_s = t0.elapsed().as_secs_f64();
                if n == PANICKED {
                    return Once::failed(parse_s, "parse panicked".to_string());
                }
                if n > toks.len() {
                    return Once::failed(
                        parse_s,
                        format!("parse reported {n} tokens into a buffer of {}", toks.len()),
                    );
                }
                let tokens_sha256 = sha256_tokens(&toks[..n]);
                let (compressed, encode_s) = if encode {
                    let t1 = Instant::now();
                    match deflate::encode(&toks[..n], input.len()) {
                        Ok(v) => (Some(v), Some(t1.elapsed().as_secs_f64())),
                        Err(e) => return Once::failed(parse_s, format!("encode: {e}")),
                    }
                } else {
                    (None, None)
                };
                Once {
                    parse_s,
                    tokens: Some(n as u64),
                    tokens_sha256: Some(tokens_sha256),
                    compressed,
                    encode_s,
                    error: None,
                }
            }
            Kind::MinizOxide(level) => {
                let t0 = Instant::now();
                let out = miniz_oxide::deflate::compress_to_vec(input, *level);
                let parse_s = t0.elapsed().as_secs_f64();
                Once {
                    parse_s,
                    tokens: None,
                    tokens_sha256: None,
                    compressed: encode.then_some(out),
                    encode_s: None,
                    error: None,
                }
            }
            Kind::LibDeflate => {
                let t0 = Instant::now();
                let mut c = libdeflater::Compressor::new(libdeflater::CompressionLvl::best());
                let mut buf = vec![0u8; c.deflate_compress_bound(input.len())];
                let n = match c.deflate_compress(input, &mut buf) {
                    Ok(n) => n,
                    Err(e) => {
                        let parse_s = t0.elapsed().as_secs_f64();
                        return Once::failed(parse_s, format!("libdeflate: {e:?}"));
                    }
                };
                let parse_s = t0.elapsed().as_secs_f64();
                buf.truncate(n);
                Once {
                    parse_s,
                    tokens: None,
                    tokens_sha256: None,
                    compressed: encode.then_some(buf),
                    encode_s: None,
                    error: None,
                }
            }
        }
    }
}

/// Decode with miniz_oxide and the system zlib; agreement between two implementations is evidence.
pub fn check_round_trip(compressed: &[u8], original: &[u8]) -> Result<(), String> {
    match miniz_oxide::inflate::decompress_to_vec(compressed) {
        Ok(got) if got == original => {}
        Ok(got) => {
            return Err(format!(
                "miniz_oxide decoded {} bytes, expected {}",
                got.len(),
                original.len()
            ))
        }
        Err(e) => return Err(format!("miniz_oxide refused the stream: {e:?}")),
    }
    use std::io::Read;
    let mut d = flate2::read::DeflateDecoder::new(compressed);
    let mut got = Vec::new();
    match d.read_to_end(&mut got) {
        Ok(_) if got == original => Ok(()),
        Ok(_) => Err(format!("zlib decoded {} bytes, expected {}", got.len(), original.len())),
        Err(e) => Err(format!("zlib refused the stream: {e}")),
    }
}
