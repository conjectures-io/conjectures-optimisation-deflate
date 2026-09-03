//! The scoring harness.
//!
//! ```text
//!   corpus file ──► parse (the slot) ──► tokens ──► deflate.rs ──► bytes
//!                                                       │
//!                        independent inflate ◄───────────┘   (round-trip check)
//! ```
//!
//! The score is **total compressed bytes over the corpus, lower wins**. It is an
//! exact integer: two validators on different machines compute the *same* number,
//! which is the property the previous project did not have and the reason its
//! scoring was fragile. Wall clock appears only as a coarse floor gate, where
//! ±10% noise is harmless.
//!
//! The round-trip check is empirical and the proof is what generalises it. Both
//! are here on purpose: the harness must stay memory-safe and terminating even if
//! the proof were unsound, and a differential check that disagrees with an
//! accepted proof is evidence of a bug in the *contract*, which is exactly the
//! failure worth catching loudly.

mod baseline;
mod deflate;
mod token;

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

/// A submission may not be slower than this multiple of the incumbent. Loose on
/// purpose: a tight floor puts SIMD back on the critical path, and SIMD is
/// outside the provable subset. See `docs/EXP1_HEADROOM.md`.
const SPEED_FLOOR: f64 = 8.0;

struct Run {
    bytes: u64,
    time: Duration,
}

fn parse_and_encode(
    parse: impl Fn(&[u8], &mut [u32]) -> usize,
    input: &[u8],
) -> Result<(Vec<u8>, Duration), String> {
    let mut toks = vec![0u32; input.len().max(1)];
    let t0 = Instant::now();
    let n = parse(input, &mut toks);
    let elapsed = t0.elapsed();
    if n > toks.len() {
        return Err(format!("parse reported {n} tokens into a buffer of {}", toks.len()));
    }
    let out = deflate::encode(&toks[..n], input.len())?;
    Ok((out, elapsed))
}

/// Two independent decoders. `miniz_oxide` is the crate the competition is aimed
/// at; the system zlib behind `flate2` is a different implementation entirely, so
/// agreement between them is real evidence rather than a shared bug.
fn check_round_trip(compressed: &[u8], original: &[u8]) -> Result<(), String> {
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

fn reference_bars(input: &[u8]) -> (u64, u64, u64) {
    let mo1 = miniz_oxide::deflate::compress_to_vec(input, 1).len() as u64;
    let mo9 = miniz_oxide::deflate::compress_to_vec(input, 9).len() as u64;
    let mut c = libdeflater::Compressor::new(libdeflater::CompressionLvl::best());
    let mut buf = vec![0u8; c.deflate_compress_bound(input.len())];
    let ld = c.deflate_compress(input, &mut buf).unwrap_or(buf.len()) as u64;
    (mo1, mo9, ld)
}

fn corpus_files(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)?
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_file())
        .collect();
    v.sort();
    Ok(v)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = PathBuf::from(args.get(1).cloned().unwrap_or_else(|| "../corpus".into()));

    let files = match corpus_files(&dir) {
        Ok(f) if !f.is_empty() => f,
        Ok(_) => {
            eprintln!("no files in {}; run `just corpus` first", dir.display());
            std::process::exit(2);
        }
        Err(e) => {
            eprintln!("cannot read {}: {e}", dir.display());
            std::process::exit(2);
        }
    };

    let mut base = Run { bytes: 0, time: Duration::ZERO };
    let mut cand = Run { bytes: 0, time: Duration::ZERO };
    let (mut raw, mut b_mo1, mut b_mo9, mut b_ld) = (0u64, 0u64, 0u64, 0u64);
    let mut failures = Vec::new();

    println!("{:<26} {:>10} {:>11} {:>11} {:>8}", "file", "raw", "incumbent", "submission", "delta");
    println!("{}", "-".repeat(70));

    for f in &files {
        let input = match std::fs::read(f) {
            Ok(b) => b,
            Err(e) => {
                eprintln!("skipping {}: {e}", f.display());
                continue;
            }
        };
        if input.is_empty() {
            continue;
        }
        raw += input.len() as u64;

        let (bo, bt) = match parse_and_encode(baseline::parse, &input) {
            Ok(x) => x,
            Err(e) => {
                failures.push(format!("{}: incumbent: {e}", f.display()));
                continue;
            }
        };
        let (co, ct) = match parse_and_encode(slot::parse::parse, &input) {
            Ok(x) => x,
            Err(e) => {
                failures.push(format!("{}: SUBMISSION: {e}", f.display()));
                continue;
            }
        };
        if let Err(e) = check_round_trip(&bo, &input) {
            failures.push(format!("{}: incumbent round trip: {e}", f.display()));
        }
        if let Err(e) = check_round_trip(&co, &input) {
            failures.push(format!("{}: SUBMISSION round trip: {e}", f.display()));
        }

        let (m1, m9, ld) = reference_bars(&input);
        b_mo1 += m1;
        b_mo9 += m9;
        b_ld += ld;

        base.bytes += bo.len() as u64;
        base.time += bt;
        cand.bytes += co.len() as u64;
        cand.time += ct;

        let name = f.file_name().unwrap_or_default().to_string_lossy();
        let delta = co.len() as f64 / bo.len().max(1) as f64;
        println!(
            "{:<26} {:>10} {:>11} {:>11} {:>7.3}x",
            if name.len() > 26 { &name[..26] } else { &name },
            input.len(),
            bo.len(),
            co.len(),
            delta
        );
    }

    println!("{}", "-".repeat(70));
    println!("{:<26} {:>10} {:>11} {:>11}", "TOTAL", raw, base.bytes, cand.bytes);
    println!();
    println!("Reference bars on the same corpus (context only, not the score):");
    println!("  miniz_oxide level 1      {b_mo1:>11}");
    println!("  miniz_oxide level 9      {b_mo9:>11}");
    println!("  libdeflate level 12      {b_ld:>11}   <- the state of the art");
    println!();

    let ratio = cand.bytes as f64 / base.bytes.max(1) as f64;
    let slowdown = cand.time.as_secs_f64() / base.time.as_secs_f64().max(1e-9);
    println!("score      {:.5}x of the incumbent's bytes  ({} vs {})",
        ratio, cand.bytes, base.bytes);
    println!("parse time {:.3}s incumbent, {:.3}s submission ({:.2}x)",
        base.time.as_secs_f64(), cand.time.as_secs_f64(), slowdown);
    println!();

    if !failures.is_empty() {
        println!("REJECTED — {} correctness failure(s):", failures.len());
        for f in failures.iter().take(20) {
            println!("  {f}");
        }
        std::process::exit(1);
    }
    if slowdown > SPEED_FLOOR {
        println!("REJECTED — {slowdown:.2}x slower than the incumbent, floor is {SPEED_FLOOR:.1}x");
        std::process::exit(1);
    }
    if ratio < 1.0 {
        println!("ACCEPTED — {:.3}% smaller than the incumbent.", (1.0 - ratio) * 100.0);
    } else if ratio > 1.0 {
        println!("no improvement — {:.3}% larger than the incumbent.", (ratio - 1.0) * 100.0);
    } else {
        println!("no change — byte-identical to the incumbent.");
    }
}
