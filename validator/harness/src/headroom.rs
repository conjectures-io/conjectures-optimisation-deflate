//! `harness <corpus> --headroom` — where the gap to `libdeflate` actually is.
//!
//! The competition advertises the distance between the best accepted submission
//! and `libdeflate` level 12 as the prize. Most of that number is honest and part
//! of it is not, because the gap has three components and **a miner can only
//! reach one of them**:
//!
//! * the **parse** — the slot. Reachable.
//! * **block splitting** — `deflate.rs` cuts a block every `BLOCK_TOKENS` tokens,
//!   identically for everyone. Not reachable.
//! * the **entropy coder** — trusted, pinned, identical for everyone. Not
//!   reachable.
//!
//! This module measures the split rather than arguing about it. The reference
//! parsers in [`crate::reference`] emit the competition's own token encoding and
//! are scored through the *same* `deflate::encode`, so whatever they reach is by
//! construction reachable through the slot: it is a parse and nothing else
//! changed. What they cannot close is what lives in the harness.
//!
//! Every arm's output is put through the same differential round-trip check the
//! scoring path uses, against both independent inflaters. A reference parser is
//! ordinary unproved code, so a bug in it would silently corrupt the one number
//! this module exists to produce.
//!
//! The numbers are a *demonstrated* floor, not a theorem. A better parser than
//! the one here would move bytes from the unreachable column into the reachable
//! one, which is the direction that helps a miner.

use crate::deflate;
use crate::reference;
use std::path::Path;
use std::time::{Duration, Instant};

/// Chain depth for the greedy and lazy reference parsers. Far past the point of
/// diminishing returns; these are not competing on speed.
const REF_DEPTH: usize = 256;

/// Chain depth for the shortest-path parse. Lower, because it queries *every*
/// position rather than every match, and the cost model matters more than the
/// candidate count at this point.
const OPT_DEPTH: usize = 48;

/// Shortest-path passes. Each one re-costs from the previous pass's frequencies;
/// the third rarely moves the number.
const OPT_ITERS: usize = 4;

/// Block sizes swept to price the harness's fixed choice. `usize::MAX` is "one
/// block for the whole file".
const BLOCK_SWEEP: [usize; 8] = [1024, 2048, 4096, 8192, 16384, 32768, 65536, usize::MAX];

struct Arm {
    label: &'static str,
    bytes: u64,
    time: Duration,
}

fn run_parse(
    label: &'static str,
    parse: impl Fn(&[u8]) -> Vec<u32>,
    input: &[u8],
) -> Result<(Arm, Vec<u32>), String> {
    let t0 = Instant::now();
    let toks = parse(input);
    let time = t0.elapsed();
    let out = deflate::encode(&toks, input.len())?;
    // `encode` rejects a *malformed* stream — a distance reaching before the
    // start, a length out of range. It cannot reject a stream that is well formed
    // and simply wrong: a match whose bytes do not actually match encodes fine and
    // decodes to different bytes. So every arm goes through the same differential
    // round-trip check the scoring path uses. A headroom number produced by a
    // buggy reference parser would be worse than no number at all.
    crate::check_round_trip(&out, input).map_err(|e| format!("round trip: {e}"))?;
    Ok((Arm { label, bytes: out.len() as u64, time }, toks))
}

pub fn report(dir: &Path, files: &[std::path::PathBuf]) -> i32 {
    let mut arms: Vec<Arm> = vec![
        Arm { label: "incumbent (harness/src/baseline.rs)", bytes: 0, time: Duration::ZERO },
        Arm { label: "submission (slot/src/parse.rs)", bytes: 0, time: Duration::ZERO },
        Arm { label: "reference: greedy, depth 256", bytes: 0, time: Duration::ZERO },
        Arm { label: "reference: lazy matching, depth 256", bytes: 0, time: Duration::ZERO },
        Arm { label: "reference: near-optimal parse", bytes: 0, time: Duration::ZERO },
    ];
    let mut ld_bytes = 0u64;
    let mut best_block_bytes = 0u64;
    let mut raw = 0u64;
    let mut block_choice: Vec<(String, usize)> = Vec::new();
    let mut errors: Vec<String> = Vec::new();

    println!("measuring the headroom decomposition over {}", dir.display());
    println!("  reference depths: greedy/lazy {REF_DEPTH}, shortest-path {OPT_DEPTH} x {OPT_ITERS} passes");
    println!("  this is a measurement tool, not the gate — it is slow on purpose");
    println!("  the `submission` arm is whatever is in slot/src/parse.rs right now\n");

    for f in files {
        let input = match std::fs::read(f) {
            Ok(b) if !b.is_empty() => b,
            Ok(_) => continue,
            Err(e) => {
                errors.push(format!("{}: {e}", f.display()));
                continue;
            }
        };
        raw += input.len() as u64;
        let name = f.file_name().unwrap_or_default().to_string_lossy().to_string();
        print!("  {name} … ");
        use std::io::Write;
        let _ = std::io::stdout().flush();

        let results = [
            run_parse(arms[0].label, |b| {
                let mut t = vec![0u32; b.len().max(1)];
                let n = crate::baseline::parse(b, &mut t);
                t.truncate(n);
                t
            }, &input),
            run_parse(arms[1].label, |b| {
                let mut t = vec![0u32; b.len().max(1)];
                let n = slot::parse::parse(b, &mut t);
                t.truncate(n);
                t
            }, &input),
            run_parse(arms[2].label, |b| reference::greedy(b, REF_DEPTH), &input),
            run_parse(arms[3].label, |b| reference::lazy(b, REF_DEPTH), &input),
            run_parse(arms[4].label, |b| reference::optimal(b, OPT_DEPTH, OPT_ITERS), &input),
        ];

        let mut opt_toks: Option<Vec<u32>> = None;
        for (i, r) in results.into_iter().enumerate() {
            match r {
                Ok((a, toks)) => {
                    arms[i].bytes += a.bytes;
                    arms[i].time += a.time;
                    if i == 4 {
                        opt_toks = Some(toks);
                    }
                }
                Err(e) => errors.push(format!("{name}: {}: {e}", arms[i].label)),
            }
        }

        // What the harness's fixed block size costs: the same near-optimal token
        // stream through the same encoder, block size swept.
        if let Some(toks) = opt_toks {
            let mut best = (u64::MAX, 0usize);
            for &bt in &BLOCK_SWEEP {
                if let Ok(v) = deflate::encode_with_block_tokens(&toks, input.len(), bt) {
                    if crate::check_round_trip(&v, &input).is_err() {
                        errors.push(format!("{name}: block size {bt} does not round trip"));
                        continue;
                    }
                    if (v.len() as u64) < best.0 {
                        best = (v.len() as u64, bt);
                    }
                }
            }
            if best.0 != u64::MAX {
                best_block_bytes += best.0;
                block_choice.push((name.clone(), best.1));
            }
        }

        let mut c = libdeflater::Compressor::new(libdeflater::CompressionLvl::best());
        let mut buf = vec![0u8; c.deflate_compress_bound(input.len())];
        ld_bytes += c.deflate_compress(&input, &mut buf).unwrap_or(buf.len()) as u64;

        println!("done");
    }

    if !errors.is_empty() {
        println!("\nerrors:");
        for e in &errors {
            println!("  {e}");
        }
        return 1;
    }

    let incumbent = arms[0].bytes.max(1);
    let mib = raw as f64 / (1024.0 * 1024.0);

    println!("\n{:<40} {:>10} {:>9} {:>12}", "arm", "bytes", "vs inc.", "ms/MiB");
    println!("{}", "-".repeat(75));
    for a in &arms {
        println!(
            "{:<40} {:>10} {:>8.3}x {:>12.1}",
            a.label,
            a.bytes,
            a.bytes as f64 / incumbent as f64,
            a.time.as_secs_f64() * 1000.0 / mib.max(1e-9)
        );
    }
    println!(
        "{:<40} {:>10} {:>8.3}x {:>12}",
        "libdeflate level 12 (whole compressor)",
        ld_bytes,
        ld_bytes as f64 / incumbent as f64,
        "—"
    );
    println!("{}", "-".repeat(75));

    // ------------------------------------------------------------------
    // The decomposition
    // ------------------------------------------------------------------
    let s = arms[1].bytes; // the accepted submission
    let r = arms[4].bytes; // near-optimal parse, harness block size
    let b = best_block_bytes; // near-optimal parse, best fixed block size
    let l = ld_bytes;

    let gap = s as i64 - l as i64;
    let parse_part = s as i64 - r as i64;
    let block_part = r as i64 - b as i64;
    let residual = b as i64 - l as i64;

    let pct = |x: i64| -> f64 {
        if gap == 0 { 0.0 } else { x as f64 * 100.0 / gap as f64 }
    };
    let of_inc = |x: i64| -> f64 { x as f64 * 100.0 / incumbent as f64 };

    println!("\nthe gap between the accepted submission and libdeflate is {gap} bytes");
    println!("({:.2}% of the incumbent). It decomposes as:\n", of_inc(gap));
    println!("{:<44} {:>10} {:>8} {:>9}", "", "bytes", "of gap", "of inc.");
    println!("{}", "-".repeat(75));
    println!(
        "{:<44} {:>10} {:>7.1}% {:>8.2}%   REACHABLE",
        "a better parse — this is the slot", parse_part, pct(parse_part), of_inc(parse_part)
    );
    println!(
        "{:<44} {:>10} {:>7.1}% {:>8.2}%   not in the slot",
        "block splitting — harness, fixed for all", block_part, pct(block_part), of_inc(block_part)
    );
    println!(
        "{:<44} {:>10} {:>7.1}% {:>8.2}%   not in the slot",
        "entropy coder + residual — harness", residual, pct(residual), of_inc(residual)
    );
    println!("{}", "-".repeat(75));

    println!("\nHow to read this:");
    println!("  * REACHABLE is what a miner can win by proving a better parse, and it is a");
    println!("    demonstrated floor, not an estimate: the parse that reaches it is in this");
    println!("    repository (harness/src/reference.rs), it emits the competition's own");
    println!("    tokens, it goes through the same trusted encoder, and its output is");
    println!("    round-tripped against both inflaters like any scored submission.");
    println!("  * The other two rows need a SECOND SLOT with its own contract. No");
    println!("    submission to the LZ77 slot can touch them. See docs/ROADMAP.md.");
    println!("  * The block-splitting row is a lower bound: it prices only the best");
    println!("    *fixed* block size, and a real splitter cuts on content. Per file the");
    println!("    best fixed size was:");
    for (name, bt) in &block_choice {
        let shown = if *bt == usize::MAX { "whole file".to_string() } else { bt.to_string() };
        println!("      {name:<28} {shown}");
    }
    println!("  * The residual row is what libdeflate does that neither a better parse");
    println!("    nor a better block size explains. A negative number there means this");
    println!("    repository's encoder is already ahead of libdeflate's on that axis.");

    println!("\nSpeed, for calibrating the budget in main.rs:");
    println!(
        "  the near-optimal reference parse costs {:.1} ms/MiB",
        arms[4].time.as_secs_f64() * 1000.0 / mib.max(1e-9)
    );
    println!(
        "  the incumbent costs {:.1} ms/MiB, the submission {:.1} ms/MiB",
        arms[0].time.as_secs_f64() * 1000.0 / mib.max(1e-9),
        arms[1].time.as_secs_f64() * 1000.0 / mib.max(1e-9)
    );
    0
}
