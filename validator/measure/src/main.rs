//! The measurement engine: dlopen N parsers, time them on one corpus, emit raw JSONL.
//!
//!   measure <corpus-dir> <name>=<crate-dir> [<name>=<crate-dir> ...]
//!
//!     --corpus-name LABEL    default: the corpus directory's own name
//!     --reps N               measured rounds per file (default 11)
//!     --warmup N             discarded rounds before them (default 1)
//!     --speed-floor F        recorded in `meta`, never applied here
//!     --rustc-version S      recorded in `meta`; the driver knows what it built with
//!     --no-bars              drop the external reference methods
//!
//! JSONL goes to stdout, one `meta` line then one line per corpus file, flushed
//! as each file finishes. Progress and errors go to stderr. The exit code says
//! whether the measurement ran, never whether a candidate passed.

mod deflate;
mod loader;
mod method;
mod record;
mod token;

use method::{check_round_trip, Kind, Method};
use record::{sha256_hex, FileOut, Meta, MethodMeta, MethodOut, Rep, SCHEMA_VERSION};
use std::collections::BTreeMap;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const USAGE: &str = "usage: measure <corpus-dir> <name>=<crate-dir> [<name>=<crate-dir> ...]";

/// Anything that stops the measurement from happening at all.
fn fail(msg: impl AsRef<str>) -> ExitCode {
    eprintln!("measure: {}", msg.as_ref());
    ExitCode::from(2)
}

struct Args {
    corpus_dir: PathBuf,
    corpus_name: String,
    reps: usize,
    warmup: usize,
    speed_floor: Option<f64>,
    rustc_version: Option<String>,
    bars: bool,
    methods: Vec<(String, PathBuf)>,
}

fn parse_args() -> Result<Args, String> {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut positional: Vec<String> = Vec::new();
    let (mut corpus_name, mut rustc_version, mut speed_floor) = (None, None, None);
    let (mut reps, mut warmup, mut bars) = (11usize, 1usize, true);

    let mut i = 0;
    while i < argv.len() {
        let a = &argv[i];
        let mut value = |what: &str| -> Result<String, String> {
            i += 1;
            argv.get(i).cloned().ok_or_else(|| format!("{what} needs a value"))
        };
        match a.as_str() {
            "--corpus-name" => corpus_name = Some(value("--corpus-name")?),
            "--rustc-version" => rustc_version = Some(value("--rustc-version")?),
            "--speed-floor" => {
                let v = value("--speed-floor")?;
                speed_floor = Some(v.parse().map_err(|_| format!("--speed-floor {v} is not a number"))?);
            }
            "--reps" => {
                let v = value("--reps")?;
                reps = v.parse().map_err(|_| format!("--reps {v} is not a number"))?;
            }
            "--warmup" => {
                let v = value("--warmup")?;
                warmup = v.parse().map_err(|_| format!("--warmup {v} is not a number"))?;
            }
            "--no-bars" => bars = false,
            "-h" | "--help" => return Err(USAGE.to_string()),
            _ if a.starts_with("--") => return Err(format!("unknown flag {a}")),
            _ => positional.push(a.clone()),
        }
        i += 1;
    }

    if reps < 1 {
        return Err("--reps must be at least 1".to_string());
    }
    if positional.len() < 2 {
        return Err(USAGE.to_string());
    }
    let corpus_dir = PathBuf::from(&positional[0]);
    let mut methods: Vec<(String, PathBuf)> = Vec::new();
    for spec in &positional[1..] {
        let (name, dir) = spec.split_once('=').ok_or_else(|| format!("{spec} is not name=<crate-dir>"))?;
        if name.is_empty() {
            return Err(format!("{spec} has an empty method name"));
        }
        if methods.iter().any(|(n, _)| n == name) {
            return Err(format!("method {name} given twice"));
        }
        methods.push((name.to_string(), PathBuf::from(dir)));
    }
    let corpus_name = corpus_name.unwrap_or_else(|| {
        corpus_dir.file_name().unwrap_or_default().to_string_lossy().to_string()
    });
    Ok(Args { corpus_dir, corpus_name, reps, warmup, speed_floor, rustc_version, bars, methods })
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

fn read_trimmed(path: &str) -> Option<String> {
    std::fs::read_to_string(path).ok().map(|s| s.trim().to_string())
}

fn cpu_model() -> Option<String> {
    let s = std::fs::read_to_string("/proc/cpuinfo").ok()?;
    s.lines()
        .find(|l| l.starts_with("model name"))
        .and_then(|l| l.split(':').nth(1))
        .map(|s| s.trim().to_string())
}

fn now_unix() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs_f64())
        .unwrap_or(0.0)
}

fn bench_file(
    corpus: &str,
    path: &Path,
    methods: &[Method],
    warmup: usize,
    reps: usize,
    order: &mut u64,
    out: &mut impl Write,
) -> std::io::Result<()> {
    let input = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("skipping {}: {e}", path.display());
            return Ok(());
        }
    };
    if input.is_empty() {
        return Ok(());
    }
    let name = path.file_name().unwrap_or_default().to_string_lossy().to_string();
    eprintln!("{corpus}/{name} ({} bytes)", input.len());

    let mut toks = vec![0u32; input.len()];
    let mut built: BTreeMap<String, MethodOut> = BTreeMap::new();

    for round in 0..(warmup + reps) {
        let phase = if round < warmup { "warmup" } else { "measured" };
        for m in methods {
            let first = !built.contains_key(&m.name);
            if !first && !built[&m.name].errors.is_empty() {
                continue;
            }
            let once = m.run_once(&input, &mut toks, first);
            *order += 1;

            let entry = built.entry(m.name.clone()).or_insert_with(|| MethodOut {
                external: m.is_external(),
                output_bytes: None,
                output_sha256: None,
                tokens: None,
                tokens_sha256: None,
                deterministic: true,
                encode_s: None,
                errors: Vec::new(),
                reps: Vec::new(),
            });
            entry.reps.push(Rep {
                phase,
                order_index: *order,
                time_s: once.parse_s,
                encode_s: once.encode_s,
                total_s: once.error.is_none().then_some(once.parse_s + once.encode_s.unwrap_or(0.0)),
            });

            if let Some(e) = &once.error {
                eprintln!("  {}: {e}", m.name);
                entry.errors.push(e.clone());
                continue;
            }
            if first {
                entry.tokens = once.tokens;
                entry.tokens_sha256 = once.tokens_sha256.clone();
                entry.encode_s = once.encode_s;
                if let Some(c) = &once.compressed {
                    entry.output_bytes = Some(c.len() as u64);
                    entry.output_sha256 = Some(sha256_hex(c));
                    if let Err(e) = check_round_trip(c, &input) {
                        eprintln!("  {}: round trip: {e}", m.name);
                        entry.errors.push(format!("round trip: {e}"));
                    }
                }
            } else if entry.tokens_sha256.is_some()
                && entry.tokens_sha256 != once.tokens_sha256
                && entry.deterministic
            {
                entry.deterministic = false;
                eprintln!("  {}: NON-DETERMINISTIC in round {round}", m.name);
            }
        }
    }

    let rec = FileOut {
        kind: "file",
        corpus: corpus.to_string(),
        file: name,
        raw_bytes: input.len() as u64,
        sha256: sha256_hex(&input),
        methods: built,
    };
    serde_json::to_writer(&mut *out, &rec)?;
    out.write_all(b"\n")?;
    out.flush()
}

fn run() -> Result<(), String> {
    let args = parse_args()?;

    let files = match corpus_files(&args.corpus_dir) {
        Ok(f) if !f.is_empty() => f,
        Ok(_) => return Err(format!("no files in {}", args.corpus_dir.display())),
        Err(e) => return Err(format!("cannot read {}: {e}", args.corpus_dir.display())),
    };

    let mut methods: Vec<Method> = Vec::new();
    for (name, dir) in &args.methods {
        methods.push(Method::slot(name, dir)?);
    }
    if args.bars {
        methods.push(Method::external("miniz_oxide-1", Kind::MinizOxide(1)));
        methods.push(Method::external("miniz_oxide-9", Kind::MinizOxide(9)));
        methods.push(Method::external("libdeflate-12", Kind::LibDeflate));
    }

    let meta = Meta {
        kind: "meta",
        schema_version: SCHEMA_VERSION,
        started_at_unix: now_unix(),
        corpus: args.corpus_name.clone(),
        corpus_dir: args.corpus_dir.display().to_string(),
        os: std::env::consts::OS,
        arch: std::env::consts::ARCH,
        rustc_version: args.rustc_version.clone(),
        cpu_model: cpu_model(),
        cpu_governor: read_trimmed("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"),
        warmup_rounds: args.warmup,
        measured_rounds: args.reps,
        speed_floor: args.speed_floor,
        methods: methods.iter().map(|m| (m.name.clone(), m.meta())).collect::<BTreeMap<String, MethodMeta>>(),
    };

    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    serde_json::to_writer(&mut out, &meta).map_err(|e| e.to_string())?;
    out.write_all(b"\n").and_then(|()| out.flush()).map_err(|e| e.to_string())?;

    let mut order = 0u64;
    for f in &files {
        bench_file(&args.corpus_name, f, &methods, args.warmup, args.reps, &mut order, &mut out)
            .map_err(|e| format!("writing results: {e}"))?;
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => fail(e),
    }
}
