//! `arena`: build parsers, benchmark them against existing DEFLATE
//! implementations in several framings, and compress files with them.
//!
//! ```text
//! arena build  --validator DIR --work DIR PARSE.rs...
//! arena bench  --corpus DIR [--label NAME] --method M... [--mode MODE] [--huffman pinned|fast]
//!              [--blocks fixed|adaptive] [--container raw|zlib|gzip] [--reps N] [--warmup N] [--out FILE.jsonl] [--validator DIR --work DIR]
//! arena gz     --method M [--mode MODE] [--format gzip|zlib|raw|bgzf] [--huffman ...] IN OUT
//! ```
//!
//! A method is `slot:NAME=PATH` (a `parse.rs`, built as the gate builds it, or a
//! built `libcandidate.so`), `slot-nochk:NAME=PATH` (the same without overflow
//! checks, which an accepted proof makes redundant), `builtin:NAME` (a linked-in reference example),
//! `ref:SPEC` (`zlib-6`, `libdeflate-12`, `miniz_oxide-9`, `zopfli-i15`), or
//! `retok:SPEC`: that reference's parse, decoded back to tokens and re-encoded
//! with the shared encoder (sizes only), for parse-versus-encoder comparisons.
//!
//! A mode is `whole` (one call, the competition's setting), `stream:CHUNK` or
//! `stream:CHUNK:FLUSH` (32 KiB history carried across chunks, optional sync
//! flush every FLUSH input bytes), `indep:CHUNK` (chunks with no history, one
//! raw stream each), `bgzf` (BGZF blocks, sizes include the framing),
//! `messages[:WBITS]` (one message per line, a sync flush after each, a
//! 2^WBITS-byte window), or `png` (recompress each PNG's IDAT, filters kept).
//! Sizes accept `k`/`m` suffixes (KiB/MiB).

use deflate_arena::encoder::{self, Blocks, Coding, Huffman};
use deflate_arena::parser::{self, FnParser, Parser, SlotParser};
use deflate_arena::reference::{self, Reference};
use deflate_arena::stream::{self, StreamConfig};
use deflate_arena::{builtin, container, inflate_tokens, png, verify};
use serde::Serialize;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

const STREAM_WRITE: usize = 64 * 1024;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let res = match args.first().map(String::as_str) {
        Some("build") => cmd_build(&args[1..]),
        Some("bench") => cmd_bench(&args[1..]),
        Some("gz") => cmd_gz(&args[1..]),
        _ => Err("usage: arena build|bench|gz ... (see the module docs in src/bin/arena.rs)".to_string()),
    };
    if let Err(e) = res {
        eprintln!("arena: {e}");
        std::process::exit(1);
    }
}

// ── Arguments ─────────────────────────────────────────────────────────────────

struct Args {
    flags: BTreeMap<String, Vec<String>>,
    positional: Vec<String>,
}

impl Args {
    fn parse(args: &[String], valued: &[&str]) -> Result<Args, String> {
        let mut flags: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut positional = Vec::new();
        let mut i = 0;
        while i < args.len() {
            let a = &args[i];
            if let Some(name) = a.strip_prefix("--") {
                if valued.contains(&name) {
                    let v = args.get(i + 1).ok_or(format!("--{name} needs a value"))?;
                    flags.entry(name.to_string()).or_default().push(v.clone());
                    i += 2;
                    continue;
                }
                return Err(format!("unknown flag --{name}"));
            }
            positional.push(a.clone());
            i += 1;
        }
        Ok(Args { flags, positional })
    }

    fn one(&self, name: &str) -> Option<&str> {
        self.flags.get(name).and_then(|v| v.last()).map(String::as_str)
    }

    fn all(&self, name: &str) -> &[String] {
        self.flags.get(name).map(Vec::as_slice).unwrap_or(&[])
    }
}

fn size(s: &str) -> Result<usize, String> {
    let (num, mul) = match s.as_bytes().last() {
        Some(b'k') | Some(b'K') => (&s[..s.len() - 1], 1024),
        Some(b'm') | Some(b'M') => (&s[..s.len() - 1], 1024 * 1024),
        _ => (s, 1),
    };
    num.parse::<usize>().map(|n| n * mul).map_err(|_| format!("bad size {s}"))
}

#[derive(Clone, Copy, Debug)]
enum Mode {
    Whole,
    Stream { chunk: usize, flush: Option<usize> },
    Indep { chunk: usize },
    Bgzf,
    /// Newline-separated messages, a sync flush after each, `window_bits` of history.
    Messages { window_bits: u8 },
    /// Each file is a PNG: recompress its IDAT, filters unchanged; sizes are whole PNGs.
    Png,
}

impl Mode {
    fn parse(s: &str) -> Result<Mode, String> {
        let parts: Vec<&str> = s.split(':').collect();
        match parts.as_slice() {
            ["whole"] => Ok(Mode::Whole),
            ["bgzf"] => Ok(Mode::Bgzf),
            ["stream", c] => Ok(Mode::Stream { chunk: size(c)?, flush: None }),
            ["stream", c, f] => Ok(Mode::Stream { chunk: size(c)?, flush: Some(size(f)?) }),
            ["indep", c] => Ok(Mode::Indep { chunk: size(c)? }),
            ["messages"] => Ok(Mode::Messages { window_bits: 15 }),
            ["messages", w] => match w.parse::<u8>() {
                Ok(w) if (8..=15).contains(&w) => Ok(Mode::Messages { window_bits: w }),
                _ => Err(format!("bad window bits {w}")),
            },
            ["png"] => Ok(Mode::Png),
            _ => Err(format!("bad mode {s}")),
        }
    }
}

fn coding(a: &Args) -> Result<Coding, String> {
    let huffman = match a.one("huffman").unwrap_or("fast") {
        "fast" => Huffman::Fast,
        "pinned" => Huffman::Pinned,
        h => return Err(format!("bad --huffman {h}")),
    };
    let blocks = match a.one("blocks").unwrap_or("fixed") {
        "fixed" => Blocks::Fixed,
        "adaptive" => Blocks::Adaptive,
        b => return Err(format!("bad --blocks {b}")),
    };
    Ok(Coding { huffman, blocks })
}

// ── Methods ───────────────────────────────────────────────────────────────────

enum Kind {
    Slot(SlotParser),
    Builtin(FnParser),
    Ref(Reference),
    Retok(Reference),
}

struct Method {
    name: String,
    kind: Kind,
    source_sha256: Option<String>,
}

impl Method {
    fn parser(&self) -> Option<&dyn Parser> {
        match &self.kind {
            Kind::Slot(p) => Some(p),
            Kind::Builtin(p) => Some(p),
            _ => None,
        }
    }
}

fn load_method(spec: &str, validator: Option<&Path>, work: Option<&Path>) -> Result<Method, String> {
    let (kind, rest) = spec.split_once(':').ok_or(format!("bad method {spec}"))?;
    match kind {
        "slot" | "slot-nochk" => {
            let profile = if kind == "slot" { parser::Profile::Gate } else { parser::Profile::NoOverflowChecks };
            let (name, path) = rest.split_once('=').ok_or(format!("slot needs NAME=PATH: {spec}"))?;
            let path = PathBuf::from(path);
            let (lib, sha) = if path.extension().is_some_and(|e| e == "so") {
                (path.clone(), parser::sha256_hex(&std::fs::read(&path).map_err(|e| e.to_string())?))
            } else {
                let v = validator.ok_or("--validator is needed to build a parse.rs")?;
                let w = work.ok_or("--work is needed to build a parse.rs")?;
                parser::build_slot_with(v, &path, w, profile)?
            };
            let p = SlotParser::load(name, &lib, sha.clone())?;
            Ok(Method { name: name.to_string(), kind: Kind::Slot(p), source_sha256: Some(sha) })
        }
        "builtin" => {
            let p = builtin::by_name(rest).ok_or(format!("no builtin parser {rest}"))?;
            Ok(Method { name: format!("builtin-{rest}"), kind: Kind::Builtin(p), source_sha256: None })
        }
        "ref" => {
            let r = Reference::parse(rest).ok_or(format!("bad or unloadable reference {rest}"))?;
            let sha = match &r {
                Reference::So(api, _) => Some(format!("zlib {}", api.version)),
                _ => None,
            };
            Ok(Method { name: r.name(), kind: Kind::Ref(r), source_sha256: sha })
        }
        "retok" => {
            let r = Reference::parse(rest).ok_or(format!("bad reference {rest}"))?;
            Ok(Method { name: format!("retok-{}", r.name()), kind: Kind::Retok(r), source_sha256: None })
        }
        _ => Err(format!("bad method kind {kind}")),
    }
}

/// One compression of `data`: the output, its size, and where the time went.
struct Run {
    out: Vec<Vec<u8>>,
    bytes: u64,
    total_s: f64,
    parse_s: Option<f64>,
    encode_s: Option<f64>,
    parsed_bytes: Option<u64>,
}

fn compress(m: &Method, data: &[u8], mode: Mode, h: Coding) -> Result<Run, String> {
    if let Mode::Png = mode {
        let img = png::parse(data)?;
        let scan = img.scanlines()?;
        let mut run = compress(m, &scan, Mode::Whole, h)?;
        let out = img.with_idat(&container::zlib(&run.out[0], &scan));
        run.bytes = out.len() as u64;
        run.out = vec![out];
        return Ok(run);
    }
    let t0 = Instant::now();
    let (out, st) = match (&m.kind, mode) {
        (Kind::Retok(r), Mode::Whole) => {
            let theirs = r.compress(data)?;
            let d = inflate_tokens::decode(&theirs)?;
            (vec![encoder::encode_with(&d.tokens, data.len(), h.huffman, h.blocks)?], None)
        }
        (Kind::Retok(_), _) => return Err("retok is whole-buffer only".to_string()),
        (Kind::Ref(r), Mode::Whole) => (vec![r.compress(data)?], None),
        (Kind::Ref(Reference::Zlib(l)), Mode::Stream { flush, .. }) => {
            (vec![reference::zlib_stream(data, *l, STREAM_WRITE, flush)?], None)
        }
        (Kind::Ref(Reference::So(api, l)), Mode::Stream { flush, .. }) => {
            let pieces: Vec<&[u8]> = match flush {
                Some(every) => data.chunks(every).collect(),
                None => data.chunks(STREAM_WRITE).collect(),
            };
            (vec![api.compress(&pieces, *l, 15, flush.is_some())?], None)
        }
        (Kind::Ref(r), Mode::Stream { .. }) => return Err(format!("{} has no streaming mode here", r.name())),
        (Kind::Ref(r), Mode::Indep { chunk }) => {
            let pieces: Vec<&[u8]> = if data.is_empty() { vec![data] } else { data.chunks(chunk).collect() };
            (pieces.iter().map(|p| r.compress(p)).collect::<Result<Vec<_>, _>>()?, None)
        }
        (Kind::Ref(r), Mode::Bgzf) => (vec![container::bgzf(data, |p| r.compress(p))?], None),
        (Kind::Ref(Reference::Zlib(l)), Mode::Messages { window_bits }) => {
            (vec![reference::zlib_messages(&stream::lines(data), *l, window_bits)?], None)
        }
        (Kind::Ref(Reference::So(api, l)), Mode::Messages { window_bits }) => {
            (vec![api.compress(&stream::lines(data), *l, window_bits.max(9) as i32, true)?], None)
        }
        (Kind::Ref(r), Mode::Messages { .. }) => return Err(format!("{} has no streaming mode here", r.name())),
        (_, mode) => {
            let p = m.parser().expect("parser kinds handled here");
            match mode {
                Mode::Whole => {
                    let (o, s) = stream::compress_whole(p, data, h)?;
                    (vec![o], Some(s))
                }
                Mode::Stream { chunk, flush } => {
                    let (o, s) = stream::compress_stream(p, data, StreamConfig::new(chunk, h), STREAM_WRITE, flush)?;
                    (vec![o], Some(s))
                }
                Mode::Indep { chunk } => {
                    let (o, s) = stream::compress_independent(p, data, chunk, h, true)?;
                    (o, Some(s))
                }
                Mode::Messages { window_bits } => {
                    let mut cfg = StreamConfig::new(1 << 20, h);
                    cfg.window = 1usize << window_bits;
                    let (o, s) = stream::compress_messages(p, &stream::lines(data), cfg)?;
                    (vec![o], Some(s))
                }
                Mode::Png => unreachable!("handled above"),
                Mode::Bgzf => {
                    let mut st = stream::Stats::default();
                    let o = container::bgzf(data, |piece| {
                        let (r, s) = stream::compress_whole(p, piece, h)?;
                        st.parse_s += s.parse_s;
                        st.encode_s += s.encode_s;
                        st.parsed_bytes += s.parsed_bytes;
                        Ok(r)
                    })?;
                    (vec![o], Some(st))
                }
            }
        }
    };
    let total_s = t0.elapsed().as_secs_f64();
    let bytes = out.iter().map(|o| o.len() as u64).sum();
    Ok(Run {
        out,
        bytes,
        total_s,
        parse_s: st.as_ref().map(|s| s.parse_s),
        encode_s: st.as_ref().map(|s| s.encode_s),
        parsed_bytes: st.map(|s| s.parsed_bytes),
    })
}

fn check(run: &Run, data: &[u8], mode: Mode) -> Result<(), String> {
    match mode {
        Mode::Whole | Mode::Stream { .. } => verify::raw(&run.out[0], data),
        Mode::Indep { chunk } => {
            let pieces: Vec<&[u8]> = if data.is_empty() { vec![data] } else { data.chunks(chunk).collect() };
            if pieces.len() != run.out.len() {
                return Err(format!("{} members for {} chunks", run.out.len(), pieces.len()));
            }
            pieces.iter().zip(&run.out).try_for_each(|(p, o)| verify::raw(o, p))
        }
        Mode::Bgzf => verify::gzip(&run.out[0], data),
        Mode::Messages { .. } => verify::raw(&run.out[0], data),
        Mode::Png => {
            let want = png::parse(data)?.scanlines()?;
            let got = png::parse(&run.out[0])?;
            verify::zlib(&got.idat, &want)
        }
    }
}

// ── build ─────────────────────────────────────────────────────────────────────

fn cmd_build(args: &[String]) -> Result<(), String> {
    let a = Args::parse(args, &["validator", "work"])?;
    let v = PathBuf::from(a.one("validator").ok_or("--validator DIR")?);
    let w = PathBuf::from(a.one("work").ok_or("--work DIR")?);
    for src in &a.positional {
        let (lib, sha) = parser::build_slot(&v, Path::new(src), &w)?;
        println!("{sha}\t{}\t{src}", lib.display());
    }
    Ok(())
}

// ── bench ─────────────────────────────────────────────────────────────────────

#[derive(Serialize)]
struct Meta<'a> {
    kind: &'static str,
    schema: u32,
    label: &'a str,
    corpus_dir: String,
    mode: String,
    huffman: String,
    blocks: String,
    container: &'a str,
    reps: usize,
    warmup: usize,
    started_at_unix: f64,
    host: Option<String>,
    cpu_model: Option<String>,
    loadavg: Option<String>,
    methods: BTreeMap<String, Option<String>>,
}

#[derive(Serialize)]
struct FileRow<'a> {
    kind: &'static str,
    file: &'a str,
    raw: u64,
    method: &'a str,
    bytes: Option<u64>,
    verified: bool,
    error: Option<String>,
    total_s: Vec<f64>,
    parse_s: Vec<f64>,
    encode_s: Vec<f64>,
    median_total_s: Option<f64>,
    parsed_bytes: Option<u64>,
}

fn median(v: &[f64]) -> Option<f64> {
    if v.is_empty() {
        return None;
    }
    let mut s = v.to_vec();
    s.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = s.len();
    Some(if n % 2 == 1 { s[n / 2] } else { (s[n / 2 - 1] + s[n / 2]) / 2.0 })
}

fn read_trim(path: &str) -> Option<String> {
    std::fs::read_to_string(path).ok().map(|s| s.trim().to_string())
}

fn cpu_model() -> Option<String> {
    let s = std::fs::read_to_string("/proc/cpuinfo").ok()?;
    s.lines().find(|l| l.starts_with("model name")).and_then(|l| l.split_once(':')).map(|(_, v)| v.trim().to_string())
}

/// Every regular file under `dir`, recursively, sorted; dotfiles skipped.
fn corpus_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    let mut todo = vec![dir.to_path_buf()];
    while let Some(d) = todo.pop() {
        for e in std::fs::read_dir(&d).map_err(|e| format!("{}: {e}", d.display()))? {
            let e = e.map_err(|e| e.to_string())?;
            if e.file_name().to_string_lossy().starts_with('.') {
                continue;
            }
            let ft = e.file_type().map_err(|e| e.to_string())?;
            if ft.is_dir() {
                todo.push(e.path());
            } else if ft.is_file() {
                files.push(e.path());
            }
        }
    }
    files.sort();
    Ok(files)
}

fn cmd_bench(args: &[String]) -> Result<(), String> {
    let a = Args::parse(
        args,
        &["corpus", "label", "method", "mode", "huffman", "blocks", "container", "reps", "warmup", "out", "validator", "work"],
    )?;
    let corpus = PathBuf::from(a.one("corpus").ok_or("--corpus DIR")?);
    let mode = Mode::parse(a.one("mode").unwrap_or("whole"))?;
    let h = coding(&a)?;
    let reps: usize = a.one("reps").unwrap_or("11").parse().map_err(|_| "bad --reps")?;
    let warmup: usize = a.one("warmup").unwrap_or("1").parse().map_err(|_| "bad --warmup")?;
    let validator = a.one("validator").map(PathBuf::from);
    let work = a.one("work").map(PathBuf::from);
    // Framing added to every whole/stream output's size, to compare with tools that write files.
    let (container, frame) = match a.one("container").unwrap_or("raw") {
        "raw" => ("raw", 0u64),
        "zlib" => ("zlib", 6),
        "gzip" => ("gzip", 18),
        c => return Err(format!("bad --container {c}")),
    };
    let frame = match mode {
        Mode::Whole | Mode::Stream { .. } | Mode::Messages { .. } => frame,
        Mode::Indep { .. } | Mode::Bgzf | Mode::Png => 0,
    };
    let methods: Vec<Method> = a
        .all("method")
        .iter()
        .map(|s| load_method(s, validator.as_deref(), work.as_deref()))
        .collect::<Result<_, _>>()?;
    if methods.is_empty() {
        return Err("no --method".to_string());
    }
    let mut out: Box<dyn std::io::Write> = match a.one("out") {
        Some(p) => Box::new(std::io::BufWriter::new(std::fs::File::create(p).map_err(|e| e.to_string())?)),
        None => Box::new(std::io::stdout()),
    };
    let mut emit = |v: &dyn erased::Json| -> Result<(), String> {
        writeln!(out, "{}", v.json()).map_err(|e| e.to_string())?;
        out.flush().map_err(|e| e.to_string())
    };
    let label = a.one("label").unwrap_or("corpus");
    emit(&Meta {
        kind: "meta",
        schema: 1,
        label,
        corpus_dir: corpus.display().to_string(),
        mode: format!("{mode:?}"),
        huffman: format!("{:?}", h.huffman),
        blocks: format!("{:?}", h.blocks),
        container,
        reps,
        warmup,
        started_at_unix: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs_f64())
            .unwrap_or(0.0),
        host: read_trim("/etc/hostname"),
        cpu_model: cpu_model(),
        loadavg: read_trim("/proc/loadavg"),
        methods: methods.iter().map(|m| (m.name.clone(), m.source_sha256.clone())).collect(),
    })?;

    let files = corpus_files(&corpus)?;
    let timed = !methods.iter().all(|m| matches!(m.kind, Kind::Retok(_)));
    for f in &files {
        let data = std::fs::read(f).map_err(|e| format!("{}: {e}", f.display()))?;
        let fname = f.strip_prefix(&corpus).unwrap_or(f).to_string_lossy().to_string();
        struct Acc {
            bytes: Option<u64>,
            verified: bool,
            error: Option<String>,
            total: Vec<f64>,
            parse: Vec<f64>,
            encode: Vec<f64>,
            parsed: Option<u64>,
        }
        let mut acc: Vec<Acc> = methods
            .iter()
            .map(|_| Acc { bytes: None, verified: false, error: None, total: vec![], parse: vec![], encode: vec![], parsed: None })
            .collect();
        let rounds = if timed { warmup + reps } else { 1 };
        // Interleaved, as the gate measures: every method once per round.
        for round in 0..rounds {
            for (m, ac) in methods.iter().zip(acc.iter_mut()) {
                if ac.error.is_some() || (matches!(m.kind, Kind::Retok(_)) && round > 0) {
                    continue;
                }
                match compress(m, &data, mode, h) {
                    Err(e) => ac.error = Some(e),
                    Ok(run) => {
                        if ac.bytes.is_none() {
                            ac.bytes = Some(run.bytes + frame);
                            ac.parsed = run.parsed_bytes;
                            match check(&run, &data, mode) {
                                Ok(()) => ac.verified = true,
                                Err(e) => ac.error = Some(format!("round trip: {e}")),
                            }
                        } else if ac.bytes != Some(run.bytes + frame) {
                            ac.error = Some("output size changed between runs".to_string());
                        }
                        if round >= warmup && !matches!(m.kind, Kind::Retok(_)) {
                            ac.total.push(run.total_s);
                            if let Some(p) = run.parse_s {
                                ac.parse.push(p);
                            }
                            if let Some(e) = run.encode_s {
                                ac.encode.push(e);
                            }
                        }
                    }
                }
            }
        }
        for (m, ac) in methods.iter().zip(acc) {
            emit(&FileRow {
                kind: "file",
                file: &fname,
                raw: data.len() as u64,
                method: &m.name,
                bytes: ac.bytes,
                verified: ac.verified,
                error: ac.error,
                median_total_s: median(&ac.total),
                total_s: ac.total,
                parse_s: ac.parse,
                encode_s: ac.encode,
                parsed_bytes: ac.parsed,
            })?;
        }
    }
    Ok(())
}

mod erased {
    pub trait Json {
        fn json(&self) -> String;
    }
    impl<T: serde::Serialize> Json for T {
        fn json(&self) -> String {
            serde_json::to_string(self).expect("rows serialise")
        }
    }
}

// ── gz ────────────────────────────────────────────────────────────────────────

fn peak_rss_kib() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/self/status").ok()?;
    s.lines().find(|l| l.starts_with("VmHWM:"))?.split_whitespace().nth(1)?.parse().ok()
}

fn cmd_gz(args: &[String]) -> Result<(), String> {
    let a = Args::parse(args, &["method", "mode", "format", "huffman", "blocks", "validator", "work"])?;
    let m = load_method(
        a.one("method").ok_or("--method M")?,
        a.one("validator").map(Path::new),
        a.one("work").map(Path::new),
    )?;
    let mode = Mode::parse(a.one("mode").unwrap_or("stream:1m"))?;
    let h = coding(&a)?;
    let [input, output] = a.positional.as_slice() else {
        return Err("arena gz ... IN OUT".to_string());
    };
    let data = std::fs::read(input).map_err(|e| format!("{input}: {e}"))?;
    let format = a.one("format").unwrap_or(if matches!(mode, Mode::Bgzf) { "bgzf" } else { "gzip" });
    let run = compress(&m, &data, mode, h)?;
    check(&run, &data, mode)?;
    let bytes = match (format, mode) {
        (_, Mode::Png) => run.out[0].clone(),
        ("bgzf", Mode::Bgzf) => run.out.concat(),
        ("bgzf", _) => return Err("--format bgzf needs --mode bgzf".to_string()),
        (_, Mode::Bgzf) => return Err("--mode bgzf writes --format bgzf".to_string()),
        (_, Mode::Indep { .. }) if run.out.len() > 1 && format != "raw" => {
            // One gzip member per chunk, as pigz --independent writes when concatenated.
            let mut v = Vec::new();
            let chunk = match mode {
                Mode::Indep { chunk } => chunk,
                _ => unreachable!(),
            };
            for (o, piece) in run.out.iter().zip(data.chunks(chunk)) {
                v.extend(container::gzip(o, piece));
            }
            v
        }
        ("gzip", _) => container::gzip(&run.out[0], &data),
        ("zlib", _) => container::zlib(&run.out[0], &data),
        ("raw", _) => run.out.concat(),
        (f, _) => return Err(format!("bad --format {f}")),
    };
    std::fs::write(output, &bytes).map_err(|e| format!("{output}: {e}"))?;
    eprintln!(
        "{}\t{} -> {} bytes\t{:.4}s\tparse {:.4}s encode {:.4}s\tpeak {} KiB",
        m.name,
        data.len(),
        bytes.len(),
        run.total_s,
        run.parse_s.unwrap_or(f64::NAN),
        run.encode_s.unwrap_or(f64::NAN),
        peak_rss_kib().unwrap_or(0)
    );
    Ok(())
}
