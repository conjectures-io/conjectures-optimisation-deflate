//! `vgzip`: gzip with proved LZ77 parsers.
//!
//! ```text
//! vgzip [OPTIONS] [FILE...]      compress each FILE to FILE.gz (FILE is removed unless -k)
//! vgzip [OPTIONS] < in > out     no FILE: stdin to stdout
//!
//!   -c, --stdout          write to stdout, keep FILE
//!   -k, --keep            keep FILE
//!   -f, --force           overwrite FILE.gz
//!   -d, --decompress      decompress (standard inflate; any gzip reader works too)
//!   -1 .. -3, --fast      Balanced (#521)
//!   -4 .. -6              High (#85, the default)
//!   -7 .. -9, --best      Max (#243)
//!   --level balanced|high|max
//!   --bgzf                write BGZF (64 KiB blocks, readable by samtools/tabix)
//!   --chunk BYTES         input per parser call (default 1048576)
//!   -v, --verbose         sizes and timing on stderr
//!   -h, --help
//! ```

use std::fs::File;
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};
use std::time::Instant;
use verified_deflate::{bgzf, GzEncoder, Level, Options};

struct Opts {
    stdout: bool,
    keep: bool,
    force: bool,
    decompress: bool,
    bgzf: bool,
    verbose: bool,
    options: Options,
    files: Vec<PathBuf>,
}

fn usage() -> ! {
    let doc = include_str!("vgzip.rs");
    for line in doc.lines().skip(3).take_while(|l| l.starts_with("//!")) {
        eprintln!("{}", line.trim_start_matches("//!").trim_start_matches(' ').trim_end_matches("```"));
    }
    std::process::exit(2)
}

fn parse_args() -> Result<Opts, String> {
    let mut o = Opts {
        stdout: false,
        keep: false,
        force: false,
        decompress: false,
        bgzf: false,
        verbose: false,
        options: Options::default(),
        files: Vec::new(),
    };
    let mut args = std::env::args().skip(1);
    let mut only_files = false;
    while let Some(a) = args.next() {
        if only_files || !a.starts_with('-') || a == "-" {
            o.files.push(PathBuf::from(a));
            continue;
        }
        match a.as_str() {
            "--" => only_files = true,
            "-c" | "--stdout" => o.stdout = true,
            "-k" | "--keep" => o.keep = true,
            "-f" | "--force" => o.force = true,
            "-d" | "--decompress" => o.decompress = true,
            "-v" | "--verbose" => o.verbose = true,
            "--bgzf" => o.bgzf = true,
            "--fast" => o.options.level = Level::Balanced,
            "--best" => o.options.level = Level::Max,
            "--level" => {
                o.options.level = match args.next().as_deref() {
                    Some("balanced") => Level::Balanced,
                    Some("high") => Level::High,
                    Some("max") => Level::Max,
                    v => return Err(format!("--level balanced|high|max, not {v:?}")),
                }
            }
            "--chunk" => {
                o.options.chunk = args
                    .next()
                    .and_then(|v| v.parse().ok())
                    .filter(|&c: &usize| c > 0)
                    .ok_or("--chunk needs a positive number of bytes")?
            }
            "-h" | "--help" => usage(),
            s if s.len() == 2 && s.as_bytes()[1].is_ascii_digit() => {
                o.options.level = Level::from_gzip((s.as_bytes()[1] - b'0') as u32)
            }
            // Bundled short flags, e.g. -kc9.
            s if !s.starts_with("--") && s.len() > 2 => {
                for c in s[1..].chars() {
                    match c {
                        'c' => o.stdout = true,
                        'k' => o.keep = true,
                        'f' => o.force = true,
                        'd' => o.decompress = true,
                        'v' => o.verbose = true,
                        d if d.is_ascii_digit() => o.options.level = Level::from_gzip(d as u32 - '0' as u32),
                        _ => return Err(format!("unknown option -{c}")),
                    }
                }
            }
            _ => return Err(format!("unknown option {a}")),
        }
    }
    Ok(o)
}

fn compress(o: &Opts, input: &mut dyn Read, output: &mut dyn Write) -> io::Result<(u64, u64)> {
    let mut counter = Counter { inner: output, n: 0 };
    let mut read = 0u64;
    let mut buf = vec![0u8; 1 << 20];
    if o.bgzf {
        let mut e = bgzf::BgzfEncoder::new(&mut counter, o.options);
        loop {
            let n = input.read(&mut buf)?;
            if n == 0 {
                break;
            }
            read += n as u64;
            e.write_all(&buf[..n])?;
        }
        e.finish()?;
    } else {
        let mut e = GzEncoder::new(&mut counter, o.options);
        loop {
            let n = input.read(&mut buf)?;
            if n == 0 {
                break;
            }
            read += n as u64;
            e.write_all(&buf[..n])?;
        }
        e.finish()?;
    }
    counter.flush()?;
    Ok((read, counter.n))
}

fn decompress(input: &mut dyn Read, output: &mut dyn Write) -> io::Result<(u64, u64)> {
    let mut counter = Counter { inner: output, n: 0 };
    let mut d = flate2::read::MultiGzDecoder::new(input);
    io::copy(&mut d, &mut counter)?;
    counter.flush()?;
    Ok((0, counter.n))
}

struct Counter<'a> {
    inner: &'a mut dyn Write,
    n: u64,
}

impl Write for Counter<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let n = self.inner.write(buf)?;
        self.n += n as u64;
        Ok(n)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

fn run_file(o: &Opts, path: &Path) -> Result<(), String> {
    let target = if o.decompress {
        match path.to_str().and_then(|s| s.strip_suffix(".gz")) {
            Some(t) => PathBuf::from(t),
            None if o.stdout => PathBuf::new(),
            None => return Err(format!("{}: no .gz suffix", path.display())),
        }
    } else {
        PathBuf::from(format!("{}.gz", path.display()))
    };
    let mut input = BufReader::new(File::open(path).map_err(|e| format!("{}: {e}", path.display()))?);
    let t0 = Instant::now();
    let (r, w) = if o.stdout {
        let stdout = io::stdout();
        let mut out = BufWriter::new(stdout.lock());
        if o.decompress { decompress(&mut input, &mut out) } else { compress(o, &mut input, &mut out) }
            .map_err(|e| format!("{}: {e}", path.display()))?
    } else {
        if target.exists() && !o.force {
            return Err(format!("{} exists; use -f to overwrite", target.display()));
        }
        let tmp = target.with_extension("vgzip-tmp");
        let mut out = BufWriter::new(File::create(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?);
        let res = if o.decompress { decompress(&mut input, &mut out) } else { compress(o, &mut input, &mut out) };
        let res = res.and_then(|rw| out.into_inner().map_err(|e| e.into_error()).map(|_| rw));
        match res {
            Ok(rw) => {
                std::fs::rename(&tmp, &target).map_err(|e| format!("{}: {e}", target.display()))?;
                if !o.keep {
                    std::fs::remove_file(path).map_err(|e| format!("{}: {e}", path.display()))?;
                }
                rw
            }
            Err(e) => {
                let _ = std::fs::remove_file(&tmp);
                return Err(format!("{}: {e}", path.display()));
            }
        }
    };
    if o.verbose {
        let s = t0.elapsed().as_secs_f64();
        if o.decompress {
            eprintln!("{}: {w} bytes out, {s:.3} s", path.display());
        } else {
            eprintln!(
                "{}: {r} -> {w} bytes ({:.2}%), {:?} (#{}), {:.1} MB/s",
                path.display(),
                if r > 0 { 100.0 * w as f64 / r as f64 } else { 0.0 },
                o.options.level,
                o.options.level.submission(),
                r as f64 / s.max(1e-9) / 1e6
            );
        }
    }
    Ok(())
}

fn main() {
    let o = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("vgzip: {e}");
            std::process::exit(2);
        }
    };
    let mut failed = false;
    if o.files.is_empty() || (o.files.len() == 1 && o.files[0] == Path::new("-")) {
        let stdin = io::stdin();
        let stdout = io::stdout();
        let mut out = BufWriter::new(stdout.lock());
        let res = if o.decompress {
            decompress(&mut stdin.lock(), &mut out)
        } else {
            compress(&o, &mut stdin.lock(), &mut out)
        };
        if let Err(e) = res {
            eprintln!("vgzip: {e}");
            failed = true;
        }
    } else {
        for f in &o.files {
            if let Err(e) = run_file(&o, f) {
                eprintln!("vgzip: {e}");
                failed = true;
            }
        }
    }
    std::process::exit(if failed { 1 } else { 0 });
}
