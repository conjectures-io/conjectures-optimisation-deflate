//! Parsers: a submission's `parse.rs` built the way the gate builds it and
//! loaded through `slot_parse`, or a reference example linked in for tests.

use crate::loader;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

pub trait Parser {
    fn name(&self) -> &str;
    /// The raw slot contract: `out.len() >= input.len()`, returns the token count.
    /// `Err` when the parser panicked or reported more tokens than `out` holds.
    fn parse(&self, input: &[u8], out: &mut [u32]) -> Result<usize, String>;
}

/// A `parse.rs` built as the gate's `candidate` cdylib and called through `slot_parse`.
pub struct SlotParser {
    name: String,
    inner: loader::Parser,
    pub source_sha256: String,
    pub lib: PathBuf,
}

impl SlotParser {
    pub fn load(name: &str, lib: &Path, source_sha256: String) -> Result<Self, String> {
        Ok(SlotParser {
            name: name.to_string(),
            inner: loader::Parser::load(lib)?,
            source_sha256,
            lib: lib.to_path_buf(),
        })
    }
}

impl Parser for SlotParser {
    fn name(&self) -> &str {
        &self.name
    }

    fn parse(&self, input: &[u8], out: &mut [u32]) -> Result<usize, String> {
        if input.is_empty() {
            return Ok(0);
        }
        let n = self.inner.parse(input, out);
        if n == loader::PANICKED {
            return Err(format!("{}: parse panicked", self.name));
        }
        if n > out.len() {
            return Err(format!("{}: {n} tokens reported into a buffer of {}", self.name, out.len()));
        }
        Ok(n)
    }
}

/// A parser linked into this binary.
pub struct FnParser {
    pub name: &'static str,
    pub f: fn(&[u8], &mut [u32]) -> usize,
}

impl Parser for FnParser {
    fn name(&self) -> &str {
        self.name
    }

    fn parse(&self, input: &[u8], out: &mut [u32]) -> Result<usize, String> {
        if input.is_empty() {
            return Ok(0);
        }
        let f = self.f;
        let n = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(input, out)))
            .map_err(|_| format!("{}: parse panicked", self.name))?;
        if n > out.len() {
            return Err(format!("{}: {n} tokens reported into a buffer of {}", self.name, out.len()));
        }
        Ok(n)
    }
}

pub fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

/// Build `source` (a `parse.rs`) as the gate does: the `candidate` template, the
/// pinned `rust-toolchain.toml`, `cargo build --release --offline`. Crates are
/// cached under `work/<sha256[..16]>`, so a source is built once.
pub fn build_slot(validator: &Path, source: &Path, work: &Path) -> Result<(PathBuf, String), String> {
    let src = std::fs::read(source).map_err(|e| format!("read {}: {e}", source.display()))?;
    let sha = sha256_hex(&src);
    let crate_dir = work.join(&sha[..16]);
    let lib = crate_dir.join("target/release/libcandidate.so");
    if lib.exists() {
        return Ok((lib, sha));
    }
    let template = validator.join("measure/candidate");
    std::fs::create_dir_all(crate_dir.join("src")).map_err(|e| e.to_string())?;
    let copy = |from: PathBuf, to: PathBuf| {
        std::fs::copy(&from, &to).map(|_| ()).map_err(|e| format!("copy {}: {e}", from.display()))
    };
    copy(template.join("Cargo.toml"), crate_dir.join("Cargo.toml"))?;
    copy(template.join("lib.rs"), crate_dir.join("src/lib.rs"))?;
    copy(validator.join("rust-toolchain.toml"), crate_dir.join("rust-toolchain.toml"))?;
    std::fs::write(crate_dir.join("src/parse.rs"), &src).map_err(|e| e.to_string())?;
    let out = Command::new("cargo")
        .args(["build", "--release", "--offline", "-q"])
        .current_dir(&crate_dir)
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_TARGET_DIR")
        .output()
        .map_err(|e| format!("cargo: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "build {}: {}",
            source.display(),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok((lib, sha))
}
