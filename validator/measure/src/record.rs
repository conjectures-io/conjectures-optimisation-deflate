//! The JSONL the engine emits: one `meta` line, then one line per corpus file.

use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

/// v3: methods are dlopen'd cdylibs rather than linked-in functions, so `meta.methods`
/// carries `source_sha256`/`lib_sha256` per method; `output_sha256` added per method;
/// the reference bars became ordinary `external` methods; one corpus per run.
// v4: encode every repetition; separate stage and combined compression timings.
pub const SCHEMA_VERSION: u32 = 4;

pub fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    h.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

pub fn sha256_tokens(toks: &[u32]) -> String {
    let mut h = Sha256::new();
    for t in toks {
        h.update(t.to_le_bytes());
    }
    h.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

#[derive(Serialize)]
pub struct MethodMeta {
    pub external: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub crate_dir: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_sha256: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lib_sha256: Option<String>,
}

#[derive(Serialize)]
pub struct Meta {
    pub kind: &'static str,
    pub schema_version: u32,
    pub started_at_unix: f64,
    pub corpus: String,
    pub corpus_dir: String,
    pub os: &'static str,
    pub arch: &'static str,
    pub rustc_version: Option<String>,
    pub cpu_model: Option<String>,
    pub cpu_governor: Option<String>,
    pub warmup_rounds: usize,
    pub measured_rounds: usize,
    pub speed_floor: Option<f64>,
    pub methods: BTreeMap<String, MethodMeta>,
}

#[derive(Serialize)]
pub struct Rep {
    pub phase: &'static str,
    pub order_index: u64,
    /// LZ77 time for slots; full compression for external references (legacy field).
    pub time_s: f64,
    pub encode_s: Option<f64>,
    pub total_s: Option<f64>,
}

/// One method on one corpus file. Every rep is kept; nothing is folded.
#[derive(Serialize)]
pub struct MethodOut {
    pub external: bool,
    pub output_bytes: Option<u64>,
    pub output_sha256: Option<String>,
    pub tokens: Option<u64>,
    pub tokens_sha256: Option<String>,
    pub deterministic: bool,
    /// Legacy first-round observation; stage statistics use the per-repetition fields.
    pub encode_s: Option<f64>,
    pub errors: Vec<String>,
    pub reps: Vec<Rep>,
}

#[derive(Serialize)]
pub struct FileOut {
    pub kind: &'static str,
    pub corpus: String,
    pub file: String,
    pub raw_bytes: u64,
    pub sha256: String,
    pub methods: BTreeMap<String, MethodOut>,
}
