//! The repository's reference parsers, linked in for tests and quick local runs.
//! Benchmarks should load them as slots instead, so every parser pays the same
//! cdylib boundary and is built with the gate's profile.

use crate::parser::FnParser;

#[allow(dead_code, clippy::all)]
#[path = "../../../validator/incumbent/parse.rs"]
mod incumbent;
#[allow(dead_code, clippy::all)]
#[path = "../../../miner/template/parse.rs"]
mod template;
#[allow(dead_code, clippy::all)]
#[path = "../../../miner/examples/hash-chains/parse.rs"]
mod hash_chains;
#[allow(dead_code, clippy::all)]
#[path = "../../../miner/examples/mo-lazy/parse.rs"]
mod mo_lazy;
#[allow(dead_code, clippy::all)]
#[path = "../../../miner/examples/optimal-iter/parse.rs"]
mod optimal_iter;
#[allow(dead_code, clippy::all)]
#[path = "../../../miner/examples/no-lz77/parse.rs"]
mod no_lz77;

pub fn all() -> Vec<FnParser> {
    vec![
        FnParser { name: "incumbent", f: incumbent::parse },
        FnParser { name: "template", f: template::parse },
        FnParser { name: "hash-chains", f: hash_chains::parse },
        FnParser { name: "mo-lazy", f: mo_lazy::parse },
        FnParser { name: "optimal-iter", f: optimal_iter::parse },
        FnParser { name: "no-lz77", f: no_lz77::parse },
    ]
}

pub fn by_name(name: &str) -> Option<FnParser> {
    all().into_iter().find(|p| p.name == name)
}
