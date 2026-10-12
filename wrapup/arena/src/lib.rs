//! Real-world harness for the competition's LZ77 parsers.
//!
//! The pinned pieces of `validator/measure` (token format, loader, encoder) are
//! included by path, not copied, so this crate cannot drift from what the gate
//! measures. [`encoder`] is the incremental twin of the pinned encoder and is
//! tested to be byte-identical to it.

#[path = "../../../validator/measure/src/token.rs"]
pub mod token;

#[path = "../../../validator/measure/src/loader.rs"]
pub mod loader;

/// The gate's encoder, untouched: the reference [`encoder`] is tested against.
#[allow(dead_code)]
#[path = "../../../validator/measure/src/deflate.rs"]
pub mod pinned;

pub mod builtin;
pub mod container;
pub mod encoder;
pub mod inflate_tokens;
pub mod parser;
pub mod png;
pub mod reference;
pub mod stream;
pub mod verify;
