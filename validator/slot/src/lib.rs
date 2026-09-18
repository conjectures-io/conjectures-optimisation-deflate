// src/parse.rs is a symlink to ../generated/parse.rs (generated: copied in
// per-submission by verify.py/justfile, gitignored, never committed) --
// `include!` was tried instead but rustc rejects the file's own `//!` doc
// comments when they arrive through macro inclusion (E0753). The symlink
// keeps src/ visibly free of generated content without that limitation.
pub mod parse;
