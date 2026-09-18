//! The shim every measured parser is wrapped in: one C-ABI symbol, no panic escapes.
//!
//! Copied verbatim beside a submission's `parse.rs` into a generated crate; see
//! `notes-sandboxed-benchmark.md` for why it is `mod parse` and not `include!`,
//! and why `catch_unwind` lives here rather than in the engine.

mod parse;

use std::panic::AssertUnwindSafe;

/// Returns the token count, or `usize::MAX` if `parse` panicked.
#[no_mangle]
pub extern "C" fn slot_parse(input: *const u8, len: usize, out: *mut u32, cap: usize) -> usize {
    let input = unsafe { std::slice::from_raw_parts(input, len) };
    let out = unsafe { std::slice::from_raw_parts_mut(out, cap) };
    std::panic::catch_unwind(AssertUnwindSafe(|| parse::parse(input, out))).unwrap_or(usize::MAX)
}
