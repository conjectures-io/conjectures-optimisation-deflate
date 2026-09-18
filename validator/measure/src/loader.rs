//! Loading a parser: one `dlopen`, one symbol, one call.

use libloading::os::unix::{Library, Symbol, RTLD_LOCAL, RTLD_NOW};
use std::path::Path;

/// What `candidate/lib.rs` exports.
pub type ParseFn = unsafe extern "C" fn(*const u8, usize, *mut u32, usize) -> usize;

/// The token count a shim returns when `parse` panicked.
pub const PANICKED: usize = usize::MAX;

pub const SYMBOL: &[u8] = b"slot_parse\0";

pub struct Parser {
    entry: Symbol<ParseFn>,
    _lib: Library,
}

impl Parser {
    pub fn load(path: &Path) -> Result<Parser, String> {
        let lib = unsafe { Library::open(Some(path), RTLD_NOW | RTLD_LOCAL) }
            .map_err(|e| format!("dlopen {}: {e}", path.display()))?;
        let entry: Symbol<ParseFn> =
            unsafe { lib.get(SYMBOL) }.map_err(|e| format!("slot_parse in {}: {e}", path.display()))?;
        Ok(Parser { entry, _lib: lib })
    }

    /// Callers must pass a non-empty `input` and a non-empty `out`.
    pub fn parse(&self, input: &[u8], out: &mut [u32]) -> usize {
        unsafe { (*self.entry)(input.as_ptr(), input.len(), out.as_mut_ptr(), out.len()) }
    }
}
