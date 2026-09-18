//! A parser that overflows the stack. Nothing in the shim can catch this, so it
//! kills the engine process it is loaded into -- which is why there is one
//! process per candidate.

pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    let _ = out;
    deeper(input.len())
}

/// `black_box` makes each frame's address escape, so this cannot be turned into
/// a loop the way a plain accumulating recursion can.
fn deeper(n: usize) -> usize {
    let pad = [n; 64];
    let p = std::hint::black_box(&pad);
    if n == 0 {
        return p[0];
    }
    let r = deeper(n - 1);
    std::hint::black_box(p[r % 64]).wrapping_add(r)
}
