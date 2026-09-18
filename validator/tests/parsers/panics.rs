//! A parser that panics. `catch_unwind` in the shim must turn this into a
//! correctness failure rather than an abort across the C ABI.

pub fn parse(input: &[u8], out: &mut [u32]) -> usize {
    if input.len() > out.len() {
        return 0;
    }
    panic!("this parser panics on purpose");
}
