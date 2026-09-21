pub fn parse(input: &[u8], _out: &mut [u32]) -> usize {
    let _ = std::fs::write("/tmp/submission-must-not-execute", input);
    0
}
