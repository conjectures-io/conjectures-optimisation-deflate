//! Framing raw DEFLATE as gzip (RFC 1952), zlib (RFC 1950) or BGZF (SAM spec §4.1).

/// gzip header: no name, mtime 0, OS "unknown", so outputs are reproducible.
pub const GZIP_HEADER: [u8; 10] = [0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 0xff];

pub fn gzip_trailer(data_crc: u32, len: u64) -> [u8; 8] {
    let mut t = [0u8; 8];
    t[..4].copy_from_slice(&data_crc.to_le_bytes());
    t[4..].copy_from_slice(&(len as u32).to_le_bytes());
    t
}

pub fn gzip(raw: &[u8], data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(raw.len() + 18);
    out.extend_from_slice(&GZIP_HEADER);
    out.extend_from_slice(raw);
    out.extend_from_slice(&gzip_trailer(crc32fast::hash(data), data.len() as u64));
    out
}

/// zlib header with a 32 KiB window; `FLEVEL` is informational only.
pub fn zlib_header(flevel: u8) -> [u8; 2] {
    let cmf = 0x78u16;
    let mut flg = ((flevel & 3) as u16) << 6;
    flg += 31 - ((cmf << 8) + flg) % 31;
    [cmf as u8, flg as u8]
}

pub fn zlib(raw: &[u8], data: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(raw.len() + 6);
    out.extend_from_slice(&zlib_header(2));
    out.extend_from_slice(raw);
    out.extend_from_slice(&adler2::adler32_slice(data).to_be_bytes());
    out
}

/// Largest input per BGZF block, as htslib writes them.
pub const BGZF_BLOCK_INPUT: usize = 0xff00;
/// A BGZF block may not exceed 64 KiB in total.
pub const BGZF_MAX_BLOCK: usize = 65536;
const BGZF_OVERHEAD: usize = 18 + 8;

/// The empty block every BGZF file ends with.
pub const BGZF_EOF: [u8; 28] = [
    0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 0xff, 6, 0, 0x42, 0x43, 2, 0, 0x1b, 0, 3, 0, 0, 0, 0, 0, 0, 0,
    0, 0,
];

/// One BGZF block around `raw` (the DEFLATE of `data`), or `None` if it would exceed 64 KiB.
pub fn bgzf_block(raw: &[u8], data: &[u8]) -> Option<Vec<u8>> {
    let total = raw.len() + BGZF_OVERHEAD;
    if total > BGZF_MAX_BLOCK {
        return None;
    }
    let mut out = Vec::with_capacity(total);
    out.extend_from_slice(&[0x1f, 0x8b, 8, 4, 0, 0, 0, 0, 0, 0xff, 6, 0, 0x42, 0x43, 2, 0]);
    out.extend_from_slice(&((total - 1) as u16).to_le_bytes());
    out.extend_from_slice(raw);
    out.extend_from_slice(&gzip_trailer(crc32fast::hash(data), data.len() as u64));
    Some(out)
}

/// A whole BGZF file. `deflate` compresses one block's input to raw DEFLATE; a
/// block that would not fit is split in half and retried, as htslib does.
pub fn bgzf<F>(data: &[u8], mut deflate: F) -> Result<Vec<u8>, String>
where
    F: FnMut(&[u8]) -> Result<Vec<u8>, String>,
{
    let mut out = Vec::new();
    let mut todo: Vec<&[u8]> = data.chunks(BGZF_BLOCK_INPUT).rev().collect();
    while let Some(piece) = todo.pop() {
        let raw = deflate(piece)?;
        match bgzf_block(&raw, piece) {
            Some(b) => out.extend(b),
            None if piece.len() > 1 => {
                let (a, b) = piece.split_at(piece.len() / 2);
                todo.push(b);
                todo.push(a);
            }
            None => return Err("a one-byte BGZF block does not fit".to_string()),
        }
    }
    out.extend_from_slice(&BGZF_EOF);
    Ok(out)
}
