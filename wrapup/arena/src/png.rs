//! PNG IDAT recompression: the filtered scanlines stay as they are (the filters
//! the PNG was written with), only the DEFLATE stream around them changes.

pub const SIGNATURE: [u8; 8] = [0x89, b'P', b'N', b'G', 0x0d, 0x0a, 0x1a, 0x0a];

pub struct Png<'a> {
    /// Chunks before the first IDAT (signature excluded), as raw chunk bytes.
    pub head: Vec<&'a [u8]>,
    /// Chunks after the last IDAT, IEND included.
    pub tail: Vec<&'a [u8]>,
    /// The concatenated IDAT payload: one zlib stream.
    pub idat: Vec<u8>,
}

pub fn parse(data: &[u8]) -> Result<Png<'_>, String> {
    if data.len() < 8 || data[..8] != SIGNATURE {
        return Err("not a PNG".to_string());
    }
    let (mut head, mut tail, mut idat) = (Vec::new(), Vec::new(), Vec::new());
    let mut seen_idat = false;
    let mut pos = 8;
    while pos + 12 <= data.len() {
        let len = u32::from_be_bytes(data[pos..pos + 4].try_into().unwrap()) as usize;
        let end = pos + 12 + len;
        if end > data.len() {
            return Err("truncated chunk".to_string());
        }
        let kind = &data[pos + 4..pos + 8];
        let chunk = &data[pos..end];
        if kind == b"IDAT" {
            idat.extend_from_slice(&data[pos + 8..pos + 8 + len]);
            seen_idat = true;
        } else if seen_idat {
            tail.push(chunk);
        } else {
            head.push(chunk);
        }
        pos = end;
    }
    if !seen_idat {
        return Err("no IDAT".to_string());
    }
    Ok(Png { head, tail, idat })
}

impl Png<'_> {
    /// The filtered scanlines.
    pub fn scanlines(&self) -> Result<Vec<u8>, String> {
        miniz_oxide::inflate::decompress_to_vec_zlib(&self.idat).map_err(|e| format!("IDAT: {e:?}"))
    }

    /// The same PNG with `zlib` (a whole zlib stream) as its single IDAT.
    pub fn with_idat(&self, zlib: &[u8]) -> Vec<u8> {
        let mut out = Vec::with_capacity(zlib.len() + 1024);
        out.extend_from_slice(&SIGNATURE);
        for c in &self.head {
            out.extend_from_slice(c);
        }
        out.extend_from_slice(&(zlib.len() as u32).to_be_bytes());
        let mut crc = crc32fast::Hasher::new();
        crc.update(b"IDAT");
        crc.update(zlib);
        out.extend_from_slice(b"IDAT");
        out.extend_from_slice(zlib);
        out.extend_from_slice(&crc.finalize().to_be_bytes());
        for c in &self.tail {
            out.extend_from_slice(c);
        }
        out
    }
}
