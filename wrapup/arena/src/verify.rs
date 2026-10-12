//! Round trips through independent inflaters. Agreement of three is the evidence;
//! nothing a parser or adapter emits is trusted without it.

use std::io::Read;

/// Raw DEFLATE through miniz_oxide, zlib and libdeflate.
pub fn raw(compressed: &[u8], original: &[u8]) -> Result<(), String> {
    match miniz_oxide::inflate::decompress_to_vec(compressed) {
        Ok(got) if got == original => {}
        Ok(got) => return Err(format!("miniz_oxide decoded {} bytes, expected {}", got.len(), original.len())),
        Err(e) => return Err(format!("miniz_oxide refused the stream: {e:?}")),
    }
    let mut got = Vec::new();
    match flate2::read::DeflateDecoder::new(compressed).read_to_end(&mut got) {
        Ok(_) if got == original => {}
        Ok(_) => return Err(format!("zlib decoded {} bytes, expected {}", got.len(), original.len())),
        Err(e) => return Err(format!("zlib refused the stream: {e}")),
    }
    let mut d = libdeflater::Decompressor::new();
    let mut buf = vec![0u8; original.len()];
    match d.deflate_decompress(compressed, &mut buf) {
        Ok(n) if n == original.len() && buf == original => Ok(()),
        Ok(n) => Err(format!("libdeflate decoded {n} bytes, expected {}", original.len())),
        Err(e) => Err(format!("libdeflate refused the stream: {e:?}")),
    }
}

/// gzip (one or more members, so BGZF too) through zlib. The raw DEFLATE inside
/// is checked with [`raw`] where it is produced.
pub fn gzip(compressed: &[u8], original: &[u8]) -> Result<(), String> {
    let mut got = Vec::new();
    flate2::read::MultiGzDecoder::new(compressed)
        .read_to_end(&mut got)
        .map_err(|e| format!("zlib refused the gzip stream: {e}"))?;
    if got != original {
        return Err(format!("zlib decoded {} bytes of gzip, expected {}", got.len(), original.len()));
    }
    Ok(())
}

pub fn zlib(compressed: &[u8], original: &[u8]) -> Result<(), String> {
    let mut got = Vec::new();
    flate2::read::ZlibDecoder::new(compressed)
        .read_to_end(&mut got)
        .map_err(|e| format!("zlib refused the zlib stream: {e}"))?;
    if got != original {
        return Err(format!("zlib decoded {} bytes of zlib, expected {}", got.len(), original.len()));
    }
    match miniz_oxide::inflate::decompress_to_vec_zlib(compressed) {
        Ok(g) if g == original => Ok(()),
        Ok(g) => Err(format!("miniz_oxide decoded {} bytes of zlib, expected {}", g.len(), original.len())),
        Err(e) => Err(format!("miniz_oxide refused the zlib stream: {e:?}")),
    }
}
