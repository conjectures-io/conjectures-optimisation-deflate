//! The library against three independent decoders, and against the benchmark
//! harness (`wrapup/arena`) whose measurements the README quotes.

use std::io::{Read, Write};
use std::path::Path;
use verified_deflate::{bgzf, deflate, gzip, zlib, DeflateEncoder, GzEncoder, Level, Options, ZlibEncoder};

fn lcg(s: &mut u64) -> u64 {
    *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *s >> 33
}

fn inputs() -> Vec<(&'static str, Vec<u8>)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut text = Vec::new();
    for rel in ["docs/SCORING.md", "docs/OPERATIONS.md", "miner/MANUAL.md", "docs/wrapup/FINDINGS.md"] {
        text.extend(std::fs::read(root.join(rel)).expect(rel));
    }
    let mut s = 3u64;
    let random: Vec<u8> = (0..150_000).map(|_| lcg(&mut s) as u8).collect();
    let mut big = Vec::new();
    while big.len() < 2_600_000 {
        big.extend_from_slice(&text);
        big.extend_from_slice(&random[..20_000]);
        big.extend(std::iter::repeat(b'x').take(3000));
    }
    vec![
        ("empty", Vec::new()),
        ("one", b"a".to_vec()),
        ("short", b"hello hello hello hello".to_vec()),
        ("text", text),
        ("random", random),
        ("big", big),
    ]
}

fn inflate_raw(c: &[u8], n: usize) -> Vec<u8> {
    let a = miniz_oxide::inflate::decompress_to_vec(c).expect("miniz_oxide");
    let mut b = Vec::new();
    flate2::read::DeflateDecoder::new(c).read_to_end(&mut b).expect("zlib");
    let mut l = vec![0u8; n];
    let k = libdeflater::Decompressor::new().deflate_decompress(c, &mut l).expect("libdeflate");
    l.truncate(k);
    assert_eq!(a, b, "miniz_oxide and zlib disagree");
    assert_eq!(a, l, "miniz_oxide and libdeflate disagree");
    a
}

#[test]
fn every_level_round_trips_in_every_format() {
    for level in Level::ALL {
        for (name, data) in inputs() {
            for chunk in [4096usize, 65_536, 1 << 20] {
                let o = Options { level, chunk, ..Options::default() };
                let raw = deflate(&data, o);
                assert_eq!(inflate_raw(&raw, data.len()), data, "{level:?} {name} chunk {chunk}");

                let gz = gzip(&data, o);
                let mut got = Vec::new();
                flate2::read::GzDecoder::new(&gz[..]).read_to_end(&mut got).unwrap();
                assert_eq!(got, data, "{level:?} {name} gzip");

                let zl = zlib(&data, o);
                assert_eq!(miniz_oxide::inflate::decompress_to_vec_zlib(&zl).unwrap(), data, "{level:?} {name} zlib");
            }
            let b = bgzf::compress(&data, level);
            let mut got = Vec::new();
            flate2::read::MultiGzDecoder::new(&b[..]).read_to_end(&mut got).unwrap();
            assert_eq!(got, data, "{level:?} {name} bgzf");
            assert!(b.ends_with(&bgzf::EOF));
        }
    }
}

#[test]
fn output_does_not_depend_on_how_input_is_written() {
    let mut s = 11u64;
    for level in Level::ALL {
        for (name, data) in inputs() {
            let want = gzip(&data, level);
            let mut e = GzEncoder::new(Vec::new(), level);
            let mut i = 0;
            while i < data.len() {
                let k = (1 + lcg(&mut s) as usize % 300_000).min(data.len() - i);
                e.write_all(&data[i..i + k]).unwrap();
                i += k;
            }
            assert_eq!(e.finish().unwrap(), want, "{level:?} {name}");
        }
    }
}

#[test]
fn a_flush_makes_everything_written_decodable() {
    let data = inputs().into_iter().find(|(n, _)| *n == "big").unwrap().1;
    let mut e = DeflateEncoder::new(Vec::new(), Level::Max);
    e.write_all(&data[..1_234_567]).unwrap();
    e.flush().unwrap();
    let so_far = e.get_ref().clone();
    assert!(so_far.ends_with(&[0, 0, 0xff, 0xff]));
    let mut d = flate2::Decompress::new(false);
    let mut got = Vec::with_capacity(1_300_000);
    d.decompress_vec(&so_far, &mut got, flate2::FlushDecompress::Sync).unwrap();
    assert_eq!(&got[..], &data[..1_234_567]);
    e.write_all(&data[1_234_567..]).unwrap();
    let all = e.finish().unwrap();
    assert_eq!(inflate_raw(&all, data.len()), data);
}

#[test]
fn dropping_an_unfinished_encoder_still_writes_a_valid_stream() {
    let data = inputs().into_iter().find(|(n, _)| *n == "text").unwrap().1;
    let mut gz_out = Vec::new();
    {
        let mut e = GzEncoder::new(&mut gz_out, Level::Balanced);
        e.write_all(&data).unwrap();
    }
    let mut got = Vec::new();
    flate2::read::GzDecoder::new(&gz_out[..]).read_to_end(&mut got).unwrap();
    assert_eq!(got, data);

    let mut zl_out = Vec::new();
    {
        let mut e = ZlibEncoder::new(&mut zl_out, Level::High);
        e.write_all(&data).unwrap();
    }
    assert_eq!(miniz_oxide::inflate::decompress_to_vec_zlib(&zl_out).unwrap(), data);
}

#[test]
fn identical_to_what_the_benchmark_harness_measured() {
    use deflate_arena::encoder::{Blocks, Coding, Huffman};
    use deflate_arena::parser::FnParser;
    use deflate_arena::stream::{self as arena_stream, StreamConfig};
    let coding = Coding { huffman: Huffman::Fast, blocks: Blocks::Adaptive };
    for level in Level::ALL {
        let p = FnParser { name: "level", f: level.parser() };
        for (name, data) in inputs() {
            // The scenarios' streaming setting: 1 MiB chunks, 4 KiB lookahead, adaptive blocks.
            let (want, _) = arena_stream::compress_stream(&p, &data, StreamConfig::new(1 << 20, coding), 65_536, None).unwrap();
            assert_eq!(deflate(&data, level), want, "{level:?} {name} stream");
            // The BGZF scenario: each block parsed whole.
            let want_bgzf = deflate_arena::container::bgzf(&data, |piece| {
                arena_stream::compress_whole(&p, piece, coding).map(|(r, _)| r)
            })
            .unwrap();
            assert_eq!(bgzf::compress(&data, level), want_bgzf, "{level:?} {name} bgzf");
        }
    }
}

#[test]
fn gzip_levels_map_like_gzip() {
    assert_eq!(Level::from_gzip(1), Level::Balanced);
    assert_eq!(Level::from_gzip(6), Level::High);
    assert_eq!(Level::from_gzip(9), Level::Max);
    assert_eq!(Level::default(), Level::High);
    assert_eq!([521, 85, 243], Level::ALL.map(|l| l.submission()));
}
