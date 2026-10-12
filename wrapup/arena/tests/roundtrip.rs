//! The adapters and encoder against the pinned encoder and three inflaters.

use deflate_arena::encoder::{self, Encoder, Flush, Huffman};
use deflate_arena::parser::Parser;
use deflate_arena::stream::{self, StreamConfig};
use deflate_arena::{builtin, container, inflate_tokens, pinned, reference, verify};
use std::path::Path;

fn lcg(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *seed >> 33
}

/// Real text from this repository plus synthetic shapes that stress boundaries.
fn inputs() -> Vec<(String, Vec<u8>)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut text = Vec::new();
    for rel in [
        "docs/SCORING.md",
        "docs/OPERATIONS.md",
        "miner/MANUAL.md",
        "validator/measure/src/deflate.rs",
        "validator/measure/src/main.rs",
        "miner/examples/optimal-iter/parse.rs",
        "docs/CORPUS-SOURCES.md",
    ] {
        text.extend(std::fs::read(root.join(rel)).expect(rel));
    }
    let mut s = 42u64;
    let random: Vec<u8> = (0..70_000).map(|_| lcg(&mut s) as u8).collect();
    // Repeats at distances just under and over the window.
    let mut far = random[..40_000].to_vec();
    far.extend_from_slice(&random[..40_000]);
    let mut mixed = Vec::new();
    for i in 0..4000u32 {
        mixed.extend_from_slice(&i.to_le_bytes());
        mixed.extend_from_slice(b"id,");
        if i % 7 == 0 {
            mixed.extend_from_slice(&text[(i as usize * 37) % 5000..(i as usize * 37) % 5000 + 60]);
        }
    }
    let mut big = Vec::new();
    while big.len() < 600_000 {
        big.extend_from_slice(&text);
        big.extend_from_slice(&mixed[..10_000]);
    }
    vec![
        ("empty".into(), Vec::new()),
        ("one".into(), b"a".to_vec()),
        ("two".into(), b"ab".to_vec()),
        ("zeros".into(), vec![0u8; 200_000]),
        ("text".into(), text),
        ("random".into(), random),
        ("far".into(), far),
        ("mixed".into(), mixed),
        ("big".into(), big),
    ]
}

fn tokens(p: &dyn Parser, data: &[u8]) -> Vec<u32> {
    let mut t = vec![0u32; data.len()];
    let n = p.parse(data, &mut t).unwrap();
    t.truncate(n);
    t
}

#[test]
fn incremental_encoder_is_byte_identical_to_pinned() {
    let mut s = 1u64;
    for p in builtin::all() {
        for (name, data) in inputs() {
            let t = tokens(&p, &data);
            let want = pinned::encode(&t, data.len()).unwrap();
            for h in [Huffman::Pinned, Huffman::Fast] {
                assert_eq!(encoder::encode(&t, data.len(), h).unwrap(), want, "{} {name} {h:?}", p.name);
                // Arbitrary batches, output taken as it comes.
                let mut e = Encoder::new(h);
                let mut out = Vec::new();
                let mut i = 0;
                while i < t.len() {
                    let k = (1 + lcg(&mut s) as usize % 40_000).min(t.len() - i);
                    e.push(&t[i..i + k]).unwrap();
                    out.extend(e.take());
                    i += k;
                }
                e.finish();
                out.extend(e.take());
                assert_eq!(out, want, "{} {name} {h:?} batched", p.name);
            }
        }
    }
}

#[test]
fn history_stream_round_trips() {
    let mut s = 9u64;
    let parsers = builtin::all();
    for (name, data) in inputs() {
        for p in &parsers {
            for chunk in [1usize, 300, 5_000, 70_000, 1 << 20] {
                // Each call parses up to 36 KiB of history and lookahead, so tiny
                // chunks only on small inputs.
                if data.len() / chunk > 200 {
                    continue;
                }
                let mut cfg = StreamConfig::new(chunk, Huffman::Fast);
                cfg.lookahead = [258usize, 4096][(lcg(&mut s) % 2) as usize];
                let write = 1 + lcg(&mut s) as usize % 100_000;
                let flush = if lcg(&mut s) % 3 == 0 { Some(1 + lcg(&mut s) as usize % 200_000) } else { None };
                let (out, st) = stream::compress_stream(p, &data, cfg, write, flush)
                    .unwrap_or_else(|e| panic!("{} {name} chunk {chunk}: {e}", p.name()));
                verify::raw(&out, &data)
                    .unwrap_or_else(|e| panic!("{} {name} chunk {chunk} write {write} flush {flush:?}: {e}", p.name()));
                assert!(st.parsed_bytes >= data.len() as u64);
            }
        }
    }
}

#[test]
fn a_large_chunk_stream_equals_the_whole_buffer() {
    // With one chunk covering everything, the stream is the whole-buffer parse.
    for p in builtin::all() {
        for (name, data) in inputs() {
            let (whole, _) = stream::compress_whole(&p, &data, Huffman::Fast).unwrap();
            let cfg = StreamConfig::new(data.len().max(1) + 10, Huffman::Fast);
            let (st, _) = stream::compress_stream(&p, &data, cfg, data.len().max(1), None).unwrap();
            assert_eq!(st, whole, "{} {name}", p.name);
        }
    }
}

#[test]
fn independent_chunks_and_containers_round_trip() {
    let p = builtin::by_name("incumbent").unwrap();
    for (name, data) in inputs() {
        let (members, _) = stream::compress_independent(&p, &data, 65_280, Huffman::Fast, true).unwrap();
        let pieces: Vec<&[u8]> = if data.is_empty() { vec![&data[..]] } else { data.chunks(65_280).collect() };
        assert_eq!(members.len(), pieces.len());
        for (m, piece) in members.iter().zip(&pieces) {
            verify::raw(m, piece).unwrap();
        }
        let (one, _) = stream::compress_independent(&p, &data, 50_000, Huffman::Fast, false).unwrap();
        verify::raw(&one[0], &data).unwrap_or_else(|e| panic!("{name} full-flush: {e}"));

        let (raw, _) = stream::compress_whole(&p, &data, Huffman::Fast).unwrap();
        verify::gzip(&container::gzip(&raw, &data), &data).unwrap();
        verify::zlib(&container::zlib(&raw, &data), &data).unwrap();
        let bgzf = container::bgzf(&data, |piece| {
            stream::compress_whole(&p, piece, Huffman::Fast).map(|(r, _)| r)
        })
        .unwrap();
        verify::gzip(&bgzf, &data).unwrap_or_else(|e| panic!("{name} bgzf: {e}"));
        assert!(bgzf.ends_with(&container::BGZF_EOF));
    }
}

#[test]
fn token_extraction_recovers_our_parse_and_reads_other_encoders() {
    let p = builtin::by_name("optimal-iter").unwrap();
    for (name, data) in inputs() {
        let t = tokens(&p, &data);
        let raw = encoder::encode(&t, data.len(), Huffman::Fast).unwrap();
        let d = inflate_tokens::decode(&raw).unwrap();
        assert_eq!(d.bytes, data, "{name}");
        assert_eq!(d.tokens, t, "{name}: tokens differ after a round trip");

        for r in ["zlib-6", "libdeflate-12", "miniz_oxide-9", "zopfli-i1"] {
            let reference = reference::Reference::parse(r).unwrap();
            let theirs = reference.compress(&data).unwrap();
            verify::raw(&theirs, &data).unwrap();
            let d = inflate_tokens::decode(&theirs).unwrap_or_else(|e| panic!("{r} {name}: {e}"));
            assert_eq!(d.bytes, data, "{r} {name}");
            // Their parse through our encoder is still a valid stream.
            let ours = encoder::encode(&d.tokens, data.len(), Huffman::Fast).unwrap();
            verify::raw(&ours, &data).unwrap();
        }
    }
}

#[test]
fn zlib_stream_reference_round_trips_with_flushes() {
    for (name, data) in inputs() {
        for flush in [None, Some(4096), Some(65_536)] {
            let out = reference::zlib_stream(&data, 6, 4096, flush).unwrap();
            verify::raw(&out, &data).unwrap_or_else(|e| panic!("{name} {flush:?}: {e}"));
        }
    }
}

#[test]
fn a_sync_flush_ends_on_the_zlib_marker() {
    let p = builtin::by_name("incumbent").unwrap();
    let data = inputs().into_iter().find(|(n, _)| n == "text").unwrap().1;
    let mut c = stream::HistoryCompressor::new(&p, StreamConfig::new(10_000, Huffman::Fast));
    c.write(&data[..30_000]).unwrap();
    c.flush(Flush::Sync).unwrap();
    let mut out = c.take();
    assert!(out.ends_with(&[0, 0, 0xff, 0xff]));
    // Everything written so far decodes before the stream ends.
    let mut d = flate2::Decompress::new(false);
    let mut got = Vec::with_capacity(40_000);
    d.decompress_vec(&out, &mut got, flate2::FlushDecompress::Sync).unwrap();
    assert_eq!(&got[..], &data[..30_000]);
    c.write(&data[30_000..]).unwrap();
    c.finish().unwrap();
    out.extend(c.take());
    verify::raw(&out, &data).unwrap();
}

#[test]
fn adaptive_blocks_round_trip_and_do_not_grow_the_output() {
    use deflate_arena::encoder::{Blocks, Coding};
    let adaptive = Coding { huffman: Huffman::Fast, blocks: Blocks::Adaptive };
    let (mut fixed_total, mut adaptive_total) = (0usize, 0usize);
    for p in builtin::all() {
        for (name, data) in inputs() {
            let t = tokens(&p, &data);
            let a = encoder::encode_with(&t, data.len(), Huffman::Fast, Blocks::Adaptive).unwrap();
            verify::raw(&a, &data).unwrap_or_else(|e| panic!("{} {name}: {e}", p.name));
            // The split only moves block boundaries: the parse is unchanged.
            assert_eq!(inflate_tokens::decode(&a).unwrap().tokens, t, "{} {name}", p.name);
            fixed_total += encoder::encode(&t, data.len(), Huffman::Fast).unwrap().len();
            adaptive_total += a.len();

            let cfg = StreamConfig::new(70_000, adaptive);
            let (s, _) = stream::compress_stream(&p, &data, cfg, 30_000, Some(150_000)).unwrap();
            verify::raw(&s, &data).unwrap_or_else(|e| panic!("{} {name} stream: {e}", p.name));
            let (one, _) = stream::compress_independent(&p, &data, 50_000, adaptive, false).unwrap();
            verify::raw(&one[0], &data).unwrap_or_else(|e| panic!("{} {name} independent: {e}", p.name));
        }
    }
    assert!(adaptive_total < fixed_total, "adaptive {adaptive_total} vs fixed {fixed_total}");
    eprintln!("adaptive {adaptive_total} vs fixed {fixed_total}");
}

#[test]
fn messages_decode_one_by_one_with_any_window() {
    let data = inputs().into_iter().find(|(n, _)| n == "text").unwrap().1;
    let msgs = stream::lines(&data);
    assert!(msgs.len() > 100);
    for p in builtin::all() {
        for wbits in [9u8, 12, 15] {
            let mut cfg = StreamConfig::new(1 << 20, Huffman::Fast);
            cfg.window = 1 << wbits;
            let (out, _) = stream::compress_messages(&p, &msgs, cfg).unwrap();
            verify::raw(&out, &data).unwrap_or_else(|e| panic!("{} w{wbits}: {e}", p.name));
            // Every distance fits the negotiated window.
            let d = inflate_tokens::decode(&out).unwrap();
            for &t in &d.tokens {
                if let deflate_arena::token::Token::Match { dist, .. } = deflate_arena::token::decode(t) {
                    assert!(dist as usize <= 1 << wbits, "{} w{wbits}: distance {dist}", p.name);
                }
            }
        }
    }
    for wbits in [9u8, 15] {
        let out = reference::zlib_messages(&msgs, 6, wbits).unwrap();
        verify::raw(&out, &data).unwrap();
    }
}

#[test]
fn png_idat_recompression_keeps_the_scanlines() {
    use deflate_arena::png;
    // A 64x48 RGB image, filter 0 on every row, built by hand.
    let (w, h) = (64u32, 48u32);
    let mut scan = Vec::new();
    for y in 0..h {
        scan.push(0u8);
        for x in 0..w {
            scan.extend_from_slice(&[(x * 4) as u8, (y * 5) as u8, ((x ^ y) * 3) as u8]);
        }
    }
    let chunk = |kind: &[u8], body: &[u8]| {
        let mut c = (body.len() as u32).to_be_bytes().to_vec();
        c.extend_from_slice(kind);
        c.extend_from_slice(body);
        let mut crc = crc32fast::Hasher::new();
        crc.update(kind);
        crc.update(body);
        c.extend_from_slice(&crc.finalize().to_be_bytes());
        c
    };
    let mut ihdr = w.to_be_bytes().to_vec();
    ihdr.extend_from_slice(&h.to_be_bytes());
    ihdr.extend_from_slice(&[8, 2, 0, 0, 0]);
    let zl = miniz_oxide::deflate::compress_to_vec_zlib(&scan, 1);
    let mut file = png::SIGNATURE.to_vec();
    file.extend(chunk(b"IHDR", &ihdr));
    file.extend(chunk(b"IDAT", &zl[..zl.len() / 2]));
    file.extend(chunk(b"IDAT", &zl[zl.len() / 2..]));
    file.extend(chunk(b"IEND", b""));

    let img = png::parse(&file).unwrap();
    assert_eq!(img.scanlines().unwrap(), scan);
    let p = builtin::by_name("optimal-iter").unwrap();
    let (raw, _) = stream::compress_whole(&p, &scan, Huffman::Fast).unwrap();
    let out = img.with_idat(&container::zlib(&raw, &scan));
    let again = png::parse(&out).unwrap();
    assert_eq!(again.scanlines().unwrap(), scan);
    assert_eq!(again.head.len(), 1);
    assert_eq!(again.tail.len(), 1);
}
