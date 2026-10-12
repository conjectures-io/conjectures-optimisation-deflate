//! Randomised stress test of the streaming adapters: `cargo run --release --example stress -- SECONDS`.
use deflate_arena::encoder::{Blocks, Coding, Flush, Huffman};
use deflate_arena::stream::{self, HistoryCompressor, StreamConfig};
use deflate_arena::{builtin, verify};
use std::time::{Duration, Instant};

fn rng(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

fn input(s: &mut u64) -> Vec<u8> {
    let n = (rng(s) % 400_000) as usize;
    let mut v = Vec::with_capacity(n);
    let words: [&[u8]; 6] = [b"the ", b"parser ", b"window ", b"\n", b"0123", b"match "];
    while v.len() < n {
        match rng(s) % 5 {
            0 => v.extend_from_slice(words[(rng(s) % 6) as usize]),
            1 => {
                let b = rng(s) as u8;
                v.extend(std::iter::repeat(b).take((rng(s) % 300) as usize));
            }
            2 => {
                // Copy from far back, sometimes beyond the window.
                if v.len() > 10 {
                    let d = 1 + (rng(s) as usize % v.len().min(70_000));
                    let l = (rng(s) % 600) as usize;
                    for _ in 0..l {
                        let b = v[v.len() - d];
                        v.push(b);
                    }
                }
            }
            _ => v.push(rng(s) as u8),
        }
    }
    v.truncate(n);
    v
}

fn main() {
    let secs: u64 = std::env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(60);
    let end = Instant::now() + Duration::from_secs(secs);
    let parsers = builtin::all();
    let mut s = 0x9e3779b97f4a7c15u64;
    let mut cases = 0u64;
    while Instant::now() < end {
        let data = input(&mut s);
        let p = &parsers[(rng(&mut s) % parsers.len() as u64) as usize];
        let coding = Coding {
            huffman: Huffman::Fast,
            blocks: if rng(&mut s) % 2 == 0 { Blocks::Fixed } else { Blocks::Adaptive },
        };
        let mut cfg = StreamConfig::new(1 + (rng(&mut s) % 200_000) as usize, coding);
        cfg.lookahead = 258 + (rng(&mut s) % 8000) as usize;
        cfg.window = 1 << (9 + rng(&mut s) % 7);
        let mut c = HistoryCompressor::new(p, cfg);
        let mut out = Vec::new();
        let mut pos = 0;
        let mut full_flush_at = Vec::new();
        while pos < data.len() {
            let k = (1 + rng(&mut s) % 50_000) as usize;
            let k = k.min(data.len() - pos);
            c.write(&data[pos..pos + k]).unwrap();
            pos += k;
            match rng(&mut s) % 10 {
                0 => c.flush(Flush::Sync).unwrap(),
                1 => {
                    c.flush(Flush::Full).unwrap();
                    full_flush_at.push(pos);
                }
                _ => {}
            }
            out.extend(c.take());
        }
        c.finish().unwrap();
        out.extend(c.take());
        if let Err(e) = verify::raw(&out, &data) {
            panic!("case {cases}: {} chunk {} look {} window {} len {}: {e}", p.name, cfg.chunk, cfg.lookahead, cfg.window, data.len());
        }
        let (ind, _) = stream::compress_independent(p, &data, 1 + (rng(&mut s) % 100_000) as usize, coding, false).unwrap();
        verify::raw(&ind[0], &data).unwrap();
        cases += 1;
    }
    println!("{cases} random cases passed in {secs} s");
}
