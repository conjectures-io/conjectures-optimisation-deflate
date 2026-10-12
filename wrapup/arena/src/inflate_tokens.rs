//! An inflater that records the LZ77 tokens of a raw DEFLATE stream instead of
//! only its bytes, after Mark Adler's `puff.c`. Decoding another compressor's
//! output gives its parse, which can then be re-encoded with the shared encoder:
//! parser quality with the entropy coder held fixed.

use crate::token;

#[derive(Clone, Debug, Default, serde::Serialize)]
pub struct Blocks {
    pub stored: u64,
    pub fixed: u64,
    pub dynamic: u64,
}

pub struct Decoded {
    pub tokens: Vec<u32>,
    pub bytes: Vec<u8>,
    pub blocks: Blocks,
}

struct Bits<'a> {
    data: &'a [u8],
    pos: usize,
    acc: u64,
    n: u32,
}

impl<'a> Bits<'a> {
    fn need(&mut self, k: u32) -> Result<(), String> {
        while self.n < k {
            if self.pos >= self.data.len() {
                return Err("unexpected end of stream".to_string());
            }
            self.acc |= (self.data[self.pos] as u64) << self.n;
            self.pos += 1;
            self.n += 8;
        }
        Ok(())
    }

    fn get(&mut self, k: u32) -> Result<u32, String> {
        if k == 0 {
            return Ok(0);
        }
        self.need(k)?;
        let v = (self.acc & ((1u64 << k) - 1)) as u32;
        self.acc >>= k;
        self.n -= k;
        Ok(v)
    }

    fn align(&mut self) {
        let drop = self.n % 8;
        self.acc >>= drop;
        self.n -= drop;
    }
}

struct Huff {
    count: [u16; 16],
    symbol: Vec<u16>,
}

impl Huff {
    fn new(lengths: &[u8]) -> Result<Huff, String> {
        let mut count = [0u16; 16];
        for &l in lengths {
            count[l as usize] += 1;
        }
        let mut left: i32 = 1;
        for len in 1..16 {
            left <<= 1;
            left -= count[len] as i32;
            if left < 0 {
                return Err("over-subscribed code".to_string());
            }
        }
        let mut offs = [0u16; 16];
        for len in 1..15 {
            offs[len + 1] = offs[len] + count[len];
        }
        let mut symbol = vec![0u16; lengths.len()];
        for (sym, &l) in lengths.iter().enumerate() {
            if l != 0 {
                symbol[offs[l as usize] as usize] = sym as u16;
                offs[l as usize] += 1;
            }
        }
        Ok(Huff { count, symbol })
    }

    fn decode(&self, b: &mut Bits) -> Result<u16, String> {
        let (mut code, mut first, mut index) = (0i32, 0i32, 0i32);
        for len in 1..16 {
            code |= b.get(1)? as i32;
            let count = self.count[len] as i32;
            if code - count < first {
                return Ok(self.symbol[(index + (code - first)) as usize]);
            }
            index += count;
            first += count;
            first <<= 1;
            code <<= 1;
        }
        Err("invalid Huffman code".to_string())
    }
}

const LBASE: [u16; 29] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258,
];
const LEXT: [u8; 29] = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DBASE: [u16; 30] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577,
];
const DEXT: [u8; 30] = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];
const CL_ORDER: [usize; 19] = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

fn codes(b: &mut Bits, ll: &Huff, dl: &Huff, out: &mut Decoded) -> Result<(), String> {
    loop {
        let sym = ll.decode(b)? as usize;
        if sym < 256 {
            out.tokens.push(sym as u32);
            out.bytes.push(sym as u8);
        } else if sym == 256 {
            return Ok(());
        } else {
            let i = sym - 257;
            if i >= 29 {
                return Err("invalid length symbol".to_string());
            }
            let len = LBASE[i] as usize + b.get(LEXT[i] as u32)? as usize;
            let ds = dl.decode(b)? as usize;
            if ds >= 30 {
                return Err("invalid distance symbol".to_string());
            }
            let dist = DBASE[ds] as usize + b.get(DEXT[ds] as u32)? as usize;
            if dist > out.bytes.len() {
                return Err("distance before the start of the output".to_string());
            }
            out.tokens.push(token::encode_match(dist as u32, len as u32));
            let from = out.bytes.len() - dist;
            for k in 0..len {
                let v = out.bytes[from + k];
                out.bytes.push(v);
            }
        }
    }
}

/// Decode raw DEFLATE into its tokens and bytes. A stored block becomes literals.
pub fn decode(data: &[u8]) -> Result<Decoded, String> {
    let mut b = Bits { data, pos: 0, acc: 0, n: 0 };
    let mut out = Decoded { tokens: Vec::new(), bytes: Vec::new(), blocks: Blocks::default() };
    loop {
        let last = b.get(1)?;
        match b.get(2)? {
            0 => {
                b.align();
                let len = b.get(16)?;
                let nlen = b.get(16)?;
                if len != !nlen & 0xffff {
                    return Err("stored block length check failed".to_string());
                }
                for _ in 0..len {
                    let v = b.get(8)? as u8;
                    out.tokens.push(v as u32);
                    out.bytes.push(v);
                }
                out.blocks.stored += 1;
            }
            1 => {
                let mut l = [0u8; 288];
                for (i, x) in l.iter_mut().enumerate() {
                    *x = match i {
                        0..=143 => 8,
                        144..=255 => 9,
                        256..=279 => 7,
                        _ => 8,
                    };
                }
                let ll = Huff::new(&l)?;
                let dl = Huff::new(&[5u8; 30])?;
                codes(&mut b, &ll, &dl, &mut out)?;
                out.blocks.fixed += 1;
            }
            2 => {
                let nlen = b.get(5)? as usize + 257;
                let ndist = b.get(5)? as usize + 1;
                let ncode = b.get(4)? as usize + 4;
                let mut cl = [0u8; 19];
                for &idx in CL_ORDER.iter().take(ncode) {
                    cl[idx] = b.get(3)? as u8;
                }
                let clh = Huff::new(&cl)?;
                let mut lengths = vec![0u8; nlen + ndist];
                let mut i = 0;
                while i < nlen + ndist {
                    let sym = clh.decode(&mut b)?;
                    if sym < 16 {
                        lengths[i] = sym as u8;
                        i += 1;
                    } else {
                        let (v, rep) = match sym {
                            16 => {
                                if i == 0 {
                                    return Err("repeat with no previous length".to_string());
                                }
                                (lengths[i - 1], 3 + b.get(2)? as usize)
                            }
                            17 => (0, 3 + b.get(3)? as usize),
                            _ => (0, 11 + b.get(7)? as usize),
                        };
                        if i + rep > nlen + ndist {
                            return Err("too many code lengths".to_string());
                        }
                        for x in &mut lengths[i..i + rep] {
                            *x = v;
                        }
                        i += rep;
                    }
                }
                let ll = Huff::new(&lengths[..nlen])?;
                let dl = Huff::new(&lengths[nlen..])?;
                codes(&mut b, &ll, &dl, &mut out)?;
                out.blocks.dynamic += 1;
            }
            _ => return Err("invalid block type".to_string()),
        }
        if last == 1 {
            return Ok(out);
        }
    }
}
