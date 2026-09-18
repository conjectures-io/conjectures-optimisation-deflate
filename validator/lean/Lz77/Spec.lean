import Aeneas
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Basic

/-!
# What a token stream means

This file is the **published contract**. It is written once by the operator,
pinned by hash, imported by every miner and edited by none of them. Everything
in it is pure Lean: it never mentions the extracted Rust, so it does not change
when a submission changes.

## The encoding

A token is a `u32`, and the encoding is *arithmetic* rather than bit-packed on
purpose — `Nat` `+`, `*`, `/` and `%` are what `omega` reasons about, whereas
`&&&` and `<<<` are not.

* `t < 256` — the literal byte `t`.
* `t = 2^24 + (dist-1)*256 + (len-3)` — copy `len` bytes from `dist` back,
  where `1 ≤ dist ≤ 32768` and `3 ≤ len ≤ 258`.

## The shape of the specification, and why it is this shape

The research phase measured that the *form* of a published contract is
worth roughly a factor of two in the proof that discharges it. The lever here is
`copyN`: rather than describing a back-reference as a list-valued function of the
window (which forces reasoning about slices of `List.set`), it describes it as
**the accumulator, extended one byte at a time**. That makes `copyN_take` below —
"a verified back-reference extends a prefix of the input to a longer prefix of the
input" — the single lemma a miner needs, and it turns their obligation into
`∀ k < len, input[pos - dist + k] = input[pos + k]`, which is exactly what a
match-length loop already computes.
-/

set_option maxRecDepth 8192

namespace LZ77

/-- Where the match tokens start. -/
def MATCH_BASE : Nat := 16777216

/-- Longest back-reference, in bytes. -/
def MAX_LEN : Nat := 258

/-- Furthest back a reference may reach. -/
def MAX_DIST : Nat := 32768

/-- One past the last legal token: `MATCH_BASE + MAX_DIST * 256`, written out
    because `simp only` unfolding a definition whose body is itself a product of
    two definitions does not terminate here. -/
def TOK_LIMIT : Nat := 25165824

def tokLen (t : Nat) : Nat := (t - MATCH_BASE) % 256 + 3
def tokDist (t : Nat) : Nat := (t - MATCH_BASE) / 256 + 1

/-- The token that copies `len` bytes from `dist` back. -/
def mkMatch (dist len : Nat) : Nat := MATCH_BASE + (dist - 1) * 256 + (len - 3)

/-- `copyN acc d n` is `acc` extended by `n` bytes, each taken `d` positions back
    from the *current* end. Bytes copied within this call are themselves visible
    to later bytes of it, which is what makes `dist < len` legal in DEFLATE. -/
def copyN (acc : List Nat) (d : Nat) : Nat → List Nat
  | 0 => acc
  | n + 1 => let a := copyN acc d n; a ++ [a[a.length - d]!]

/-- Decoding one token. `none` is a malformed stream. -/
def emit (acc : List Nat) (t : Nat) : Option (List Nat) :=
  if t < 256 then some (acc ++ [t])
  else if MATCH_BASE ≤ t ∧ t < TOK_LIMIT then
    let d := tokDist t
    let l := tokLen t
    if d ≤ acc.length then some (copyN acc d l) else none
  else none

/-- The decoder: RFC 1951's LZ77 layer, with the Huffman coding stripped off. -/
def decode (ts : List Nat) : Option (List Nat) := ts.foldlM emit []

/-- **The contract.** A token stream is valid for an input exactly when it
    decodes back to it. Nothing else is required of a submission: the search
    structure, the parse strategy and the block layout are entirely free. -/
def Valid (input : List Nat) (ts : List Nat) : Prop := decode ts = some input

end LZ77
