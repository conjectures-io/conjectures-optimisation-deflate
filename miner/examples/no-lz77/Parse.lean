import Lz77
import Slot

/-!
The smallest complete proof: a parser that writes every byte as a literal. One loop,
one token-writing site, and the one invariant every parser proof has:

    the tokens written so far decode to the input consumed so far.

Everything a search would need (`Found`, `match_len`, the emission of a match) is
absent here, which is the point: read this first, then `miner/template` for the
match site, then `lazy` for a pending match, then `optimal` for a re-verified DP.
-/

namespace Submission
open Aeneas Aeneas.Std Result ControlFlow

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open LZ77 (toks bytes bytes_getElem! emit_lit)

/-! ## The loop

State `(out, i)`. The invariant carries `i ≤ n` (the measure `n - i` decreases),
the buffer's length (so the next write is in bounds), and the decode fact. -/

theorem parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n i0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hi : i0.val ≤ n.val)
    (hdec : LZ77.decode (toks out0 i0.val) = some ((bytes input).take i0.val)) :
    slot.parse_loop input out0 n i0 ⦃ fun r =>
      r.length = out0.length ∧ LZ77.decode (toks r n.val) = some (bytes input) ⦄ := by
  rw [slot.parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.val)
    (inv := fun s =>
      s.2.val ≤ n.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.val) = some ((bytes input).take s.2.val))
  · rintro ⟨out, i⟩ ⟨hle, hlen, hde⟩
    simp only at hle hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop.body]
    split
    case isTrue hlt =>
      -- one literal: `input[i]` cast to `u32`, written at `out[i]`
      step*
      have hval : i2.val = (bytes input)[i.val]! := by
        rw [bytes_getElem! input i.val (by scalar_tac), i2_post, Std.U8.cast_U32_val_eq, i1_post]
      refine ⟨by scalar_tac, by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_,
        by scalar_tac⟩
      rw [s_post, show i3.val = i.val + 1 by scalar_tac]
      exact emit_lit input out i i.val i2 hde (by scalar_tac) (by scalar_tac) hval
    case isFalse hge =>
      -- `i = n`: the tokens decode to the whole input
      refine ⟨hlen, ?_⟩
      rw [show n.val = i.val by scalar_tac, hde, show i.val = (bytes input).length by
        rw [LZ77.bytes_length]; scalar_tac]
      simp
  · exact ⟨hi, rfl, hdec⟩

/-! ## The obligation -/

theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.parse]
  apply Std.WP.spec_bind (parse_loop_spec input out (Std.Slice.len input) 0#usize
    (by simp) hlen (by scalar_tac) (by simp [toks, LZ77.decode]))
  intro out1 ⟨hlen1, hdec⟩
  step*
  exact ⟨by simp, hlen1, hdec⟩

end Submission
