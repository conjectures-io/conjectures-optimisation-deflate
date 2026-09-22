import Lz77
import Slot

/-!
# The submission's proof

This file is what a **miner** writes. Everything it imports is fixed: `Lz77` is
the published contract and its lemmas, `Slot` is `charon`+`aeneas` output that the
verifier regenerates from the submitted `parse.rs` and never takes on trust.

The obligation is `parse_spec` at the bottom, whose statement is pinned by the
verifier. Nothing else in this file is checked, so a miner may restructure it
freely.
-/

namespace Submission
open Aeneas Aeneas.Std Result ControlFlow

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr
  Matches Found Pending emitted emitted_ge emitted_lt pending_of_found emit_lit emit_match)

/-! ## The hash

Nothing about correctness depends on what `hash3` computes, only that it lands in
range: a wrong hash finds a worse match, never an invalid one. That is the
property that lets a miner replace the whole search with anything they like. -/

@[local step]
theorem hash3_spec (a b c : Std.U8) :
    slot.hash3 a b c ⦃ fun h => h.val < 32768 ⦄ := by
  prove_hash3

/-! ## The match-length loop

The one function whose *result* the proof depends on. Its postcondition is
precisely the hypothesis `LZ77.valid_match` wants, which is why the rest of the
submission never mentions `copyN`. -/

theorem match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  prove_match_len_loop

@[local step]
theorem match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  prove_match_len

/-! ## The hash-insert loop

Pure bookkeeping: it writes into the search structure and nothing else, so its
postcondition is `True`. What still has to be proved is that it *terminates* and
never fails — which is the price of total correctness, and the reason a miner's
search structure is free but not free of obligations. -/

@[local step]
theorem parse_loop0_loop0_spec (input : Slice Std.U8)
    (head0 prev0 : Array Std.U32 32768#usize)
    (has30 : Bool) (lim «end» k0 : Std.Usize)
    (hlim : has30 = true → lim.val + 3 ≤ input.length) :
    slot.parse_loop0_loop0 input head0 prev0 has30 lim «end» k0
      ⦃ fun r => r.2.2 = true → lim.val + 3 ≤ input.length ⦄ := by
  rw [slot.parse_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «end».val - s.2.2.2.val)
    (inv := fun s => s.2.2.1 = true → lim.val + 3 ≤ input.length)
  · rintro ⟨hd, pv, h3, k⟩ hinv
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0_loop0.body]
    step*
  · exact hlim

/-! ## The search

`find_match` walks a hash chain. Its whole postcondition is `Found`, and `Found`
is also its loop invariant — which is the point of the design: a submission that
replaces this with a suffix automaton or an optimal parse rewrites *this lemma
only*, and everything below is untouched.

Note what is **not** proved: nothing says the chain is acyclic, nothing says
`prev` points anywhere sensible, and nothing says the match found is the best one.
The walk terminates because `probes` counts up, and a wrong candidate is harmless
because `match_len` compares the bytes.
-/

theorem find_match_loop_spec (input : Slice Std.U8) (prev : Slice Std.U32)
    (n pos cap bl0 bd0 cur0 probes0 : Std.Usize)
    (hn : n.val = input.length) (hprev : prev.length = 32768)
    (hcap : pos.val + cap.val ≤ n.val) (hcap258 : cap.val ≤ 258)
    (h0 : Found input n pos bl0 bd0) :
    slot.find_match_loop input prev pos cap bl0 bd0 cur0 probes0
      ⦃ fun r => Found input n pos r.1 r.2 ⦄ := by
  rw [slot.find_match_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.MAX_PROBES.val - s.2.2.2.val)
    (inv := fun s => Found input n pos s.1 s.2.1)
  · rintro ⟨bl, bd, cur, probes⟩ hinv
    simp only at hinv
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.find_match_loop.body]
    step*
    -- The window test is a `do` block behind an `if`, so it is cut off with its
    -- own postcondition — which is just `Found` again, one probe later.
    apply Std.WP.spec_bind (Pₘ := fun r => Found input n pos r.1 r.2.1)
    · split
      case isTrue hw =>
        step*
        rw [show ((if l > bl then ok (l, i) else ok (bl, bd))
              : Result (Std.Usize × Std.Usize))
            = ok (if l > bl then (l, i) else (bl, bd)) from by split <;> rfl]
        step*
        split
        case isTrue hbetter =>
          step*
          rcases Nat.lt_or_ge l.val 3 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h, by scalar_tac, by scalar_tac, by scalar_tac,
              by scalar_tac, by scalar_tac,
              by rw [show pos.val - i.val = cpos.val by scalar_tac]; exact l_post2⟩
        case isFalse =>
          -- the candidate was no better, so the invariant is carried through
          -- unchanged and `step*` closes it against `hinv` itself
          step*
      case isFalse => exact hinv
    · rintro ⟨bl1, bd1, cur1⟩ hf
      step*
  · exact h0

@[local step]
theorem find_match_spec (input : Slice Std.U8) (prev : Slice Std.U32)
    (n pos cap start : Std.Usize)
    (hn : n.val = input.length) (hprev : prev.length = 32768)
    (hcap : pos.val + cap.val ≤ n.val) (hcap258 : cap.val ≤ 258) :
    slot.find_match input prev pos cap start
      ⦃ fun r => Found input n pos r.1 r.2 ⦄ :=
  find_match_loop_spec input prev n pos cap 0#usize 0#usize start 0#usize
    hn hprev hcap hcap258 (Or.inl (by scalar_tac))

/-! ## The parse loop

The invariant is one line of English: *the tokens written so far decode to the
input consumed so far*. Everything else in it — `pos ≤ n`, `ntok ≤ pos`, the
buffer keeps its length — is bookkeeping that exists to make the writes legal. -/

theorem parse_loop0_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (n lim : Std.Usize) (head0 prev0 : Array Std.U32 32768#usize)
    (ntok0 pos0 : Std.Usize) (has30 : Bool)
    (hn : n.val = input.length)
    (hout : input.length ≤ out0.length)
    (hlim : has30 = true → lim.val + 3 ≤ input.length)
    (hpos : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.parse_loop0 input out0 n head0 prev0 ntok0 pos0 has30 lim ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
      LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.parse_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.2.1.val ≤ n.val ∧ s.2.2.2.1.val ≤ s.2.2.2.2.1.val ∧
      s.1.length = out0.length ∧
      (s.2.2.2.2.2 = true → lim.val + 3 ≤ input.length) ∧
      LZ77.decode (toks s.1 s.2.2.2.1.val) = some ((bytes input).take s.2.2.2.2.1.val))
  · rintro ⟨out, hd, pv, ntok, pos, h3⟩ ⟨hp, hnt, hlen, hh3, hde⟩
    simp only at hp hnt hlen hh3 hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0.body]
    split
    case isTrue hposlt =>
      -- `step*` will not enter a `do` block whose first statement is an `if`, so
      -- the search is cut off here with its own postcondition. That is also the
      -- right division of labour: `Found` is everything the emission needs to
      -- know, and it is all a *different* search would have to establish.
      apply Std.WP.spec_bind (Pₘ := fun (r : (Array Std.U32 32768#usize) ×
          (Array Std.U32 32768#usize) × Std.Usize × Std.Usize) =>
        Found input n pos r.2.2.1 r.2.2.2)
      · split
        case isTrue hb3 =>
          split
          case isTrue hpl =>
            have hlim3 : lim.val + 3 ≤ input.length := hh3 hb3
            have hposl : pos.val ≤ lim.val := by scalar_tac
            step*
            -- `if b then ok x else ok y` is a choice of *value*; `step*` needs
            -- it in that form before it will go on.
            rw [show ((if cap > 258#usize then ok 258#usize else ok cap)
                  : Result Std.Usize)
                = ok (if cap > 258#usize then 258#usize else cap) from by
                  split <;> rfl]
            step*
            -- `find_match`'s two range preconditions, on the capped length
            · split <;> scalar_tac
            · split <;> scalar_tac
          case isFalse => exact Or.inl (by scalar_tac)
        case isFalse => exact Or.inl (by scalar_tac)
      · rintro ⟨head1, prev1, best_len, best_dist⟩ hfound
        have hntok_lt : ntok.val < out.length := by scalar_tac
        have hlim3 : h3 = true → lim.val + 3 ≤ input.length := hh3
        replace hfound : Found input n pos best_len best_dist := hfound
        simp only [Found] at hfound
        step*
        -- Unfolding `Found` before `step*` is worth doing: its side-goal solver
        -- then case-splits the disjunction itself and discharges all five range
        -- obligations of the token encoding, leaving only the two invariants.
        -- The invariant, after emitting a match.
        · rcases hfound with _ | ⟨hl3, hlmax, hend, hd1, hdmax, hdpos, hmatch⟩
          · exfalso; scalar_tac
          have htok : i6.val = LZ77.mkMatch best_dist.val best_len.val := by
            simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i6_post, i3_post, i2_post,
              i5_post, i1_post, i4_post1, i_post1, Std.UScalar.cast_val_eq]
            scalar_tac
          refine ⟨by scalar_tac, by scalar_tac, by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, head2_post, ?_,
            by scalar_tac⟩
          rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
            toks_update out ntok i6 hntok_lt, htok,
            show «end».val = pos.val + best_len.val by scalar_tac]
          refine LZ77.valid_match (bytes input) (toks out ntok.val) pos.val
            best_dist.val best_len.val hde hd1 hdpos
            (by simpa [LZ77.MAX_DIST] using hdmax) hl3
            (by simpa [LZ77.MAX_LEN] using hlmax) (by rw [bytes_length]; scalar_tac) ?_
          intro k hk
          exact (bytes_congr input _ _ (by scalar_tac) (by scalar_tac)
            (hmatch k hk)).symm
        -- The invariant, after emitting a literal.
        · have hposlen : pos.val < input.length := by scalar_tac
          have hval : i1.val = (bytes input)[pos.val]! := by
            rw [bytes_getElem! input pos.val hposlen, i1_post,
              Std.U8.cast_U32_val_eq, i_post]
          refine ⟨by scalar_tac, by scalar_tac, by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, hlim3, ?_,
            by scalar_tac⟩
          rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
            toks_update out ntok i1 hntok_lt, hval,
            show pos1.val = pos.val + 1 by scalar_tac]
          exact LZ77.valid_lit (bytes input) (toks out ntok.val) pos.val hde
            (by rw [bytes_length]; scalar_tac) (by rw [← hval]; scalar_tac)
    case isFalse hge =>
      have hpn : pos.val = n.val := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      rw [hde, hpn, hn]
      simp
  · exact ⟨hpos, hntok, rfl, hlim, hdec⟩

/-! ## The obligation

This is the statement the verifier pins. A submission is accepted when *this*
theorem, with this statement, elaborates against a `Slot` the verifier generated
itself, and `#print axioms` on it shows nothing but Lean's own three.

Read it as: `parse` writes `ntok` tokens into `out`, does not disturb its length,
never fails and always terminates, and **the tokens it wrote decode back to the
input**. -/

theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.parse]
  apply Std.WP.spec_bind (Pₘ := fun r => r.1 = true → r.2.val + 3 ≤ input.length)
  · split
    case isTrue h3 =>
      have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
      step*
    case isFalse h3 =>
      intro hc; exact absurd hc (by simp)
  · rintro ⟨has3, lim⟩ hlim
    exact parse_loop0_spec input out (Std.Slice.len input) lim
      (Std.Array.repeat 32768#usize 0#u32) (Std.Array.repeat 32768#usize 0#u32)
      0#usize 0#usize has3
      (by simp) hlen hlim (by scalar_tac) (by scalar_tac)
      (by simp [toks, LZ77.decode])

end Submission
