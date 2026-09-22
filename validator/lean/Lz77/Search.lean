import Lz77.Lemmas
import Lz77.Interface

/-!
# The search library: what every parser proof shares

`Spec.lean` says what a token means and `Lemmas.lean` how one token steps the
decoder. This file is the layer above, written once so a submission's `Parse.lean`
is only the proof of its own emission:

* `Matches`, `Found`, `Pending`, `emitted`: the predicates every search and every
  lazy decision is stated with. A search proves `Found` and nothing else.
* `emit_lit`, `emit_match`, `Found.emit`: one token written into `out` steps the
  invariant "tokens so far decode to input so far". Each is `toks_update` plus the
  matching `valid_*` lemma plus the `bytes_congr` bookkeeping, folded.
* `prove_hash3`, `prove_match_len_loop`, `prove_match_len`: the proofs of the three
  search functions that every reference parser shares verbatim, as tactics. They
  expand against the `slot.*` the verifier extracted from the submission, so this
  file never imports `Slot` and is pinned like the rest of the contract.

Nothing here mentions a particular parser.
-/

namespace LZ77

open Aeneas Aeneas.Std

/-! ## Predicates -/

/-- `Matches input a b n`: the `n` bytes at `a` and at `b` agree. -/
def Matches (input : Slice Std.U8) (a b n : Nat) : Prop :=
  ∀ k, k < n → input.val[b + k]! = input.val[a + k]!

theorem Matches.zero (input : Slice Std.U8) (a b : Nat) : Matches input a b 0 := by
  intro k hk; simp at hk

theorem Matches.mono {input : Slice Std.U8} {a b n m : Nat}
    (h : Matches input a b n) (hm : m ≤ n) : Matches input a b m :=
  fun k hk => h k (by omega)

/-- One more agreeing byte extends a match by one. -/
theorem Matches.succ {input : Slice Std.U8} {a b n : Nat}
    (h : Matches input a b n) (heq : input.val[b + n]! = input.val[a + n]!) :
    Matches input a b (n + 1) := by
  intro k hk
  rcases Nat.lt_or_ge k n with hlt | hge
  · exact h k hlt
  · have : k = n := by omega
    subst this; exact heq

/-- Either nothing was found, or the `(length, distance)` is in range and its bytes were
    compared. Everything a search has to establish, and nothing else. -/
def Found (input : Slice Std.U8) (n pos best_len best_dist : Std.Usize) : Prop :=
  best_len.val < 3 ∨
    (3 ≤ best_len.val ∧ best_len.val ≤ 258 ∧ pos.val + best_len.val ≤ n.val ∧
      1 ≤ best_dist.val ∧ best_dist.val ≤ 32768 ∧ best_dist.val ≤ pos.val ∧
      Matches input (pos.val - best_dist.val) pos.val best_len.val)

/-- Nothing pending, or `(len, dist)` is `Found` at `pos - 1`: the state of a lazy parser. -/
def Pending (input : Slice Std.U8) (n pos len dist : Std.Usize) : Prop :=
  len.val < 3 ∨
    (1 ≤ pos.val ∧ 3 ≤ len.val ∧ len.val ≤ 258 ∧ (pos.val - 1) + len.val ≤ n.val ∧
      1 ≤ dist.val ∧ dist.val ≤ 32768 ∧ dist.val ≤ pos.val - 1 ∧
      Matches input (pos.val - 1 - dist.val) (pos.val - 1) len.val)

/-- The input prefix the tokens written so far decode to, when a match may be pending. -/
def emitted (pos len : Nat) : Nat := if 3 ≤ len then pos - 1 else pos

theorem emitted_ge {pos len : Nat} (h : 3 ≤ len) : emitted pos len = pos - 1 := by
  simp [emitted, h]

theorem emitted_lt {pos len : Nat} (h : len < 3) : emitted pos len = pos := by
  simp [emitted, Nat.not_le.mpr h]

/-- A match `Found` at `pos` is `Pending` at `pos + 1`. -/
theorem pending_of_found (input : Slice Std.U8) (n pos pos1 len dist : Std.Usize)
    (h1 : pos1.val = pos.val + 1) (hf : Found input n pos len dist) :
    Pending input n pos1 len dist := by
  rcases hf with h | ⟨hl3, hlmax, hend, hd1, hdmax, hdpos, hm⟩
  · exact Or.inl h
  · refine Or.inr ⟨by omega, hl3, hlmax, by omega, hd1, hdmax, by omega, ?_⟩
    rw [show pos1.val - 1 = pos.val by omega]
    exact hm

/-! ## A rewrite `step*` needs -/

/-- `step*` will not enter `if c then ok x else ok y`; as `ok (if c then x else y)` it will. -/
theorem ite_ok {α : Type} (c : Prop) [Decidable c] (x y : α) :
    (if c then Result.ok x else Result.ok y : Result α) = Result.ok (if c then x else y) := by
  split <;> rfl

/-! ## Writing one token -/

theorem bytes_lt_256 (input : Slice Std.U8) (pos : Nat) (hpos : pos < input.length) :
    (bytes input)[pos]! < 256 := by
  rw [bytes_getElem! input pos hpos]
  scalar_tac

/-- Writing the literal at `pos` into `out[ntok]` steps the invariant by one byte. -/
theorem emit_lit (input : Slice Std.U8) (out : Slice Std.U32) (ntok : Std.Usize) (pos : Nat)
    (v : Std.U32)
    (hde : decode (toks out ntok.val) = some ((bytes input).take pos))
    (hpos : pos < input.length) (hntok : ntok.val < out.length)
    (hv : v.val = (bytes input)[pos]!) :
    decode (toks (out.set ntok v) (ntok.val + 1)) = some ((bytes input).take (pos + 1)) := by
  rw [toks_update out ntok v hntok, hv]
  exact valid_lit (bytes input) (toks out ntok.val) pos hde (by rw [bytes_length]; exact hpos)
    (bytes_lt_256 input pos hpos)

/-- Writing the match `(d, L)` at `pos` into `out[ntok]` steps the invariant by `L` bytes.
    The hypotheses are exactly the second disjunct of `Found`, with `n = input.length`. -/
theorem emit_match (input : Slice Std.U8) (out : Slice Std.U32) (ntok : Std.Usize)
    (pos d L : Nat) (v : Std.U32)
    (hde : decode (toks out ntok.val) = some ((bytes input).take pos))
    (hntok : ntok.val < out.length)
    (hd1 : 1 ≤ d) (hdp : d ≤ pos) (hdmax : d ≤ 32768) (hl3 : 3 ≤ L) (hlmax : L ≤ 258)
    (hL : pos + L ≤ input.length) (hm : Matches input (pos - d) pos L)
    (hv : v.val = mkMatch d L) :
    decode (toks (out.set ntok v) (ntok.val + 1)) = some ((bytes input).take (pos + L)) := by
  rw [toks_update out ntok v hntok, hv]
  refine valid_match (bytes input) (toks out ntok.val) pos d L hde hd1 hdp
    (by simpa [MAX_DIST] using hdmax) hl3 (by simpa [MAX_LEN] using hlmax)
    (by rw [bytes_length]; exact hL) ?_
  intro k hk
  exact (bytes_congr input _ _ (by omega) (by omega) (hm k hk)).symm

/-- `emit_match` straight from a `Found` with a real match (`3 ≤ len`). -/
theorem Found.emit {input : Slice Std.U8} {n pos len dist : Std.Usize}
    (hf : Found input n pos len dist) (h3 : 3 ≤ len.val) (hn : n.val = input.length)
    (out : Slice Std.U32) (ntok : Std.Usize) (v : Std.U32)
    (hde : decode (toks out ntok.val) = some ((bytes input).take pos.val))
    (hntok : ntok.val < out.length) (hv : v.val = mkMatch dist.val len.val) :
    decode (toks (out.set ntok v) (ntok.val + 1)) =
      some ((bytes input).take (pos.val + len.val)) := by
  rcases hf with h | ⟨_, hlmax, hend, hd1, hdmax, hdpos, hm⟩
  · omega
  · exact emit_match input out ntok pos.val dist.val len.val v hde hntok hd1 hdpos hdmax h3 hlmax
      (by omega) hm hv

/-! ## The three search proofs every reference parser shares

They are tactics, not theorems, because their statements are about `slot.hash3`,
`slot.match_len_loop` and `slot.match_len`, which exist only once a submission has
been extracted. A parser that keeps the template's `hash3` and `match_len` verbatim
proves them with one line each; one that changes them writes its own. -/

set_option hygiene false in
/-- Proves `slot.hash3 a b c ⦃ fun h => h.val < 32768 ⦄` for the template's `hash3`. -/
macro "prove_hash3" : tactic => `(tactic| (rw [slot.hash3]; step*))

set_option hygiene false in
/-- Proves the template's `match_len_loop` spec: `l ≤ cap ∧ Matches input a b l`, from the
    invariant hypotheses `ha hb hl0 h0` in scope under those names. -/
macro "prove_match_len_loop" : tactic => `(tactic| (
  rw [slot.match_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ LZ77.Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    simp only [slot.match_len_loop.body]
    split
    case isTrue hlt =>
      have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
      step*
      all_goals first
        | scalar_tac
        | exact ⟨hle, hinv⟩
        | (refine ⟨by scalar_tac, ?_, by scalar_tac⟩
           rw [show l1.val = l.val + 1 by scalar_tac]
           apply LZ77.Matches.succ hinv
           rw [← i_post, ← i2_post, getElem!_pos _ _ (by scalar_tac),
             getElem!_pos _ _ (by scalar_tac), ← i1_post, ← i3_post]
           assumption)
    case isFalse => exact ⟨hle, hinv⟩
  · exact ⟨hl0, h0⟩))

set_option hygiene false in
/-- Proves `slot.match_len` from `match_len_loop_spec` in scope. -/
macro "prove_match_len" : tactic => `(tactic| (
  exact match_len_loop_spec input a b cap 0#usize ha hb (by scalar_tac)
    (LZ77.Matches.zero input a.val b.val)))

end LZ77
