import Lz77.Spec

/-!
# The lemmas a submission actually uses

Two of them, `valid_lit` and `valid_match`, and between them they are the whole
per-patch interface to the contract. A miner's proof carries a loop invariant of
the form *"the tokens written so far decode to the prefix of the input consumed
so far"* and steps it with one of these at each emission.

This file is the substrate's investment and it is paid once.
-/

set_option maxRecDepth 8192

namespace LZ77

theorem getElem!_take {α : Type} [Inhabited α] (l : List α) (n i : Nat) (h : i < n) :
    (l.take n)[i]! = l[i]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt h]

@[simp] theorem copyN_length (acc : List Nat) (d n : Nat) :
    (copyN acc d n).length = acc.length + n := by
  induction n with
  | zero => simp [copyN]
  | succ m ih => simp [copyN, ih]; omega

/-- **The lemma.** A back-reference whose bytes have actually been compared
    extends a prefix of the input to a longer prefix of the input.

    The hypothesis is exactly the postcondition of a match-length loop, which is
    why a submission never has to reason about `copyN` itself. -/
theorem copyN_take (input : List Nat) (pos d : Nat) (hd1 : 1 ≤ d) (hdp : d ≤ pos) :
    ∀ L, pos + L ≤ input.length →
      (∀ k, k < L → input[pos - d + k]! = input[pos + k]!) →
      copyN (input.take pos) d L = input.take (pos + L) := by
  intro L
  induction L with
  | zero => intro _ _; simp [copyN]
  | succ m ih =>
    intro hL hm
    have ihm := ih (by omega) (fun k hk => hm k (by omega))
    have hlt : pos + m < input.length := by omega
    have hlen2 : (input.take (pos + m)).length = pos + m := by
      rw [List.length_take]; omega
    rw [copyN]
    simp only [ihm, hlen2]
    have hidx : pos + m - d = pos - d + m := by omega
    rw [hidx, getElem!_take input (pos + m) (pos - d + m) (by omega), hm m (by omega),
        show pos + (m + 1) = pos + m + 1 by omega, List.take_add_one,
        List.getElem?_eq_getElem hlt]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]

theorem decode_snoc (ts : List Nat) (t : Nat) :
    decode (ts ++ [t]) = (decode ts).bind (fun acc => emit acc t) := by
  simp [decode, List.foldlM_append]

/-- Emitting a literal steps the invariant. -/
theorem valid_lit (input : List Nat) (ts : List Nat) (pos : Nat)
    (hd : decode ts = some (input.take pos))
    (hpos : pos < input.length) (hb : input[pos]! < 256) :
    decode (ts ++ [input[pos]!]) = some (input.take (pos + 1)) := by
  rw [decode_snoc, hd]
  simp only [Option.bind_some, emit, if_pos hb]
  rw [List.take_add_one, List.getElem?_eq_getElem hpos]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hpos]

/-- Emitting a verified back-reference steps the invariant. The last hypothesis
    is the postcondition of the match-length loop; the rest are range checks. -/
theorem valid_match (input : List Nat) (ts : List Nat) (pos d L : Nat)
    (hd : decode ts = some (input.take pos))
    (hd1 : 1 ≤ d) (hdp : d ≤ pos) (hdmax : d ≤ MAX_DIST)
    (hl3 : 3 ≤ L) (hlmax : L ≤ MAX_LEN) (hL : pos + L ≤ input.length)
    (hm : ∀ k, k < L → input[pos - d + k]! = input[pos + k]!) :
    decode (ts ++ [mkMatch d L]) = some (input.take (pos + L)) := by
  have hdmax' : d ≤ 32768 := by simpa [MAX_DIST] using hdmax
  have hlmax' : L ≤ 258 := by simpa [MAX_LEN] using hlmax
  have hlen : (input.take pos).length = pos := by rw [List.length_take]; omega
  have hbase : MATCH_BASE ≤ mkMatch d L := by
    simp only [mkMatch]; omega
  have hlimit : mkMatch d L < TOK_LIMIT := by
    simp only [mkMatch, TOK_LIMIT, MATCH_BASE]; omega
  have hnotlit : ¬ (mkMatch d L < 256) := by
    simp only [mkMatch, MATCH_BASE]; omega
  have hsub : mkMatch d L - MATCH_BASE = (d - 1) * 256 + (L - 3) := by
    simp only [mkMatch]; omega
  -- `omega` knows `/` and `%` by a literal, which is the whole reason the token
  -- encoding is arithmetic rather than bit-packed.
  have hdist : tokDist (mkMatch d L) = d := by simp only [tokDist, hsub]; omega
  have hlenT : tokLen (mkMatch d L) = L := by simp only [tokLen, hsub]; omega
  rw [decode_snoc, hd]
  simp only [Option.bind_some, emit, if_neg hnotlit, hdist, hlenT, hlen, if_pos hdp]
  rw [copyN_take input pos d hd1 hdp L hL hm]
  exact if_pos (And.intro hbase hlimit)

end LZ77
