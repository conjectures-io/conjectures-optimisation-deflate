import Lz77
import Slot

namespace Submission
open Aeneas Aeneas.Std Result ControlFlow
open LZ77 (toks bytes)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace EA
open Aeneas Aeneas.Std Result ControlFlow
open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr Matches emit_lit emit_match ite_ok)
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

def AMatchAt (s : Slice Std.U8) (p l d : Nat) : Prop :=
  3 ≤ l ∧ l ≤ 258 ∧ p + l ≤ s.length ∧ 1 ≤ d ∧ d ≤ 32768 ∧ d ≤ p ∧ Matches s (p - d) p l

theorem a_copyN_take_prefix (acc : List Nat) (d : Nat) :
    ∀ n, (LZ77.copyN acc d n).take acc.length = acc := by
  intro n
  induction n with
  | zero => simp [LZ77.copyN]
  | succ m ih =>
    simp only [LZ77.copyN]
    rw [List.take_append_of_le_length (by simp)]
    exact ih

theorem a_foldlM_emit_length : ∀ (ts : List Nat) (init acc : List Nat),
    ts.foldlM LZ77.emit init = some acc → init.length + ts.length ≤ acc.length := by
  intro ts
  induction ts with
  | nil => intro init acc h; simp at h; subst h; simp
  | cons t ts ih =>
    intro init acc h
    simp only [List.foldlM_cons] at h
    cases he : LZ77.emit init t with
    | none => rw [he] at h; simp at h
    | some a =>
      rw [he] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      have h1 := ih a acc h
      have h2 : init.length + 1 ≤ a.length := by
        simp only [LZ77.emit] at he
        split at he
        · simp at he; subst he; simp
        · split at he
          · split at he
            · simp at he; subst he; rw [LZ77.copyN_length]; simp only [LZ77.tokLen]; omega
            · simp at he
          · simp at he
      simp only [List.length_cons]
      omega

theorem a_decode_length_le {ts acc : List Nat} (h : LZ77.decode ts = some acc) :
    ts.length ≤ acc.length := by
  have := a_foldlM_emit_length ts [] acc h
  simpa using this

theorem a_decode_pop_lit {ts : List Nat} {t : Nat} {inp : List Nat} {p : Nat}
    (hp : p ≤ inp.length) (hd : LZ77.decode (ts ++ [t]) = some (inp.take p)) (ht : t < 256) :
    1 ≤ p ∧ LZ77.decode ts = some (inp.take (p - 1)) := by
  rw [LZ77.decode_snoc] at hd
  cases hts : LZ77.decode ts with
  | none => rw [hts] at hd; simp at hd
  | some acc =>
    rw [hts] at hd
    simp only [Option.bind_some, LZ77.emit, if_pos ht] at hd
    have hacc : acc ++ [t] = inp.take p := Option.some.inj hd
    have hlen : acc.length + 1 = p := by
      have := congrArg List.length hacc
      simp [List.length_take] at this; omega
    refine ⟨by omega, ?_⟩
    apply congrArg some
    have := congrArg (List.take acc.length) hacc
    rw [List.take_append_of_le_length (le_refl _), List.take_length, List.take_take] at this
    rw [this, show min acc.length p = p - 1 by omega]

theorem a_decode_pop_match {ts : List Nat} {t : Nat} {inp : List Nat} {p : Nat}
    (hp : p ≤ inp.length) (hd : LZ77.decode (ts ++ [t]) = some (inp.take p)) (ht : 256 ≤ t) :
    LZ77.tokLen t ≤ p ∧ LZ77.decode ts = some (inp.take (p - LZ77.tokLen t)) := by
  rw [LZ77.decode_snoc] at hd
  cases hts : LZ77.decode ts with
  | none => rw [hts] at hd; simp at hd
  | some acc =>
    rw [hts] at hd
    simp only [Option.bind_some, LZ77.emit, if_neg (show ¬ t < 256 by omega)] at hd
    split at hd
    · split at hd
      · have hacc : LZ77.copyN acc (LZ77.tokDist t) (LZ77.tokLen t) = inp.take p := Option.some.inj hd
        have hlen : acc.length + LZ77.tokLen t = p := by
          have := congrArg List.length hacc
          simp [List.length_take] at this; omega
        refine ⟨by omega, ?_⟩
        apply congrArg some
        have := congrArg (List.take acc.length) hacc
        rw [a_copyN_take_prefix, List.take_take] at this
        rw [this, show min acc.length p = p - LZ77.tokLen t by omega]
      · simp at hd
    · simp at hd

theorem a_toks_pop (out : Slice Std.U32) (nt : Nat) (h0 : 0 < nt) (hle : nt ≤ out.length) :
    toks out nt = toks out (nt - 1) ++ [(out.val[nt - 1]!).val] := by
  have hlt : nt - 1 < out.val.length := by
    have : out.length = out.val.length := rfl
    omega
  simp only [toks]
  conv_lhs => rw [show nt = (nt - 1) + 1 by omega]
  rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append]
  simp [getElem!_pos out.val (nt - 1) hlt]

theorem a_toks_length (out : Slice Std.U32) (nt : Nat) (h : nt ≤ out.length) :
    (toks out nt).length = nt := by
  simp only [toks, List.length_map, List.length_take]
  have : out.length = out.val.length := rfl
  omega

def ADec (s : Slice Std.U8) (out : Slice Std.U32) (nt p : Nat) : Prop :=
  p ≤ s.length ∧ nt ≤ p ∧ s.length ≤ out.length ∧
    LZ77.decode (toks out nt) = some ((bytes s).take p)

theorem ADec.init (input : Slice Std.U8) (out : Slice Std.U32) (h : input.length ≤ out.length) :
    ADec input out (0#usize).val (0#usize).val :=
  ⟨by simp, by simp, h, by simp [toks, LZ77.decode]⟩

theorem ADec.lit {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat} (h : ADec s out nt p)
    (hp : p < s.length) (ntU : Std.Usize) (hnt : ntU.val = nt) (v : Std.U32)
    (hv : v.val = (s.val[p]!).val) :
    ADec s (out.set ntU v) (nt + 1) (p + 1) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  have hntl : ntU.val < out.length := by omega
  refine ⟨by omega, by omega, by rw [Std.Slice.set_length]; exact hso, ?_⟩
  rw [← hnt]
  refine emit_lit s out ntU p v (by rw [hnt]; exact hde) hp hntl ?_
  have hpl : p < s.val.length := hp
  rw [hv, bytes_getElem! s p hpl, getElem!_pos s.val p hpl]

theorem ADec.match {s : Slice Std.U8} {out : Slice Std.U32} {nt p l d : Nat} (h : ADec s out nt p)
    (hm : AMatchAt s p l d) (ntU : Std.Usize) (hnt : ntU.val = nt) (v : Std.U32)
    (hv : v.val = LZ77.mkMatch d l) :
    ADec s (out.set ntU v) (nt + 1) (p + l) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  obtain ⟨h3, h258, hpl, hd1, hd32, hdp, hmm⟩ := hm
  have hntl : ntU.val < out.length := by omega
  refine ⟨by omega, by omega, by rw [Std.Slice.set_length]; exact hso, ?_⟩
  rw [← hnt]
  exact emit_match s out ntU p d l v (by rw [hnt]; exact hde) hntl hd1 hdp hd32 h3 h258 hpl hmm hv

theorem ADec.pop_lit {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat} (h : ADec s out nt p)
    (h0 : 0 < nt) (hle : nt ≤ out.length) (ht : (out.val[nt - 1]!).val < 256) :
    1 ≤ p ∧ ADec s out (nt - 1) (p - 1) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  rw [a_toks_pop out nt h0 hle] at hde
  obtain ⟨hp1, hde'⟩ := a_decode_pop_lit (by simpa using hps) hde ht
  exact ⟨hp1, by omega, by omega, hso, hde'⟩

theorem ADec.pop_match {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat} (h : ADec s out nt p)
    (h0 : 0 < nt) (hle : nt ≤ out.length) (ht : 256 ≤ (out.val[nt - 1]!).val) :
    LZ77.tokLen (out.val[nt - 1]!).val ≤ p ∧
      ADec s out (nt - 1) (p - LZ77.tokLen (out.val[nt - 1]!).val) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  rw [a_toks_pop out nt h0 hle] at hde
  obtain ⟨hw, hde'⟩ := a_decode_pop_match (by simpa using hps) hde ht
  have hlen := a_decode_length_le hde'
  rw [a_toks_length out (nt - 1) (by omega), List.length_take, LZ77.bytes_length] at hlen
  exact ⟨hw, by omega, by omega, hso, hde'⟩

theorem ADec.done {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat} (h : ADec s out nt p)
    (hp : s.length ≤ p) : nt ≤ s.length ∧ LZ77.Valid (bytes s) (toks out nt) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  refine ⟨by omega, ?_⟩
  unfold LZ77.Valid
  rw [hde, show p = s.length by omega, ← LZ77.bytes_length, List.take_length]

theorem AMatchAt.back_lit {s : Slice Std.U8} {p l d : Nat} (h : AMatchAt s p l d) (hl : l < 258)
    (hdp : d < p) (heq : s.val[p - 1]! = s.val[p - 1 - d]!) : AMatchAt s (p - 1) (l + 1) d := by
  obtain ⟨h3, h258, hpl, hd1, hd32, _, hm⟩ := h
  refine ⟨by omega, by omega, by omega, hd1, hd32, by omega, ?_⟩
  intro k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    rw [Nat.add_zero, Nat.add_zero, show p - 1 - d = p - 1 - d by rfl]
    exact heq
  · have := hm (k - 1) (by omega)
    rw [show p - 1 + k = p + (k - 1) by omega, show p - 1 - d + k = p - d + (k - 1) by omega]
    exact this

theorem AMatchAt.back_match {s : Slice Std.U8} {p l d w : Nat} (h : AMatchAt s p l d)
    (hlw : l + w ≤ 258) (hw : w ≤ p) (hdw : d ≤ p - w) (hmw : Matches s (p - w - d) (p - w) w) :
    AMatchAt s (p - w) (l + w) d := by
  obtain ⟨h3, h258, hpl, hd1, hd32, _, hm⟩ := h
  refine ⟨by omega, by omega, by omega, hd1, hd32, hdw, ?_⟩
  intro k hk
  rcases Nat.lt_or_ge k w with hkw | hkw
  · have := hmw k hkw
    rw [show p - w - d = p - w - d by rfl] at this
    exact this
  · have := hm (k - w) (by omega)
    rw [show p - w + k = p + (k - w) by omega, show p - w - d + k = p - d + (k - w) by omega]
    exact this

def ABackInv (input : Slice Std.U8) (L d E P0 : Nat) (out : Slice Std.U32) (nt p l : Nat) : Prop :=
  ADec input out nt p ∧ out.length = L ∧ AMatchAt input p l d ∧ p + l = E ∧ p ≤ P0

theorem ABackInv.lit {input : Slice Std.U8} {out : Slice Std.U32} {L d E P0 : Nat}
    {nt p l i1 i2 i4 l1 : Std.Usize} {t : Std.U32} {x y : Std.U8}
    (h : ABackInv input L d E P0 out nt.val p.val l.val)
    (hi1 : i1.val = nt.val - 1) (hntl : nt.val ≤ out.length) (hnt0 : 1 ≤ nt.val)
    (hi1l : i1.val < out.val.length) (ht : t = out.val[i1.val]) (ht256 : t < 256#u32)
    (hi2 : i2.val = p.val - 1) (hi2l : i2.val < input.val.length) (hx : x = input.val[i2.val])
    (hxy : x = y) (hi4 : i4.val = i2.val - d) (hi4l : i4.val < input.val.length)
    (hy : y = input.val[i4.val]) (hl : l.val < 258) (hdp : d < p.val)
    (hl1 : l1.val = l.val + 1) :
    ABackInv input L d E P0 out i1.val i2.val l1.val := by
  obtain ⟨hdec, hL, hm, hE, hP⟩ := h
  have ht' : (out.val[nt.val - 1]!).val < 256 := by
    rw [← hi1, getElem!_pos out.val i1.val hi1l, ← ht]; scalar_tac
  obtain ⟨hp1, hdec'⟩ := ADec.pop_lit hdec (by omega) hntl ht'
  have heq : input.val[p.val - 1]! = input.val[p.val - 1 - d]! := by
    rw [← hi2, getElem!_pos input.val i2.val hi2l, show i2.val - d = i4.val by omega,
      getElem!_pos input.val i4.val hi4l, ← hx, ← hy, hxy]
  have hm' := AMatchAt.back_lit hm hl hdp heq
  rw [hi1, hi2, hl1]
  exact ⟨hdec', hL, hm', by omega, by omega⟩

theorem ABackInv.match {input : Slice Std.U8} {out : Slice Std.U32} {L d E P0 : Nat}
    {nt p l i1 w i9 i10 i11 i12 : Std.Usize} {t : Std.U32}
    (h : ABackInv input L d E P0 out nt.val p.val l.val)
    (hi1 : i1.val = nt.val - 1) (hntl : nt.val ≤ out.length) (hnt0 : 1 ≤ nt.val)
    (hi1l : i1.val < out.val.length) (ht : t = out.val[i1.val])
    (hsame : i12.val = 1 → Matches input i11.val i10.val w.val) (hi12 : i12 = 1#usize)
    (ht24 : 16777216 ≤ t.val) (hwv : w.val = (t.val - 16777216) % 256 + 3)
    (hi9 : i9.val = l.val + w.val) (hi9' : i9.val ≤ 258) (hi10 : i10.val = p.val - w.val)
    (hwp : w.val ≤ p.val) (hdw : d ≤ i10.val) (hi11 : i11.val = i10.val - d) :
    ABackInv input L d E P0 out i1.val i10.val i9.val := by
  obtain ⟨hdec, hL, hm, hE, hP⟩ := h
  have htv : (out.val[nt.val - 1]!).val = t.val := by
    rw [← hi1, getElem!_pos out.val i1.val hi1l, ← ht]
  have hwv' : w.val = LZ77.tokLen (out.val[nt.val - 1]!).val := by
    rw [htv, hwv]
    simp only [LZ77.tokLen, LZ77.MATCH_BASE]
  obtain ⟨hwl, hdec'⟩ := ADec.pop_match hdec (by omega) hntl (by omega)
  rw [← hwv'] at hdec'
  have hmw : Matches input (p.val - w.val - d) (p.val - w.val) w.val := by
    have := hsame (by rw [hi12]; rfl)
    rw [hi11, hi10] at this
    exact this
  have hm' := AMatchAt.back_match hm (by omega) hwp (by omega) hmw
  rw [hi1, hi10, hi9]
  exact ⟨hdec', hL, hm', by omega, by omega⟩

theorem ABackInv.part {input : Slice Std.U8} {out out1 : Slice Std.U32} {L d E P0 : Nat}
    {nt nt1 p l : Nat} {p1 l1 : Std.Usize} (h : ABackInv input L d E P0 out nt p l)
    (hlen : out1.length = out.length) (hdec : ADec input out1 nt1 p1.val)
    (hm : AMatchAt input p1.val l1.val d) (hE : p1.val + l1.val = p + l) (hp : p1.val ≤ p) :
    ABackInv input L d E P0 out1 nt1 p1.val l1.val := by
  obtain ⟨_, hL, _, hE0, hP⟩ := h
  exact ⟨hdec, by rw [hlen, hL], hm, by omega, by omega⟩

theorem Matches.a_cons {input : Slice Std.U8} {a b n : Nat} (h : Matches input (a + 1) (b + 1) n)
    (heq : input.val[b]! = input.val[a]!) : Matches input a b (n + 1) := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with h0 | hk0
  · subst h0; simpa using heq
  · have := h (k - 1) (by omega)
    rw [show b + 1 + (k - 1) = b + k by omega, show a + 1 + (k - 1) = a + k by omega] at this
    exact this

theorem Matches.a_append {input : Slice Std.U8} {a b k l : Nat} (h1 : Matches input a b k)
    (h2 : Matches input (a + k) (b + k) l) : Matches input a b (k + l) := by
  intro j hj
  rcases Nat.lt_or_ge j k with hjk | hjk
  · exact h1 j hjk
  · have := h2 (j - k) (by omega)
    rw [show b + k + (j - k) = b + j by omega, show a + k + (j - k) = a + j by omega] at this
    exact this

theorem AMatchAt.back_part {s : Slice Std.U8} {p l d k : Nat} (h : AMatchAt s p l d)
    (hmk : Matches s (p - k - d) (p - k) k) (hlk : l + k ≤ 258) (hdk : d + k ≤ p) :
    AMatchAt s (p - k) (l + k) d := by
  obtain ⟨h3, h258, hpl, hd1, hd32, _, hm⟩ := h
  refine ⟨by omega, hlk, by omega, hd1, hd32, by omega, ?_⟩
  have hm' : Matches s (p - k - d + k) (p - k + k) l := by
    rw [show p - k - d + k = p - d by omega, show p - k + k = p by omega]; exact hm
  have := Matches.a_append hmk hm'
  rw [show k + l = l + k by omega] at this
  exact this

theorem Matches.a_back_step {input : Slice Std.U8} {p d k : Nat} {i4 i7 k1 : Std.Usize}
    {x y : Std.U8} (h : Matches input (p - k - d) (p - k) k) (hdk : d + k < p)
    (hi4 : i4.val = p - 1 - k) (hi4l : i4.val < input.val.length) (hx : x = input.val[i4.val])
    (hi7 : i7.val = p - 1 - k - d) (hi7l : i7.val < input.val.length)
    (hy : y = input.val[i7.val]) (hxy : x = y) (hk1 : k1.val = k + 1) :
    Matches input (p - k1.val - d) (p - k1.val) k1.val := by
  rw [hk1]
  apply Matches.a_cons
  · rw [show p - (k + 1) - d + 1 = p - k - d by omega, show p - (k + 1) + 1 = p - k by omega]
    exact h
  · rw [show p - (k + 1) - d = i7.val by omega, show p - (k + 1) = i4.val by omega,
      getElem!_pos input.val i4.val hi4l, getElem!_pos input.val i7.val hi7l, ← hx, ← hy, hxy]

theorem copyN_periodic (acc : List Nat) (d : Nat) (hd1 : 1 ≤ d) (hdp : d ≤ acc.length) :
    ∀ n k, k < n →
      (LZ77.copyN acc d n)[acc.length + k]! =
        (LZ77.copyN acc d n)[acc.length + k - d]! := by
  intro n
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [LZ77.copyN]
    have hlen : (LZ77.copyN acc d n).length = acc.length + n := LZ77.copyN_length ..
    rcases Nat.lt_or_ge k n with hkn | hkn
    · rw [List.getElem!_append_left _ _ _ (by omega),
        List.getElem!_append_left _ _ _ (by omega)]
      exact ih k hkn
    · have hke : k = n := by omega
      subst k
      rw [List.getElem!_append_right _ _ _ (by omega),
        List.getElem!_append_left _ _ _ (by omega)]
      simp [hlen]

theorem getElemBang_take (inp : List Nat) (p k : Nat)
    (hk : k < p) (hp : p ≤ inp.length) : (inp.take p)[k]! = inp[k]! := by
  rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by omega), List.getElem_take]

theorem decode_pop_match_semantics {ts : List Nat} {t : Nat} {inp : List Nat} {p : Nat}
    (hp : p ≤ inp.length) (hd : LZ77.decode (ts ++ [t]) = some (inp.take p)) (ht : 256 ≤ t) :
    LZ77.tokLen t ≤ p ∧
      LZ77.decode ts = some (inp.take (p - LZ77.tokLen t)) ∧
      1 ≤ LZ77.tokDist t ∧ LZ77.tokDist t ≤ 32768 ∧
      LZ77.tokDist t ≤ p - LZ77.tokLen t ∧
      ∀ k < LZ77.tokLen t,
        inp[p - LZ77.tokLen t + k]! = inp[p - LZ77.tokLen t - LZ77.tokDist t + k]! := by
  obtain ⟨hlp, hprev⟩ := a_decode_pop_match hp hd ht
  refine ⟨hlp, hprev, ?_⟩
  rw [LZ77.decode_snoc, hprev] at hd
  simp only [Option.bind_some, LZ77.emit, if_neg (show ¬ t < 256 by omega)] at hd
  split at hd
  · rename_i htlegal
    split at hd
    · rename_i hdpos
      have hcopy : LZ77.copyN (inp.take (p - LZ77.tokLen t)) (LZ77.tokDist t)
          (LZ77.tokLen t) = inp.take p := Option.some.inj hd
      have hdist1 : 1 ≤ LZ77.tokDist t := by unfold LZ77.tokDist; omega
      have hdist32 : LZ77.tokDist t ≤ 32768 := by
        simp only [LZ77.MATCH_BASE, LZ77.TOK_LIMIT] at htlegal
        unfold LZ77.tokDist LZ77.MATCH_BASE
        omega
      have hlen : (inp.take (p - LZ77.tokLen t)).length = p - LZ77.tokLen t := by
        simp only [List.length_take]; omega
      refine ⟨hdist1, hdist32, by simpa [hlen] using hdpos, ?_⟩
      intro k hk
      have heq := copyN_periodic (inp.take (p - LZ77.tokLen t)) (LZ77.tokDist t)
        hdist1 hdpos (LZ77.tokLen t) k hk
      rw [hlen, hcopy, getElemBang_take inp p _ (by omega) hp,
        getElemBang_take inp p _ (by omega) hp] at heq
      rw [show p - LZ77.tokLen t + k - LZ77.tokDist t =
        p - LZ77.tokLen t - LZ77.tokDist t + k by omega] at heq
      exact heq
    · simp at hd
  · simp at hd

theorem ADec.pop_match_full {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat}
    (h : ADec s out nt p) (h0 : 0 < nt) (hle : nt ≤ out.length)
    (ht : 256 ≤ (out.val[nt - 1]!).val) :
    ADec s out (nt - 1) (p - LZ77.tokLen (out.val[nt - 1]!).val) ∧
      AMatchAt s (p - LZ77.tokLen (out.val[nt - 1]!).val)
        (LZ77.tokLen (out.val[nt - 1]!).val) (LZ77.tokDist (out.val[nt - 1]!).val) := by
  have hde := h.2.2.2
  rw [a_toks_pop out nt h0 hle] at hde
  obtain ⟨hw, _, hd1, hd32, hdp, hm⟩ := decode_pop_match_semantics
    (by simpa using h.1) hde ht
  have hp : p ≤ s.length := h.1
  have hpsum : p - LZ77.tokLen (out.val[nt - 1]!).val +
      LZ77.tokLen (out.val[nt - 1]!).val = p := by omega
  refine ⟨(ADec.pop_match h h0 hle ht).2, ?_⟩
  have hl3 : 3 ≤ LZ77.tokLen (out.val[nt - 1]!).val := by
    unfold LZ77.tokLen; omega
  have hl258 : LZ77.tokLen (out.val[nt - 1]!).val ≤ 258 := by
    unfold LZ77.tokLen; omega
  refine ⟨hl3, hl258, by omega, hd1, hd32, hdp, ?_⟩
  intro k hk
  have heq := hm k hk
  rw [LZ77.bytes_getElem! s _ (by omega), LZ77.bytes_getElem! s _ (by omega)] at heq
  rw [getElem!_pos s.val (p - LZ77.tokLen (out.val[nt - 1]!).val + k) (by simpa using (show
      p - LZ77.tokLen (out.val[nt - 1]!).val + k < s.length by omega)),
    getElem!_pos s.val (p - LZ77.tokLen (out.val[nt - 1]!).val - LZ77.tokDist (out.val[nt - 1]!).val + k)
      (by simpa using (show p - LZ77.tokLen (out.val[nt - 1]!).val -
        LZ77.tokDist (out.val[nt - 1]!).val + k < s.length by omega))]
  exact UScalar.eq_of_val_eq heq

theorem AMatchAt.prefix {s : Slice Std.U8} {p l d nl : Nat}
    (h : AMatchAt s p l d) (hnl3 : 3 ≤ nl) (hnl : nl ≤ l) :
    AMatchAt s p nl d := by
  obtain ⟨h3, h258, hpl, hd1, hd32, hdp, hm⟩ := h
  exact ⟨hnl3, by omega, by omega, hd1, hd32, hdp, Matches.mono hm hnl⟩

def NearPrefix (input : Slice Std.U8) (p l d : Nat) : Prop :=
  d = 0 ∨ AMatchAt input p l d

theorem old_prefix_near {input : Slice Std.U8} {out : Slice Std.U32} {nt p w nl oldd : Nat}
    (hdec : ADec input out nt p) (h0 : 0 < nt) (hle : nt ≤ out.length)
    (ht : 256 ≤ (out.val[nt - 1]!).val)
    (hw : w = LZ77.tokLen (out.val[nt - 1]!).val)
    (hd : oldd = LZ77.tokDist (out.val[nt - 1]!).val)
    (hnl3 : 3 ≤ nl) (hnl : nl ≤ w) : NearPrefix input (p - w) nl oldd := by
  have hm := (ADec.pop_match_full hdec h0 hle ht).2
  rw [← hw, ← hd] at hm
  exact Or.inr (AMatchAt.prefix hm hnl3 hnl)

theorem fold_part_post {input : Slice Std.U8} {out out1 : Slice Std.U32}
    {nt p l d w k c nl pp p1 l1 : Nat} {ntU : Std.Usize} {v : Std.U32}
    (hdec : ADec input out nt p) (hm : AMatchAt input p l d)
    (h0 : 1 ≤ nt) (hntl : nt ≤ out.length) (ht : 256 ≤ (out.val[nt - 1]!).val)
    (hw : w = LZ77.tokLen (out.val[nt - 1]!).val)
    (hmk : Matches input (p - k - d) (p - k) k) (hc : NearPrefix input pp nl c)
    (hout1 : out1 = out.set ntU v)
    (hlk : l + k ≤ 258) (hdk : d + k ≤ p) (hk : k ≤ w) (hpp : pp = p - w) (hnl : nl = w - k)
    (hc0 : 0 < c) (hntU : ntU.val = nt - 1) (hv : v.val = LZ77.mkMatch c nl)
    (hp1 : p1 = p - k) (hl1 : l1 = l + k) :
    out1.length = out.length ∧ ADec input out1 nt p1 ∧ AMatchAt input p1 l1 d ∧
      p1 + l1 = p + l ∧ p1 ≤ p := by
  subst hp1 hl1 hpp
  obtain ⟨hwp, hdec'⟩ := ADec.pop_match hdec (by omega) hntl ht
  rw [← hw] at hdec' hwp
  have hmc : AMatchAt input (p - w) nl c := by
    rcases hc with hc | hc
    · omega
    · exact hc
  have hd2 := ADec.match hdec' hmc ntU hntU v hv
  rw [show nt - 1 + 1 = nt by omega, show p - w + nl = p - k by omega, ← hout1] at hd2
  refine ⟨by rw [hout1, Std.Slice.set_length], hd2, AMatchAt.back_part hm hmk hlk hdk,
    by omega, by omega⟩

theorem Matches.back_trim {input : Slice Std.U8} {p d k c : Nat}
    (h : Matches input (p - k - d) (p - k) k) (hc : c ≤ k) (hd : d + k ≤ p) :
    Matches input (p - c - d) (p - c) c := by
  intro j hj
  have he := h (k - c + j) (by omega)
  rw [show p - k + (k - c + j) = p - c + j by omega,
    show p - k - d + (k - c + j) = p - c - d + j by omega] at he
  exact he

theorem absorb_one_dec {input : Slice Std.U8} {out out1 : Slice Std.U32}
    {nt p w : Nat} {idx : Std.Usize} {v : Std.U32}
    (hdec : ADec input out nt p) (h0 : 0 < nt) (hntl : nt ≤ out.length)
    (ht : 256 ≤ (out.val[nt - 1]!).val)
    (hw : w = LZ77.tokLen (out.val[nt - 1]!).val)
    (hw3 : 3 ≤ w) (hp : p < input.length)
    (hi : idx.val = nt - 1) (hv : v.val = (input.val[p-w]!).val)
    (ho : out1 = out.set idx v) :
    ADec input out1 nt (p-w+1) := by
  obtain ⟨hwp,hpre⟩ := ADec.pop_match hdec h0 hntl ht
  rw [←hw] at hwp hpre
  have hnext := ADec.lit hpre (by omega) idx hi v hv
  rw [show nt - 1 + 1 = nt by omega, ←ho] at hnext
  exact hnext

theorem absorb_match_post {input : Slice Std.U8} {out out1 : Slice Std.U32}
    {nt p l d w k keep nt1 p1 l1 : Nat}
    (hm : AMatchAt input p l d)
    (hdec : ADec input out1 nt1 (p-w+keep))
    (hL : out1.length = out.length)
    (hs : Matches input (p-k-d) (p-k) k)
    (hwp : w ≤ p) (hkeep : keep ≤ w) (hchecked : w-keep ≤ k)
    (hlk : l+k ≤ 258) (hdk : d+k ≤ p)
    (hp1 : p1 = p-w+keep) (hl1 : l1 = l+w-keep) :
    out1.length = out.length ∧ ADec input out1 nt1 p1 ∧
      AMatchAt input p1 l1 d ∧ p1+l1=p+l ∧ p1≤p := by
  subst hp1 hl1
  have heq : p-w+keep = p-(w-keep) := by omega
  have hlen : l+w-keep = l+(w-keep) := by omega
  have hcheck := Matches.back_trim hs hchecked hdk
  have hmatch := AMatchAt.back_part hm hcheck (by omega) (by omega)
  rw [←heq,←hlen] at hmatch
  exact ⟨hL,hdec,hmatch,by omega,by omega⟩

theorem absorb_two_dec {input : Slice Std.U8} {out out1 out2 : Slice Std.U32}
    {nt p w pp : Nat} {nt0 nt1 : Std.Usize} {v0 v1 : Std.U32}
    (hdec : ADec input out nt p) (h0 : 0 < nt) (hntl : nt ≤ out.length)
    (ht : 256 ≤ (out.val[nt - 1]!).val)
    (hw : w = LZ77.tokLen (out.val[nt - 1]!).val) (hw3 : 3 ≤ w)
    (hpp : pp = p - w)
    (hnt0 : nt0.val = nt - 1) (hnt1 : nt1.val = nt)
    (hv0 : v0.val = (input.val[pp]!).val)
    (hv1 : v1.val = (input.val[pp + 1]!).val)
    (hout1 : out1 = out.set nt0 v0) (hout2 : out2 = out1.set nt1 v1) :
    out2.length = out.length ∧ ADec input out2 (nt + 1) (p - w + 2) := by
  subst pp
  obtain ⟨hwp, hd0⟩ := ADec.pop_match hdec h0 hntl ht
  rw [← hw] at hwp hd0
  have hp : p ≤ input.length := hdec.1
  have hd1 := ADec.lit hd0 (by omega) nt0 hnt0 v0 hv0
  have hi1 : nt1.val = nt - 1 + 1 := by omega
  have hd2 := ADec.lit hd1 (by omega) nt1 hi1 v1 hv1
  rw [← hout1, ← hout2] at hd2
  rw [show nt - 1 + 1 + 1 = nt + 1 by omega,
    show p - w + 1 + 1 = p - w + 2 by omega] at hd2
  exact ⟨by rw [hout2, Std.Slice.set_length, hout1, Std.Slice.set_length], hd2⟩

end EA

namespace EA
open Aeneas Aeneas.Std Result ControlFlow

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open LZ77 (toks bytes bytes_length bytes_getElem! Matches emit_lit emit_match ite_ok)

theorem decode_nil (input : Slice Std.U8) (out : Slice Std.U32) :
    LZ77.decode (toks out (0#usize).val) = some ((bytes input).take (0#usize).val) := by
  simp [toks, LZ77.decode]

theorem valid_of_decode {input : Slice Std.U8} {o : Slice Std.U32} {t p : Std.Usize}
    (hde : LZ77.decode (toks o t.val) = some ((bytes input).take p.val)) (hp : p.val = input.length) :
    LZ77.Valid (bytes input) (toks o t.val) := by
  unfold LZ77.Valid
  rw [hde, hp]
  simp

theorem spec_ite_cut {α : Type} (c : Prop) [Decidable c] (a b : Result α) (Q : α → Prop)
    (ha : c → a ⦃ Q ⦄) (hb : ¬c → b ⦃ Q ⦄) : (if c then a else b) ⦃ Q ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem ite_prod_spec {α β : Type} (c : Prop) [Decidable c] (A B : Result (α × β))
    (hA : c → A ⦃ fun _ => True ⦄) (hB : ¬c → B ⦃ fun _ => True ⦄) :
    (if c then A else B) ⦃ fun _ => True ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

theorem ite_true_spec {α : Type} (c : Prop) [Decidable c] (A B : Result α)
    (hA : c → A ⦃ fun _ => True ⦄) (hB : ¬c → B ⦃ fun _ => True ⦄) :
    (if c then A else B) ⦃ fun _ => True ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

@[local step]
theorem ld4_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.a_ld4 input p ⦃ fun _ => True ⦄ := by
  rw [slot.a_ld4]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem ld8_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.a_ld8 input p ⦃ fun _ => True ⦄ := by
  rw [slot.a_ld8]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem first_diff_spec (x : Std.U64) :
    slot.a_first_diff x ⦃ fun _ => True ⦄ := by
  rw [slot.a_first_diff]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fast_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) (l : Std.Usize) (go : Std.Usize) (it : Std.Usize)  :
    slot.a_fast_len_loop input a b cap l go it ⦃ fun _ => True ⦄ := by
  rw [slot.a_fast_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 40 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_fast_len_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fast_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) :
    slot.a_fast_len input a b cap ⦃ fun _ => True ⦄ := by
  rw [slot.a_fast_len]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem hashp_spec (input : Slice Std.U8) (p : Std.Usize) (hs : Std.U32) :
    slot.a_hashp input p hs ⦃ fun _ => True ⦄ := by
  rw [slot.a_hashp]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem hash3_spec (w : Std.U32) :
    slot.a_hash3 w ⦃ fun _ => True ⦄ := by
  rw [slot.a_hash3]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem dextra_spec (d : Std.Usize) :
    slot.a_dextra d ⦃ fun _ => True ⦄ := by
  rw [slot.a_dextra]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem lextra_spec (l : Std.Usize) :
    slot.a_lextra l ⦃ fun _ => True ⦄ := by
  rw [slot.a_lextra]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem score_spec (l : Std.Usize) (d : Std.Usize) (cq : Std.Usize) :
    slot.a_score l d cq ⦃ fun _ => True ⦄ := by
  rw [slot.a_score]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem lg8_spec (x : Std.U32) :
    slot.a_lg8 x ⦃ fun _ => True ⦄ := by
  rw [slot.a_lg8]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem sample_loop_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) (n : Std.Usize) (st : Std.Usize) (k : Std.Usize) (c : Std.Usize) (hn : n.val = input.length) :
    slot.a_sample_loop input h n st k c ⦃ fun _ => True ⦄ := by
  rw [slot.a_sample_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 8192 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_sample_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem sample_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) :
    slot.a_sample input h ⦃ fun _ => True ⦄ := by
  rw [slot.a_sample]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem entropy256_loop_spec (h : Array Std.U32 256#usize) (tot : Std.U64) (acc : Std.U64) (i : Std.Usize)  :
    slot.a_entropy256_loop h tot acc i ⦃ fun _ => True ⦄ := by
  rw [slot.a_entropy256_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_entropy256_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem entropy256_spec (h : Array Std.U32 256#usize) :
    slot.a_entropy256 h ⦃ fun _ => True ⦄ := by
  rw [slot.a_entropy256]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem share_loop_spec (h : Array Std.U32 256#usize) (lo : Std.Usize) (hi : Std.Usize) (t : Std.Usize) (s : Std.Usize) (i : Std.Usize)  :
    slot.a_share_loop h lo hi t s i ⦃ fun _ => True ⦄ := by
  rw [slot.a_share_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_share_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem share_spec (h : Array Std.U32 256#usize) (lo : Std.Usize) (hi : Std.Usize) :
    slot.a_share h lo hi ⦃ fun _ => True ⦄ := by
  rw [slot.a_share]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem low_mode_spec (e : Std.Usize) :
    slot.a_low_mode e ⦃ fun _ => True ⦄ := by
  rw [slot.a_low_mode]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem lit_cost_spec (e : Std.Usize) (low : Std.Usize) :
    slot.a_lit_cost e low ⦃ fun _ => True ⦄ := by
  rw [slot.a_lit_cost]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem m3_mode_spec (h : Array Std.U32 256#usize) (e : Std.Usize) :
    slot.a_m3_mode h e ⦃ fun _ => True ⦄ := by
  rw [slot.a_m3_mode]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem h3_mode_spec (h : Array Std.U32 256#usize) (e : Std.Usize) :
    slot.a_h3_mode h e ⦃ fun _ => True ⦄ := by
  rw [slot.a_h3_mode]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem numeric_spec (h : Array Std.U32 256#usize) (n : Std.Usize) (low : Std.Usize) :
    slot.a_numeric h n low ⦃ fun _ => True ⦄ := by
  rw [slot.a_numeric]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem walk_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 65536#usize) (pos : Std.Usize) (cap : Std.Usize) (probes : Std.Usize) (litq : Std.Usize) (lim : Std.Usize) (stop : Std.Usize) (cur : Std.Usize) (k : Std.Usize) (bl : Std.Usize) (bs : Std.Usize) (bd : Std.Usize) (off : Std.Usize) (want : Std.U32)  :
    slot.a_walk_loop input prev pos cap probes litq lim stop cur k bl bs bd off want ⦃ fun _ => True ⦄ := by
  rw [slot.a_walk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => probes.val - s.2.1.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5, x6⟩ _
    simp only [slot.a_walk_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem walk_spec (input : Slice Std.U8) (prev : Array Std.U32 65536#usize) (pos : Std.Usize) (start : Std.Usize) (cap : Std.Usize) (probes : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) :
    slot.a_walk input prev pos start cap probes bl0 bs0 litq ⦃ fun _ => True ⦄ := by
  rw [slot.a_walk]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem lwalk_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 65536#usize) (pos : Std.Usize) (cap : Std.Usize) (probes : Std.Usize) (litq : Std.Usize) (lim : Std.Usize) (stop : Std.Usize) (cur : Std.Usize) (k : Std.Usize) (bl : Std.Usize) (bs : Std.Usize) (bd : Std.Usize) (off : Std.Usize) (want : Std.U32)  :
    slot.a_lwalk_loop input prev pos cap probes litq lim stop cur k bl bs bd off want ⦃ fun _ => True ⦄ := by
  rw [slot.a_lwalk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => probes.val - s.2.1.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5, x6⟩ _
    simp only [slot.a_lwalk_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem lwalk_spec (input : Slice Std.U8) (prev : Array Std.U32 65536#usize) (pos : Std.Usize) (start : Std.Usize) (cap : Std.Usize) (probes : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) :
    slot.a_lwalk input prev pos start cap probes bl0 bs0 litq ⦃ fun _ => True ⦄ := by
  rw [slot.a_lwalk]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem cand3_spec (input : Slice Std.U8) (pos : Std.Usize) (s3 : Std.Usize) (cap : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) :
    slot.a_cand3 input pos s3 cap bs0 litq ⦃ fun _ => True ⦄ := by
  rw [slot.a_cand3]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem upd3_spec (input : Slice Std.U8) (head3 : Array Std.U32 16384#usize) (pos : Std.Usize) (on : Std.Usize) :
    slot.a_upd3 input head3 pos on ⦃ fun _ => True ⦄ := by
  rw [slot.a_upd3]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem search_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 65536#usize) (head3 : Array Std.U32 16384#usize) (shorts : Array Std.U32 4096#usize) (pos : Std.Usize) (probes : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) (hs : Std.U32) (h3on : Std.Usize) :
    slot.a_search input head prev head3 shorts pos probes bl0 bs0 litq hs h3on ⦃ fun _ => True ⦄ := by
  rw [slot.a_search]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem insert_range_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («to» : Std.Usize) (hs : Std.U32) (lim : Std.Usize) (p : Std.Usize)  :
    slot.a_insert_range_loop input head prev «to» hs lim p ⦃ fun _ => True ⦄ := by
  rw [slot.a_insert_range_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «to».val - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_insert_range_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem insert_range_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («from» : Std.Usize) («to» : Std.Usize) (hs : Std.U32) :
    slot.a_insert_range input head prev «from» «to» hs ⦃ fun _ => True ⦄ := by
  rw [slot.a_insert_range]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem insert_range3_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (head3 : Array Std.U32 16384#usize) («to» : Std.Usize) (hs : Std.U32) (lim : Std.Usize) (p : Std.Usize)  :
    slot.a_insert_range3_loop input head prev head3 «to» hs lim p ⦃ fun _ => True ⦄ := by
  rw [slot.a_insert_range3_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «to».val - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [slot.a_insert_range3_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem insert_range3_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (head3 : Array Std.U32 16384#usize) («from» : Std.Usize) («to» : Std.Usize) (hs : Std.U32) :
    slot.a_insert_range3 input head prev head3 «from» «to» hs ⦃ fun _ => True ⦄ := by
  rw [slot.a_insert_range3]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem insert_match_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (head3 : Array Std.U32 16384#usize) («from» : Std.Usize) («to» : Std.Usize) (hs : Std.U32) (h3on : Std.Usize) :
    slot.a_insert_match input head prev head3 «from» «to» hs h3on ⦃ fun _ => True ⦄ := by
  rw [slot.a_insert_match]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

def w8 (input : Slice Std.U8) (p : Nat) : Nat :=
  (input.val[p]!).val + (input.val[p + 1]!).val * 256 + (input.val[p + 2]!).val * 65536 +
  (input.val[p + 3]!).val * 16777216 + (input.val[p + 4]!).val * 4294967296 +
  (input.val[p + 5]!).val * 1099511627776 + (input.val[p + 6]!).val * 281474976710656 +
  (input.val[p + 7]!).val * 72057594037927936

def w4 (input : Slice Std.U8) (p : Nat) : Nat :=
  (input.val[p]!).val + (input.val[p + 1]!).val * 256 + (input.val[p + 2]!).val * 65536 +
  (input.val[p + 3]!).val * 16777216

theorem w8_bytes (input : Slice Std.U8) (p q : Nat) (h : w8 input p = w8 input q) :
    ∀ k, k < 8 → input.val[q + k]! = input.val[p + k]! := by
  unfold w8 at h
  have b0 := (input.val[p]!).hBounds
  have b1 := (input.val[p + 1]!).hBounds
  have b2 := (input.val[p + 2]!).hBounds
  have b3 := (input.val[p + 3]!).hBounds
  have b4 := (input.val[p + 4]!).hBounds
  have b5 := (input.val[p + 5]!).hBounds
  have b6 := (input.val[p + 6]!).hBounds
  have b7 := (input.val[p + 7]!).hBounds
  have c0 := (input.val[q]!).hBounds
  have c1 := (input.val[q + 1]!).hBounds
  have c2 := (input.val[q + 2]!).hBounds
  have c3 := (input.val[q + 3]!).hBounds
  have c4 := (input.val[q + 4]!).hBounds
  have c5 := (input.val[q + 5]!).hBounds
  have c6 := (input.val[q + 6]!).hBounds
  have c7 := (input.val[q + 7]!).hBounds
  simp only [Std.UScalarTy.numBits] at *
  intro k hk
  apply UScalar.eq_imp
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero]) <;> omega

theorem w4_bytes (input : Slice Std.U8) (p q : Nat) (h : w4 input p = w4 input q) :
    ∀ k, k < 4 → input.val[q + k]! = input.val[p + k]! := by
  unfold w4 at h
  have b0 := (input.val[p]!).hBounds
  have b1 := (input.val[p + 1]!).hBounds
  have b2 := (input.val[p + 2]!).hBounds
  have b3 := (input.val[p + 3]!).hBounds
  have c0 := (input.val[q]!).hBounds
  have c1 := (input.val[q + 1]!).hBounds
  have c2 := (input.val[q + 2]!).hBounds
  have c3 := (input.val[q + 3]!).hBounds
  simp only [Std.UScalarTy.numBits] at *
  intro k hk
  apply UScalar.eq_imp
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with
    rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero]) <;> omega

theorem Matches.add8 {input : Slice Std.U8} {a b l : Nat} (h : Matches input a b l)
    (hw : w8 input (a + l) = w8 input (b + l)) : Matches input a b (l + 8) := by
  have hb := w8_bytes input (a + l) (b + l) hw
  intro k hk
  by_cases hkl : k < l
  · exact h k hkl
  · have := hb (k - l) (by omega)
    rw [show b + k = b + l + (k - l) by omega, show a + k = a + l + (k - l) by omega]
    exact this

theorem Matches.tail8 {input : Slice Std.U8} {a b l c : Nat} (h : Matches input a b l)
    (hc : 8 ≤ c) (hl : c ≤ l + 8)
    (hw : w8 input (a + (c - 8)) = w8 input (b + (c - 8))) : Matches input a b c := by
  have hb := w8_bytes input (a + (c - 8)) (b + (c - 8)) hw
  intro k hk
  by_cases hkl : k < l
  · exact h k hkl
  · have := hb (k - (c - 8)) (by omega)
    rw [show b + k = b + (c - 8) + (k - (c - 8)) by omega,
      show a + k = a + (c - 8) + (k - (c - 8)) by omega]
    exact this

theorem Matches.two4 {input : Slice Std.U8} {a b c : Nat}
    (hc : 4 ≤ c) (hc8 : c < 8) (hw0 : w4 input a = w4 input b)
    (hw1 : w4 input (a + (c - 4)) = w4 input (b + (c - 4))) : Matches input a b c := by
  have h0 := w4_bytes input a b hw0
  have h1 := w4_bytes input (a + (c - 4)) (b + (c - 4)) hw1
  intro k hk
  by_cases hk4 : k < 4
  · exact h0 k hk4
  · have := h1 (k - (c - 4)) (by omega)
    rw [show b + k = b + (c - 4) + (k - (c - 4)) by omega,
      show a + k = a + (c - 4) + (k - (c - 4)) by omega]
    exact this

theorem Matches.two8 {input : Slice Std.U8} {a b c : Nat}
    (hc : 8 ≤ c) (hc16 : c ≤ 16) (hw0 : w8 input a = w8 input b)
    (hw1 : w8 input (a + (c - 8)) = w8 input (b + (c - 8))) : Matches input a b c := by
  have h0 := w8_bytes input a b hw0
  have h1 := w8_bytes input (a + (c - 8)) (b + (c - 8)) hw1
  intro k hk
  by_cases hk8 : k < 8
  · exact h0 k hk8
  · have := h1 (k - (c - 8)) (by omega)
    rw [show b + k = b + (c - 8) + (k - (c - 8)) by omega,
      show a + k = a + (c - 8) + (k - (c - 8)) by omega]
    exact this

@[local step]
theorem tw8_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 8 ≤ input.length) :
    slot.a_tw8 input p ⦃ fun r => r.val = w8 input p.val ⦄ := by
  rw [slot.a_tw8]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  unfold w8
  rw [getElem!_pos input.val p.val (by scalar_tac), getElem!_pos input.val (p.val + 1) (by scalar_tac),
    getElem!_pos input.val (p.val + 2) (by scalar_tac), getElem!_pos input.val (p.val + 3) (by scalar_tac),
    getElem!_pos input.val (p.val + 4) (by scalar_tac), getElem!_pos input.val (p.val + 5) (by scalar_tac),
    getElem!_pos input.val (p.val + 6) (by scalar_tac), getElem!_pos input.val (p.val + 7) (by scalar_tac)]
  scalar_tac

@[local step]
theorem tw4_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 4 ≤ input.length) :
    slot.a_tw4 input p ⦃ fun r => r.val = w4 input p.val ⦄ := by
  rw [slot.a_tw4]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  unfold w4
  rw [getElem!_pos input.val p.val (by scalar_tac), getElem!_pos input.val (p.val + 1) (by scalar_tac),
    getElem!_pos input.val (p.val + 2) (by scalar_tac), getElem!_pos input.val (p.val + 3) (by scalar_tac)]
  scalar_tac

theorem words_eq_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.a_words_eq_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.a_words_eq_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.a_words_eq_loop.body]
    step*
    all_goals first
      | exact ⟨hle, hinv⟩
      | (refine ⟨by scalar_tac, ?_, by scalar_tac⟩
         rw [show l1.val = l.val + 8 by scalar_tac]
         apply Matches.add8 hinv
         rw [show a.val + l.val = i1.val by scalar_tac, show b.val + l.val = i3.val by scalar_tac,
           ← i2_post, ← i4_post, ‹i2 = i4›])
  · exact ⟨hl0, h0⟩

@[local step]
theorem tail_eq_spec (input : Slice Std.U8) (a b cap l : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) (hl : l.val ≤ cap.val) :
    slot.a_tail_eq input a b cap l ⦃ fun r => r.val = 1 →
      8 ≤ cap.val ∧ cap.val ≤ l.val + 8 ∧
      w8 input (a.val + (cap.val - 8)) = w8 input (b.val + (cap.val - 8)) ⦄ := by
  rw [slot.a_tail_eq]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals first
    | (intro h; simp at h)
    | (intro _
       refine ⟨by scalar_tac, by scalar_tac, ?_⟩
       rw [show a.val + (cap.val - 8) = i2.val by scalar_tac,
         show b.val + (cap.val - 8) = i4.val by scalar_tac, ← i3_post, ← i5_post, ‹i3 = i5›])
    | (refine ⟨by scalar_tac, by scalar_tac, ?_⟩
       rw [show a.val + (cap.val - 8) = i2.val by scalar_tac,
         show b.val + (cap.val - 8) = i4.val by scalar_tac, ← i3_post, ← i5_post, ‹i3 = i5›])

@[local step]
theorem short_eq_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.a_short_eq input a b cap ⦃ fun r => r.val = 1 →
      4 ≤ cap.val ∧ cap.val < 8 ∧ w4 input a.val = w4 input b.val ∧
      w4 input (a.val + (cap.val - 4)) = w4 input (b.val + (cap.val - 4)) ⦄ := by
  rw [slot.a_short_eq]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals first
    | (intro h; simp at h)
    | (intro _
       refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
       · rw [← i_post, ← i1_post]
         simp_all
       · rw [show a.val + (cap.val - 4) = i3.val by scalar_tac,
           show b.val + (cap.val - 4) = i5.val by scalar_tac, ← i4_post, ← i6_post, ‹i4 = i6›])
    | (refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
       · rw [← i_post, ← i1_post]
         simp_all
       · rw [show a.val + (cap.val - 4) = i3.val by scalar_tac,
           show b.val + (cap.val - 4) = i5.val by scalar_tac, ← i4_post, ← i6_post, ‹i4 = i6›])

@[local step]
theorem words_eq_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.a_words_eq input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.a_words_eq]
  apply Std.WP.spec_bind (words_eq_loop_spec input a b cap 0#usize ha hb (by scalar_tac)
    (LZ77.Matches.zero input a.val b.val))
  rintro l ⟨hle, hm⟩
  apply Std.WP.spec_bind (tail_eq_spec input a b cap l ha hb hle)
  rintro big hbig
  apply Std.WP.spec_bind (short_eq_spec input a b cap ha hb)
  rintro small hsmall
  split
  · have h1 : big.val = 1 := by scalar_tac
    obtain ⟨h8, hcl, hw⟩ := hbig h1
    simp only [Std.WP.spec_ok]
    exact ⟨le_refl _, Matches.tail8 hm h8 hcl hw⟩
  · split
    · have h1 : small.val = 1 := by scalar_tac
      obtain ⟨h4, h8, hw0, hw1⟩ := hsmall h1
      simp only [Std.WP.spec_ok]
      exact ⟨le_refl _, Matches.two4 h4 h8 hw0 hw1⟩
    · simp only [Std.WP.spec_ok]
      exact ⟨hle, hm⟩

theorem match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.a_match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  (
  rw [slot.a_match_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ LZ77.Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    simp only [slot.a_match_len_loop.body]
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
  · exact ⟨hl0, h0⟩)

@[local step]
theorem match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.a_match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.a_match_len]
  apply Std.WP.spec_bind (words_eq_spec input a b cap ha hb)
  rintro l0 ⟨hle, hm⟩
  exact match_len_loop_spec input a b cap l0 ha hb hle hm

theorem verified_spec (input : Slice Std.U8) (pos d ch : Std.Usize) :
    slot.a_verified input pos d ch ⦃ fun b => b = true →
      3 ≤ ch.val ∧ ch.val ≤ 258 ∧ 1 ≤ d.val ∧ d.val ≤ 32768 ∧ d.val ≤ pos.val ∧
      pos.val + ch.val ≤ input.length ∧ Matches input (pos.val - d.val) pos.val ch.val ⦄ := by
  rw [slot.a_verified]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals intro hv
  all_goals try simp at hv
  all_goals refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac,
    by scalar_tac, by scalar_tac, ?_⟩
  all_goals rw [← a_post1]
  all_goals first
    | exact Matches.mono i1_post2 hv
    | (refine Matches.two8 (by scalar_tac) (by scalar_tac) ?_ ?_
       · rw [← i1_post, ← i2_post, ‹i1 = i2›]
       · rw [show a.val + (ch.val - 8) = i4.val by scalar_tac,
           show pos.val + (ch.val - 8) = i7.val by scalar_tac,
           ← i5_post, ← i8_post, hv])
    | (refine Matches.two4 (by scalar_tac) (by scalar_tac) ?_ ?_
       · rw [← i1_post, ← i2_post, ‹i1 = i2›]
       · rw [show a.val + (ch.val - 4) = i4.val by scalar_tac,
           show pos.val + (ch.val - 4) = i7.val by scalar_tac,
           ← i5_post, ← i8_post, hv])
    | (intro k hk
       rcases (by scalar_tac : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
       · simp only [Nat.add_zero]
         rw [getElem!_pos input.val pos.val (by scalar_tac),
           getElem!_pos input.val a.val (by scalar_tac), ← i1_post, ← i2_post, ‹i1 = i2›]
       · rw [show pos.val + 1 = i5.val by scalar_tac,
           show a.val + 1 = i3.val by scalar_tac,
           getElem!_pos input.val i5.val (by scalar_tac),
           getElem!_pos input.val i3.val (by scalar_tac), ← i4_post, ← i6_post, ‹i4 = i6›]
       · rw [show pos.val + 2 = i9.val by scalar_tac,
           show a.val + 2 = i7.val by scalar_tac,
           getElem!_pos input.val i9.val (by scalar_tac),
           getElem!_pos input.val i7.val (by scalar_tac), ← i8_post, ← i10_post, hv])

theorem emit_lits_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (n cnt1 k0 c0 ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ n.val) (hntok : ntok0.val ≤ k0.val) (hc0 : c0.val = 0)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take k0.val)) :
    slot.a_emit_lits_loop input out0 n cnt1 k0 c0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ (k0.val < r.2.1.val ∨ cnt1.val = 0 ∨ k0.val = n.val) ∧
      r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := by
  rw [slot.a_emit_lits_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.1.val)
    (inv := fun s =>
      s.2.1.val ≤ n.val ∧ s.2.1.val = k0.val + s.2.2.1.val ∧ s.2.2.2.val ≤ s.2.1.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.val) = some ((bytes input).take s.2.1.val))
  · rintro ⟨out, k, c, ntok⟩ ⟨hkn, hkc, hnt, hlen, hde⟩
    simp only at hkn hkc hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.a_emit_lits_loop.body]
    split
    case isTrue hklt =>
      split
      case isTrue hc =>
        have hntok_lt : ntok.val < out.length := by scalar_tac
        have hposlen : k.val < input.length := by scalar_tac
        step*
        have hval : i1.val = (bytes input)[k.val]! := by
          rw [bytes_getElem! input k.val hposlen, i1_post, Std.U8.cast_U32_val_eq, i_post]
        refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show k1.val = k.val + 1 by scalar_tac]
        exact emit_lit input out ntok k.val i1 hde hposlen hntok_lt hval
      case isFalse hc =>
        exact ⟨hkn, by scalar_tac, hnt, hlen, hde⟩
    case isFalse hge =>
      exact ⟨hkn, by scalar_tac, hnt, hlen, hde⟩
  · exact ⟨hk, by scalar_tac, hntok, rfl, hdec⟩

@[local step]
theorem emit_lits_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos0 cnt ntok0 : Std.Usize)
    (hout : input.length ≤ out.length) (hpos : pos0.val ≤ input.length)
    (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.a_emit_lits input out pos0 cnt ntok0 ⦃ fun r =>
      (pos0.val < r.1.2.val ∨ pos0.val = input.length) ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_emit_lits]
  apply Std.WP.spec_bind (Pₘ := fun (c : Std.Usize) => 1 ≤ c.val)
  · split <;> simp only [Std.WP.spec_ok] <;> scalar_tac
  intro cnt1 hc1
  apply Std.WP.spec_bind (emit_lits_loop_spec input out _ cnt1 pos0 0#usize ntok0
    (by simp) hout (by scalar_tac) hntok (by simp) hdec)
  rintro ⟨out1, k, ntok⟩ ⟨h1, h2, h3, h4, h5⟩
  simp only at h1 h2 h3 h4 h5
  step*
  all_goals exact ⟨by scalar_tac, by scalar_tac, h3, h4, h5⟩

@[local step]
theorem emit_step_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos d l lits ntok : Std.Usize)
    (hout : input.length ≤ out.length) (hpos : pos.val < input.length)
    (hntok : ntok.val ≤ pos.val)
    (hdec : LZ77.decode (toks out ntok.val) = some ((bytes input).take pos.val)) :
    slot.a_emit_step input out pos d l lits ntok ⦃ fun r =>
      pos.val < r.1.2.val ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_emit_step]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (verified_spec input pos d l)
  intro b hb
  split
  case isTrue hbt =>
    obtain ⟨hl3, hl258, hd1, hdmax, hdpos, hend, hmatch⟩ := hb hbt
    have hntok_lt : ntok.val < out.length := by scalar_tac
    step*
    have htok : i6.val = LZ77.mkMatch d.val l.val := by
      simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i6_post, i3_post, i2_post]
      scalar_tac
    refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
      by rw [out1_post]; simp [Std.Slice.set_val_eq], ?_⟩
    rw [out1_post, show i7.val = ntok.val + 1 by scalar_tac,
      show i8.val = pos.val + l.val by scalar_tac]
    exact emit_match input out ntok pos.val d.val l.val i6 hdec hntok_lt hd1 hdpos hdmax
      hl3 hl258 hend hmatch htok
  case isFalse hbf =>
    apply Std.WP.spec_mono (emit_lits_spec input out pos lits ntok hout (by scalar_tac) hntok hdec)
    rintro ⟨⟨t, k⟩, o⟩ ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by scalar_tac, h2, h3, h4, h5⟩

@[local step]
theorem lazy_probe_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 65536#usize) (head3 : Array Std.U32 16384#usize) (q : Std.Usize) (go : Std.Usize) (p2 : Std.Usize) (l1 : Std.Usize) (sv1 : Std.Usize) (litq : Std.Usize) (hs : Std.U32) (h3on : Std.Usize) (start : Std.Usize) :
    slot.a_lazy_probe input head prev head3 q go p2 l1 sv1 litq hs h3on start ⦃ fun _ => True ⦄ := by
  rw [slot.a_lazy_probe]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem ext_ok_spec (input : Slice Std.U8) (pos : Std.Usize) (l2 : Std.Usize) (d2 : Std.Usize) :
    slot.a_ext_ok input pos l2 d2 ⦃ fun _ => True ⦄ := by
  rw [slot.a_ext_ok]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_tw8_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 8 ≤ input.length) :
    slot.a_fl_tw8 input p ⦃ fun r => r.val = w8 input p.val ⦄ := by
  rw [slot.a_fl_tw8]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  unfold w8
  rw [getElem!_pos input.val p.val (by scalar_tac), getElem!_pos input.val (p.val + 1) (by scalar_tac),
    getElem!_pos input.val (p.val + 2) (by scalar_tac), getElem!_pos input.val (p.val + 3) (by scalar_tac),
    getElem!_pos input.val (p.val + 4) (by scalar_tac), getElem!_pos input.val (p.val + 5) (by scalar_tac),
    getElem!_pos input.val (p.val + 6) (by scalar_tac), getElem!_pos input.val (p.val + 7) (by scalar_tac)]
  scalar_tac

@[local step]
theorem fl_tw4_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 4 ≤ input.length) :
    slot.a_fl_tw4 input p ⦃ fun r => r.val = w4 input p.val ⦄ := by
  rw [slot.a_fl_tw4]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  unfold w4
  rw [getElem!_pos input.val p.val (by scalar_tac), getElem!_pos input.val (p.val + 1) (by scalar_tac),
    getElem!_pos input.val (p.val + 2) (by scalar_tac), getElem!_pos input.val (p.val + 3) (by scalar_tac)]
  scalar_tac

theorem fl_words_eq_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.a_fl_words_eq_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.a_fl_words_eq_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.a_fl_words_eq_loop.body]
    step*
    all_goals first
      | exact ⟨hle, hinv⟩
      | (refine ⟨by scalar_tac, ?_, by scalar_tac⟩
         rw [show l1.val = l.val + 8 by scalar_tac]
         apply Matches.add8 hinv
         rw [show a.val + l.val = i1.val by scalar_tac, show b.val + l.val = i3.val by scalar_tac,
           ← i2_post, ← i4_post, ‹i2 = i4›])
  · exact ⟨hl0, h0⟩

@[local step]
theorem fl_tail_eq_spec (input : Slice Std.U8) (a b cap l : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) (hl : l.val ≤ cap.val) :
    slot.a_fl_tail_eq input a b cap l ⦃ fun r => r.val = 1 →
      8 ≤ cap.val ∧ cap.val ≤ l.val + 8 ∧
      w8 input (a.val + (cap.val - 8)) = w8 input (b.val + (cap.val - 8)) ⦄ := by
  rw [slot.a_fl_tail_eq]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals first
    | (intro h; simp at h)
    | (intro _
       refine ⟨by scalar_tac, by scalar_tac, ?_⟩
       rw [show a.val + (cap.val - 8) = i2.val by scalar_tac,
         show b.val + (cap.val - 8) = i4.val by scalar_tac, ← i3_post, ← i5_post, ‹i3 = i5›])
    | (refine ⟨by scalar_tac, by scalar_tac, ?_⟩
       rw [show a.val + (cap.val - 8) = i2.val by scalar_tac,
         show b.val + (cap.val - 8) = i4.val by scalar_tac, ← i3_post, ← i5_post, ‹i3 = i5›])

@[local step]
theorem fl_short_eq_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.a_fl_short_eq input a b cap ⦃ fun r => r.val = 1 →
      4 ≤ cap.val ∧ cap.val < 8 ∧ w4 input a.val = w4 input b.val ∧
      w4 input (a.val + (cap.val - 4)) = w4 input (b.val + (cap.val - 4)) ⦄ := by
  rw [slot.a_fl_short_eq]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals first
    | (intro h; simp at h)
    | (intro _
       refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
       · rw [← i_post, ← i1_post]
         simp_all
       · rw [show a.val + (cap.val - 4) = i3.val by scalar_tac,
           show b.val + (cap.val - 4) = i5.val by scalar_tac, ← i4_post, ← i6_post, ‹i4 = i6›])
    | (refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
       · rw [← i_post, ← i1_post]
         simp_all
       · rw [show a.val + (cap.val - 4) = i3.val by scalar_tac,
           show b.val + (cap.val - 4) = i5.val by scalar_tac, ← i4_post, ← i6_post, ‹i4 = i6›])

@[local step]
theorem fl_words_eq_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.a_fl_words_eq input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.a_fl_words_eq]
  apply Std.WP.spec_bind (fl_words_eq_loop_spec input a b cap 0#usize ha hb (by scalar_tac)
    (LZ77.Matches.zero input a.val b.val))
  rintro l ⟨hle, hm⟩
  apply Std.WP.spec_bind (fl_tail_eq_spec input a b cap l ha hb hle)
  rintro big hbig
  apply Std.WP.spec_bind (fl_short_eq_spec input a b cap ha hb)
  rintro small hsmall
  split
  · have h1 : big.val = 1 := by scalar_tac
    obtain ⟨h8, hcl, hw⟩ := hbig h1
    simp only [Std.WP.spec_ok]
    exact ⟨le_refl _, Matches.tail8 hm h8 hcl hw⟩
  · split
    · have h1 : small.val = 1 := by scalar_tac
      obtain ⟨h4, h8, hw0, hw1⟩ := hsmall h1
      simp only [Std.WP.spec_ok]
      exact ⟨le_refl _, Matches.two4 h4 h8 hw0 hw1⟩
    · simp only [Std.WP.spec_ok]
      exact ⟨hle, hm⟩

theorem fl_match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.a_fl_match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.a_fl_match_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ LZ77.Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    simp only [slot.a_fl_match_len_loop.body]
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
  · exact ⟨hl0, h0⟩

@[local step]
theorem fl_match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.a_fl_match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.a_fl_match_len]
  apply Std.WP.spec_bind (fl_words_eq_spec input a b cap ha hb)
  rintro l0 ⟨hle, hm⟩
  exact fl_match_len_loop_spec input a b cap l0 ha hb hle hm

theorem fl_verified_spec (input : Slice Std.U8) (pos d ch : Std.Usize) :
    slot.a_fl_verified input pos d ch ⦃ fun b => b = true →
      3 ≤ ch.val ∧ ch.val ≤ 258 ∧ 1 ≤ d.val ∧ d.val ≤ 32768 ∧ d.val ≤ pos.val ∧
      pos.val + ch.val ≤ input.length ∧ Matches input (pos.val - d.val) pos.val ch.val ⦄ := by
  rw [slot.a_fl_verified]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  intro hv
  have hv' : ch.val ≤ v.val := by simpa using hv
  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac,
    by scalar_tac, ?_⟩
  rw [show pos.val - d.val = i1.val by scalar_tac]
  exact Matches.mono v_post2 hv'

theorem fl_emit_lits_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (n cnt1 k0 c0 ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ n.val) (hntok : ntok0.val ≤ k0.val) (hc0 : c0.val = 0)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take k0.val)) :
    slot.a_fl_emit_lits_loop input out0 n cnt1 k0 c0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ (k0.val < r.2.1.val ∨ cnt1.val = 0 ∨ k0.val = n.val) ∧
      r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := by
  rw [slot.a_fl_emit_lits_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.1.val)
    (inv := fun s =>
      s.2.1.val ≤ n.val ∧ s.2.1.val = k0.val + s.2.2.1.val ∧ s.2.2.2.val ≤ s.2.1.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.val) = some ((bytes input).take s.2.1.val))
  · rintro ⟨out, k, c, ntok⟩ ⟨hkn, hkc, hnt, hlen, hde⟩
    simp only at hkn hkc hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.a_fl_emit_lits_loop.body]
    split
    case isTrue hklt =>
      split
      case isTrue hc =>
        have hntok_lt : ntok.val < out.length := by scalar_tac
        have hposlen : k.val < input.length := by scalar_tac
        step*
        have hval : i1.val = (bytes input)[k.val]! := by
          rw [bytes_getElem! input k.val hposlen, i1_post, Std.U8.cast_U32_val_eq, i_post]
        refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show k1.val = k.val + 1 by scalar_tac]
        exact emit_lit input out ntok k.val i1 hde hposlen hntok_lt hval
      case isFalse hc =>
        exact ⟨hkn, by scalar_tac, hnt, hlen, hde⟩
    case isFalse hge =>
      exact ⟨hkn, by scalar_tac, hnt, hlen, hde⟩
  · exact ⟨hk, by scalar_tac, hntok, rfl, hdec⟩

@[local step]
theorem fl_emit_lits_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos0 cnt ntok0 : Std.Usize)
    (hout : input.length ≤ out.length) (hpos : pos0.val ≤ input.length)
    (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.a_fl_emit_lits input out pos0 cnt ntok0 ⦃ fun r =>
      (pos0.val < r.1.2.val ∨ pos0.val = input.length) ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_fl_emit_lits]
  apply Std.WP.spec_bind (Pₘ := fun (c : Std.Usize) => 1 ≤ c.val)
  · split <;> simp only [Std.WP.spec_ok] <;> scalar_tac
  intro cnt1 hc1
  apply Std.WP.spec_bind (fl_emit_lits_loop_spec input out _ cnt1 pos0 0#usize ntok0
    (by simp) hout (by scalar_tac) hntok (by simp) hdec)
  rintro ⟨out1, k, ntok⟩ ⟨h1, h2, h3, h4, h5⟩
  simp only at h1 h2 h3 h4 h5
  step*
  all_goals exact ⟨by scalar_tac, by scalar_tac, h3, h4, h5⟩

@[local step]
theorem fl_emit_step_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos d l lits ntok : Std.Usize)
    (hout : input.length ≤ out.length) (hpos : pos.val < input.length)
    (hntok : ntok.val ≤ pos.val)
    (hdec : LZ77.decode (toks out ntok.val) = some ((bytes input).take pos.val)) :
    slot.a_fl_emit_step input out pos d l lits ntok ⦃ fun r =>
      pos.val < r.1.2.val ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_fl_emit_step]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (fl_verified_spec input pos d l)
  intro b hb
  split
  case isTrue hbt =>
    obtain ⟨hl3, hl258, hd1, hdmax, hdpos, hend, hmatch⟩ := hb hbt
    have hntok_lt : ntok.val < out.length := by scalar_tac
    step*
    have htok : i6.val = LZ77.mkMatch d.val l.val := by
      simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i6_post, i3_post, i2_post]
      scalar_tac
    refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
      by rw [out1_post]; simp [Std.Slice.set_val_eq], ?_⟩
    rw [out1_post, show i7.val = ntok.val + 1 by scalar_tac,
      show i8.val = pos.val + l.val by scalar_tac]
    exact emit_match input out ntok pos.val d.val l.val i6 hdec hntok_lt hd1 hdpos hdmax
      hl3 hl258 hend hmatch htok
  case isFalse hbf =>
    apply Std.WP.spec_mono (fl_emit_lits_spec input out pos lits ntok hout (by scalar_tac) hntok hdec)
    rintro ⟨⟨t, k⟩, o⟩ ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by scalar_tac, h2, h3, h4, h5⟩

@[local step]
theorem fl_byte_spec (input : Slice Std.U8) (i : Std.Usize) :
    slot.a_fl_byte input i ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_byte]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_ld4_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.a_fl_ld4 input p ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_ld4]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_ld8_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.a_fl_ld8 input p ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_ld8]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) (l : Std.Usize) (go : Std.Usize) (it : Std.Usize)  :
    slot.a_fl_len_loop input a b cap l go it ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 40 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_fl_len_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) :
    slot.a_fl_len input a b cap ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_len]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_hashp_spec (input : Slice Std.U8) (p : Std.Usize) (hsh : Std.U64) :
    slot.a_fl_hashp input p hsh ⦃ fun r => r.val < 65536 ⦄ := by
  rw [slot.a_fl_hashp]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_log16_spec (f : Std.U32) :
    slot.a_fl_log16 f ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_log16]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_sample_loop_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) (n : Std.Usize) (st : Std.Usize) (k : Std.Usize) (c : Std.Usize) (hn : n.val = input.length) :
    slot.a_fl_sample_loop input h n st k c ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_sample_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 8192 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_fl_sample_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_sample_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) :
    slot.a_fl_sample input h ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_sample]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_costs_loop0_spec (h : Array Std.U32 256#usize) (t : Std.U32) (i : Std.Usize)  :
    slot.a_fl_costs_loop0 h t i ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_costs_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.a_fl_costs_loop0.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_costs_loop1_spec (h : Array Std.U32 256#usize) (cost : Array Std.U32 256#usize) (lt : Std.U32) (j : Std.Usize)  :
    slot.a_fl_costs_loop1 h cost lt j ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_costs_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.a_fl_costs_loop1.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_costs_spec (h : Array Std.U32 256#usize) (cost : Array Std.U32 256#usize) :
    slot.a_fl_costs h cost ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_costs]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_ent_loop0_spec (h : Array Std.U32 1024#usize) (base : Std.Usize) (t : Std.U32) (i : Std.Usize)  :
    slot.a_fl_ent_loop0 h base t i ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_ent_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.a_fl_ent_loop0.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_ent_loop1_spec (h : Array Std.U32 1024#usize) (base : Std.Usize) (lt : Std.U32) (bits : Std.Usize) (j : Std.Usize)  :
    slot.a_fl_ent_loop1 h base lt bits j ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_ent_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.a_fl_ent_loop1.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_ent_spec (h : Array Std.U32 1024#usize) (base : Std.Usize) :
    slot.a_fl_ent h base ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_ent]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_stats_loop0_spec (h : Array Std.U32 256#usize) (t : Std.U32) (i : Std.Usize)  :
    slot.a_fl_stats_loop0 h t i ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_stats_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.a_fl_stats_loop0.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_stats_loop1_spec (h : Array Std.U32 256#usize) (t : Std.U32) (lt : Std.U32) (bits : Std.Usize) (top : Std.U32) (np : Std.Usize) (big : Std.Usize) (bigsum : Std.Usize) (j : Std.Usize)  :
    slot.a_fl_stats_loop1 h t lt bits top np big bigsum j ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_stats_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.2.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5⟩ _
    simp only [slot.a_fl_stats_loop1.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_stats_spec (h : Array Std.U32 256#usize) :
    slot.a_fl_stats h ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_stats]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_probe_chunk_loop_spec (input : Slice Std.U8) (tab : Array Std.U32 4096#usize) (ph : Array Std.U32 1024#usize) (s : Std.Usize) (p : Std.Usize) (k : Std.Usize) (c4 : Std.Usize)  :
    slot.a_fl_probe_chunk_loop input tab ph s p k c4 ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_probe_chunk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.A_FL_PCH.val - s.2.2.2.1.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4⟩ _
    simp only [slot.a_fl_probe_chunk_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_weights_loop_spec (input : Slice Std.U8) (tab : Array Std.U32 4096#usize) (ph : Array Std.U32 1024#usize) (span : Std.Usize) (c4 : Std.Usize) (i : Std.Usize)  :
    slot.a_fl_weights_loop input tab ph span c4 i ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_weights_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.A_FL_PNC.val - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [slot.a_fl_weights_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_weights_spec (input : Slice Std.U8) :
    slot.a_fl_weights input ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_weights]
  try simp only [lift, Array.to_slice_mut, ite_ok]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_mode_spec (input : Slice Std.U8) (st : Std.U64) :
    slot.a_fl_mode input st ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_mode]
  try simp only [lift, Array.to_slice_mut, ite_ok]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_config_spec («class» : Std.Usize) (cf : Array Std.Usize 8#usize) :
    slot.a_fl_config «class» cf ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_config]
  try simp only [lift, Array.to_slice_mut, ite_ok]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

section
attribute [local step] ite_true_spec

@[local step]
theorem fl_lit_parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.a_fl_lit_parse input out ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_fl_lit_parse]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by assumption⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac)

end
attribute [local step] fl_lit_parse_spec

section
attribute [local step] ite_true_spec

@[local step]
theorem fl_rle_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize) (pos0 : Std.Usize) (ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.a_fl_rle_parse_loop input out0 n pos0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := by
  rw [slot.a_fl_rle_parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.1.val)
    (inv := fun s =>
      s.2.1.val ≤ n.val ∧ s.2.2.val ≤ s.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.val) = some ((bytes input).take s.2.1.val))
  · rintro ⟨out, pos, ntok⟩ ⟨hpn, hnt, hlen, hde⟩
    simp only at hpn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.a_fl_rle_parse_loop.body, lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      all_goals (repeat (first
        | (refine ⟨by scalar_tac, by scalar_tac, by assumption, by assumption, by scalar_tac⟩)
        | (intro hc; (try step*))
        | (casesm* _ × _; (try simp only []); (try step*))
        | (split <;> (try step*))
        | (step <;> (try step*))))
      all_goals (try scalar_tac)
    case isFalse hge =>
      exact ⟨hpn, hnt, hlen, hde⟩
  · exact ⟨hp, hntok, rfl, hdec⟩

end
attribute [local step] fl_rle_parse_loop_spec

section
attribute [local step] ite_true_spec

@[local step]
theorem fl_rle_parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.a_fl_rle_parse input out ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_fl_rle_parse]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by assumption⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac)

end
attribute [local step] fl_rle_parse_spec

@[local step]
theorem fl_cheap_run_loop_spec (input : Slice Std.U8) (cost : Array Std.U32 256#usize) (n : Std.Usize) (k : Std.Usize) (hn : n.val = input.length) :
    slot.a_fl_cheap_run_loop input cost n k ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_cheap_run_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.val)
    (inv := fun s => True)
  · rintro x0 _
    simp only [slot.a_fl_cheap_run_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_cheap_run_spec (input : Slice Std.U8) (cost : Array Std.U32 256#usize) (pos : Std.Usize) :
    slot.a_fl_cheap_run input cost pos ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_cheap_run]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_span_cost_loop_spec (input : Slice Std.U8) (cost : Array Std.U32 256#usize) (pos : Std.Usize) (l : Std.Usize) (s : Std.Usize) (i : Std.Usize)  :
    slot.a_fl_span_cost_loop input cost pos l s i ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_span_cost_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => l.val - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.a_fl_span_cost_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_dextra_spec (d : Std.Usize) :
    slot.a_fl_dextra d ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_dextra]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_lextra_spec (l : Std.Usize) :
    slot.a_fl_lextra l ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_lextra]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_dna_ok_spec (input : Slice Std.U8) (cost : Array Std.U32 256#usize) (pos : Std.Usize) (l : Std.Usize) (d : Std.Usize) :
    slot.a_fl_dna_ok input cost pos l d ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_dna_ok]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_dwalk_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) (bl : Std.Usize) (bd : Std.Usize) (cur : Std.Usize) (k : Std.Usize)  :
    slot.a_fl_dwalk_loop input prev pos cap depth bl bd cur k ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_dwalk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => depth.val - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [slot.a_fl_dwalk_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_dwalk_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (start : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) :
    slot.a_fl_dwalk input prev pos start cap depth ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_dwalk]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_dsearch_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (p : Std.Usize) (depth : Std.Usize) :
    slot.a_fl_dsearch input head prev p depth ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_dsearch]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_tinsert_loop_spec (input : Slice Std.U8) (head : Array Std.U16 16384#usize) (prev : Array Std.U16 32768#usize) («to» : Std.Usize) (hsh : Std.U64) (lim : Std.Usize) (p : Std.Usize)  :
    slot.a_fl_tinsert_loop input head prev «to» hsh lim p ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_tinsert_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «to».val - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_fl_tinsert_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_tinsert_spec (input : Slice Std.U8) (head : Array Std.U16 16384#usize) (prev : Array Std.U16 32768#usize) («from» : Std.Usize) («to» : Std.Usize) (hsh : Std.U64) :
    slot.a_fl_tinsert input head prev «from» «to» hsh ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_tinsert]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_insert_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («to» : Std.Usize) (hsh : Std.U64) (lim : Std.Usize) (p : Std.Usize)  :
    slot.a_fl_insert_loop input head prev «to» hsh lim p ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_insert_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «to».val - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_fl_insert_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_insert_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («from» : Std.Usize) («to» : Std.Usize) (hsh : Std.U64) :
    slot.a_fl_insert input head prev «from» «to» hsh ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_insert]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

section
attribute [local step] ite_true_spec

@[local step]
theorem fl_dna_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (cost : Array Std.U32 256#usize) (n : Std.Usize) (head0 : Array Std.U32 65536#usize) (prev0 : Array Std.U32 32768#usize) (pos0 : Std.Usize) (ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.a_fl_dna_parse_loop input out0 cost n head0 prev0 pos0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := by
  rw [slot.a_fl_dna_parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.1.val ≤ n.val ∧ s.2.2.2.2.val ≤ s.2.2.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.val) = some ((bytes input).take s.2.2.2.1.val))
  · rintro ⟨out, head, prev, pos, ntok⟩ ⟨hpn, hnt, hlen, hde⟩
    simp only at hpn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.a_fl_dna_parse_loop.body, lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      all_goals (repeat (first
        | (refine ⟨by scalar_tac, by scalar_tac, by assumption, by assumption, by scalar_tac⟩)
        | (intro hc; (try step*))
        | (casesm* _ × _; (try simp only []); (try step*))
        | (split <;> (try step*))
        | (step <;> (try step*))))
      all_goals (try scalar_tac)
    case isFalse hge =>
      exact ⟨hpn, hnt, hlen, hde⟩
  · exact ⟨hp, hntok, rfl, hdec⟩

end
attribute [local step] fl_dna_parse_loop_spec

section
attribute [local step] ite_true_spec

@[local step]
theorem fl_dna_parse_spec (input : Slice Std.U8) (out : Slice Std.U32) (cost : Array Std.U32 256#usize)
    (hlen : input.length ≤ out.length) :
    slot.a_fl_dna_parse input out cost ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_fl_dna_parse]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by assumption⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac)

end
attribute [local step] fl_dna_parse_spec

@[local step]
theorem fl_score_spec (l : Std.Usize) (d : Std.Usize) (litq : Std.Usize) :
    slot.a_fl_score l d litq ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_score]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_lg8_spec (x : Std.U32) :
    slot.a_fl_lg8 x ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_lg8]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_entropy256_loop_spec (h : Array Std.U32 256#usize) (tot : Std.U64) (acc : Std.U64) (i : Std.Usize)  :
    slot.a_fl_entropy256_loop h tot acc i ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_entropy256_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.a_fl_entropy256_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_entropy256_spec (h : Array Std.U32 256#usize) :
    slot.a_fl_entropy256 h ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_entropy256]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_lit_cost_spec (h0 : Std.Usize) :
    slot.a_fl_lit_cost h0 ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_lit_cost]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_walk_loop_spec (input : Slice Std.U8) (prev : Array Std.U16 32768#usize) (pos : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) (litq : Std.Usize) (nice : Std.Usize) (bl : Std.Usize) (bd : Std.Usize) (bs : Std.Usize) (cur : Std.Usize) (k : Std.Usize) (off : Std.Usize) (want : Std.U32)  :
    slot.a_fl_walk_loop input prev pos cap depth litq nice bl bd bs cur k off want ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_walk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => depth.val - s.2.2.2.2.1.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5, x6⟩ _
    simp only [slot.a_fl_walk_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem fl_walk_spec (input : Slice Std.U8) (prev : Array Std.U16 32768#usize) (pos : Std.Usize) (start : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) (nice : Std.Usize) :
    slot.a_fl_walk input prev pos start cap depth bl0 bs0 litq nice ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_walk]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_search_spec (input : Slice Std.U8) (head : Array Std.U16 16384#usize) (prev : Array Std.U16 32768#usize) (pos : Std.Usize) (depth : Std.Usize) (ins : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) (hsh : Std.U64) (nice : Std.Usize) :
    slot.a_fl_search input head prev pos depth ins bl0 bs0 litq hsh nice ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_search]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_insert_match_spec (input : Slice Std.U8) (head : Array Std.U16 16384#usize) (prev : Array Std.U16 32768#usize) («from» : Std.Usize) («to» : Std.Usize) (hsh : Std.U64) (ih : Std.Usize) (it : Std.Usize) :
    slot.a_fl_insert_match input head prev «from» «to» hsh ih it ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_insert_match]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_lits_spec (miss : Std.Usize) (acc : Std.Usize) :
    slot.a_fl_lits miss acc ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_lits]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_litq_spec (h0 : Std.Usize) :
    slot.a_fl_litq h0 ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_litq]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

@[local step]
theorem fl_hsh_spec (h0 : Std.Usize) :
    slot.a_fl_hsh h0 ⦃ fun _ => True ⦄ := by
  rw [slot.a_fl_hsh]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

section
attribute [local step] ite_true_spec

@[local step]
theorem fl_lazy_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize) (depth : Std.Usize) (depth2 : Std.Usize) (lazy : Std.Usize) (nice : Std.Usize) (ih : Std.Usize) (it : Std.Usize) (acc : Std.Usize) (litq : Std.Usize) (hsh : Std.U64) (head0 : Array Std.U16 16384#usize) (prev0 : Array Std.U16 32768#usize) (pos0 : Std.Usize) (ntok0 : Std.Usize) (carry0 : Std.Usize) (miss0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.a_fl_lazy_parse_loop input out0 n depth depth2 lazy nice ih it acc litq hsh head0 prev0 pos0 ntok0 carry0 miss0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := by
  rw [slot.a_fl_lazy_parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.1.val ≤ n.val ∧ s.2.2.2.2.1.val ≤ s.2.2.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.1.val) = some ((bytes input).take s.2.2.2.1.val))
  · rintro ⟨out, head, prev, pos, ntok, carry, miss⟩ ⟨hpn, hnt, hlen, hde⟩
    simp only at hpn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.a_fl_lazy_parse_loop.body, lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      all_goals (repeat (first
        | (refine ⟨by scalar_tac, by scalar_tac, by assumption, by assumption, by scalar_tac⟩)
        | (intro hc; (try step*))
        | (casesm* _ × _; (try simp only []); (try step*))
        | (split <;> (try step*))
        | (step <;> (try step*))))
      all_goals (try scalar_tac)
    case isFalse hge =>
      exact ⟨hpn, hnt, hlen, hde⟩
  · exact ⟨hp, hntok, rfl, hdec⟩

end
attribute [local step] fl_lazy_parse_loop_spec

section
attribute [local step] ite_true_spec

@[local step]
theorem fl_lazy_parse_spec (input : Slice Std.U8) (out : Slice Std.U32) (lh : Array Std.U32 256#usize) (cf : Array Std.Usize 8#usize)
    (hlen : input.length ≤ out.length) :
    slot.a_fl_lazy_parse input out lh cf ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_fl_lazy_parse]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by assumption⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac)

end
attribute [local step] fl_lazy_parse_spec

section
attribute [local step] ite_true_spec

@[local step]
theorem fl_part_spec (input : Slice Std.U8) (out : Slice Std.U32) (mc : Std.Usize) (fh : Array Std.U32 256#usize)
    (hlen : input.length ≤ out.length) :
    slot.a_fl_part input out mc fh ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_fl_part]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by assumption⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac)

end
attribute [local step] fl_part_spec

@[local step]
theorem prepare_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 65536#usize) (head3 : Array Std.U32 16384#usize) (shorts : Array Std.U32 4096#usize) (hs : Std.U32) (h3on : Std.Usize) («end» : Std.Usize) (p : Std.Usize)  :
    slot.a_prepare_loop input head prev head3 shorts h3on hs «end» p ⦃ fun _ => True ⦄ := by
  rw [slot.a_prepare_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «end».val - s.2.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4⟩ _
    simp only [slot.a_prepare_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial

@[local step]
theorem prepare_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 65536#usize) (head3 : Array Std.U32 16384#usize) (shorts : Array Std.U32 4096#usize) («from» : Std.Usize) (pos : Std.Usize) (hs : Std.U32) (h3on : Std.Usize) :
    slot.a_prepare input head prev head3 shorts «from» pos hs h3on ⦃ fun _ => True ⦄ := by
  rw [slot.a_prepare]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac

end EA

namespace EA
open Aeneas Aeneas.Std Result ControlFlow
open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr Matches emit_lit
  emit_match ite_ok)
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

attribute [local step] verified_spec lextra_spec dextra_spec emit_step_spec

theorem public_back_suffix_spec (input : Slice Std.U8) (p l d w k : Std.Usize)
    (hp : p.val ≤ input.length) (hw : w.val ≤ 258) (hkw : k.val + 1 ≤ w.val)
    (hl : l.val + k.val ≤ 258) (hd : d.val + k.val ≤ p.val)
    (hm : Matches input (p.val - k.val - d.val) (p.val - k.val) k.val) :
    slot.a_public_partial_loop0 input p l d w k ⦃ fun r =>
      r.val + 1 ≤ w.val ∧ l.val + r.val ≤ 258 ∧ d.val + r.val ≤ p.val ∧
      Matches input (p.val - r.val - d.val) (p.val - r.val) r.val ⦄ := by
  rw [slot.a_public_partial_loop0]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.loop.spec_decr_nat
    (measure := fun r => w.val - r.val)
    (inv := fun r => r.val + 1 ≤ w.val ∧ l.val + r.val ≤ 258 ∧ d.val + r.val ≤ p.val ∧
      Matches input (p.val - r.val - d.val) (p.val - r.val) r.val)
  · rintro k ⟨hkw, hl, hd, hm⟩
    simp only [slot.a_public_partial_loop0.body]
    step*
    all_goals first
      | exact ⟨hkw, hl, hd, hm⟩
      | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
          Matches.a_back_step (i4 := i4) (i7 := i7) (x := i5) (y := i8) hm (by scalar_tac)
            (by scalar_tac) (by scalar_tac) (by assumption) (by scalar_tac) (by scalar_tac)
            (by assumption) (by assumption) (by scalar_tac), by scalar_tac⟩)
  · exact ⟨hkw, hl, hd, hm⟩

@[local step]
theorem public_back_suffix_spec0 (input : Slice Std.U8) (p l d w : Std.Usize)
    (hp : p.val ≤ input.length) (hw : w.val ≤ 258) (hw4 : 1 ≤ w.val) (hl : l.val ≤ 258) (hd : d.val ≤ p.val) :
    slot.a_public_partial_loop0 input p l d w 0#usize ⦃ fun r =>
      r.val + 1 ≤ w.val ∧ l.val + r.val ≤ 258 ∧ d.val + r.val ≤ p.val ∧
      Matches input (p.val - r.val - d.val) (p.val - r.val) r.val ⦄ :=
  public_back_suffix_spec input p l d w 0#usize hp hw (by simpa using hw4) (by simpa using hl)
    (by simpa using hd) (by simpa using Matches.zero input (p.val - d.val) p.val)

theorem nearer_prefix_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 65536#usize)
    (pp nl oldd cur probes result : Std.Usize)
    (hinv : NearPrefix input pp.val nl.val result.val) :
    slot.a_nearer_prefix_loop input prev pp nl oldd cur probes result ⦃ fun r =>
      NearPrefix input pp.val nl.val r.val ⦄ := by
  rw [slot.a_nearer_prefix_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 4 - r.2.1.val)
    (inv := fun r => NearPrefix input pp.val nl.val r.2.2.val)
  · rintro ⟨cur, probes, result⟩ hinv
    simp only [slot.a_nearer_prefix_loop.body]
    step*
    all_goals first
      | exact hinv
      | (refine ⟨hinv, by scalar_tac⟩)
      | (refine ⟨Or.inr ?_, by scalar_tac⟩
         obtain ⟨h3, h258, hd1, hd32, hdp, hpl, hm⟩ := b_post (by assumption)
         exact ⟨h3, h258, hpl, hd1, hd32, hdp, hm⟩)
  · exact hinv

@[local step]
theorem nearer_prefix_spec (input : Slice Std.U8) (prev : Array Std.U32 65536#usize)
    (pp nl oldd : Std.Usize) :
    slot.a_nearer_prefix input prev pp nl oldd ⦃ fun r => NearPrefix input pp.val nl.val r.val ⦄ := by
  rw [slot.a_nearer_prefix]
  step*
  exact nearer_prefix_loop_spec input prev pp nl oldd cur 0#usize 0#usize (Or.inl (by simp))

@[local step]
theorem ext_ok_bound (input : Slice Std.U8) (pos l2 d2 : Std.Usize) :
    slot.a_ext_ok input pos l2 d2 ⦃ fun r => r.val ≤ 1 ⦄ := by
  rw [slot.a_ext_ok]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals scalar_tac

@[local step]
theorem public_span_better_loop_spec (input : Slice Std.U8) (costs : Array Std.U32 256#usize)
    (pos l2 aa bb tail j : Std.Usize) (hpos : pos.val + l2.val < input.length)
    (hl2 : l2.val ≤ 258) (hj : j.val ≤ l2.val + 1) :
    slot.a_public_span_better_loop input costs pos l2 aa bb tail j ⦃ fun r => r.val ≤ 1 ⦄ := by
  rw [slot.a_public_span_better_loop]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.loop.spec_decr_nat
    (measure := fun r => l2.val + 1 - r.2.val)
    (inv := fun r => r.2.val ≤ l2.val + 1)
  · rintro ⟨tail, j⟩ hj
    simp only [slot.a_public_span_better_loop.body]
    step*
    all_goals first
      | scalar_tac
      | exact ⟨by scalar_tac, by scalar_tac⟩
  · exact hj

@[local step]
theorem public_span_better_spec (input : Slice Std.U8) (costs : Array Std.U32 256#usize)
    (pos l1 d1 l2 d2 ex : Std.Usize) (hex : ex.val ≤ 1) :
    slot.a_public_span_better input costs pos l1 d1 l2 d2 ex ⦃ fun r => r.val ≤ 1 ⦄ := by
  rw [slot.a_public_span_better]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals first
    | scalar_tac
    | (split <;> step* <;> scalar_tac)

theorem public_keep_loop_spec (l w remain keep lc best chosen : Std.Usize)
    (hlw : l.val + w.val ≤ Std.Usize.max)
    (hk : 1 ≤ keep.val ∧ keep.val ≤ 3)
    (hchosen : chosen.val = 0 ∨ 1 ≤ chosen.val ∧ chosen.val ≤ 2 ∧ remain.val ≤ chosen.val) :
    slot.a_public_partial_loop1 l w remain keep lc best chosen ⦃ fun r =>
      r.val = 0 ∨ 1 ≤ r.val ∧ r.val ≤ 2 ∧ remain.val ≤ r.val ⦄ := by
  rw [slot.a_public_partial_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 3-r.1.val)
    (inv := fun r => (1 ≤ r.1.val ∧ r.1.val ≤ 3) ∧
      (r.2.2.2.val = 0 ∨ 1 ≤ r.2.2.2.val ∧ r.2.2.2.val ≤ 2 ∧ remain.val ≤ r.2.2.2.val))
  · rintro ⟨keep,lc,best,chosen⟩ ⟨hk,hchosen⟩
    simp only [slot.a_public_partial_loop1.body]
    step*
    all_goals first
      | exact hchosen
      | (apply Std.WP.spec_bind (Pₘ := fun bc =>
            bc.2.val=0 ∨ 1≤bc.2.val ∧ bc.2.val≤2 ∧ remain.val≤bc.2.val)
         · split <;> step*
           all_goals first | exact hchosen | (right; scalar_tac)
         · rintro ⟨best1,chosen1⟩ hchosen1
           step*
           exact ⟨by scalar_tac,by scalar_tac,hchosen1,by scalar_tac⟩)
  · exact ⟨hk,hchosen⟩

@[local step]
theorem public_keep_spec (l w remain oldcost : Std.Usize)
    (hlw : l.val + w.val ≤ Std.Usize.max) :
    slot.a_public_partial_loop1 l w remain 1#usize 0#usize oldcost 0#usize ⦃ fun r =>
      r.val = 0 ∨ 1 ≤ r.val ∧ r.val ≤ 2 ∧ remain.val ≤ r.val ⦄ :=
  public_keep_loop_spec l w remain 1#usize 0#usize oldcost 0#usize hlw
    (by scalar_tac) (by simp)

end EA

namespace EA
open Aeneas Aeneas.Std Result ControlFlow
open LZ77 (toks bytes bytes_length bytes_getElem! Matches emit_lit emit_match ite_ok)
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
attribute [local step] public_back_suffix_spec0 nearer_prefix_spec lextra_spec dextra_spec public_keep_spec

theorem public_partial_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (prev : Array Std.U32 65536#usize) (nt p l d : Std.Usize) (t : Std.U32) (w : Std.Usize)
    (costs : Array Std.U32 256#usize)
    (hdec : ADec input out nt.val p.val) (hm : AMatchAt input p.val l.val d.val)
    (h0 : 0 < nt.val) (hntl : nt.val ≤ out.length)
    (ht : (out.val[nt.val - 1]!).val = t.val) (ht24 : 16777216 ≤ t.val)
    (hw : w.val = (t.val - 16777216) % 256 + 3) :
    slot.a_public_partial input out prev nt p l d t w costs ⦃ fun r =>
      r.2.length = out.length ∧ ADec input r.2 r.1.1.val r.1.2.1.val ∧
      AMatchAt input r.1.2.1.val r.1.2.2.val d.val ∧
      r.1.2.1.val + r.1.2.2.val = p.val + l.val ∧ r.1.2.1.val ≤ p.val ⦄ := by
  rw [slot.a_public_partial]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  have hm' := hm
  obtain ⟨h3, h258, hpl, hd1, hd32, hdp, hmm⟩ := hm'
  have hdec' := hdec
  obtain ⟨hps, hntp, hso, hde⟩ := hdec'
  have hwt : w.val = LZ77.tokLen (out.val[nt.val - 1]!).val := by
    rw [ht, hw]; simp only [LZ77.tokLen, LZ77.MATCH_BASE]
  have ht256 : 256 ≤ (out.val[nt.val - 1]!).val := by rw [ht]; omega
  have hw3 : 3 ≤ w.val := by scalar_tac
  have hw258 : w.val ≤ 258 := by scalar_tac
  obtain ⟨hwp,hpre⟩ := ADec.pop_match hdec h0 hntl ht256
  rw [←hwt] at hwp hpre
  have hntpre : nt.val-1 ≤ p.val-w.val := hpre.2.1
  have hpin : p.val < input.length := by omega
  step*
  all_goals try exact ⟨rfl,hdec,hm,rfl,le_refl _⟩
  focus
       have hkeep : 1≤chosen.val ∧ chosen.val≤2 ∧ remain.val≤chosen.val := by
         rcases chosen_post with hz | hz
         · exfalso; scalar_tac
         · exact hz
       have hbyte0 : i11.val = (input.val[pp.val]!).val := by
         rw [getElem!_pos input.val pp.val (by scalar_tac),←i9_post,i11_post,
           Std.U8.cast_U32_val_eq]
       have hfirst := absorb_one_dec (out1:=index_mut_back i11) (idx:=i10) (v:=i11) hdec h0 hntl ht256 hwt hw3 hpin i10_post1
         (by simpa only [pp_post1] using hbyte0) (by rw [__post2])
       have hfirstlen : (index_mut_back i11).length=out.length := by
         rw [__post2,Std.Slice.set_length]
       apply Std.WP.spec_bind (Pₘ := fun out1 => out1.length=out.length ∧
           ADec input out1 (nt.val-1+chosen.val) (pp.val+chosen.val))
       · split
         case isTrue htwo =>
           step*
           have hbyte1 : i14.val=(input.val[pp.val+1]!).val := by
             rw [show pp.val+1=i12.val by scalar_tac,
               getElem!_pos input.val i12.val (by scalar_tac),←i13_post,i14_post,
               Std.U8.cast_U32_val_eq]
           have htwoDec := absorb_two_dec (out1:=index_mut_back i11) (out2:=out1) (nt0:=i10) (nt1:=nt) (v0:=i11) (v1:=i14) hdec h0 hntl ht256 hwt hw3 pp_post1
             i10_post1 rfl hbyte0 hbyte1 (by rw [__post2]) out1_post
           refine ⟨htwoDec.1,?_⟩
           rw [show nt.val-1+chosen.val=nt.val+1 by scalar_tac,
             show pp.val+chosen.val=p.val-w.val+2 by scalar_tac]
           exact htwoDec.2
         case isFalse hone =>
           step*
       · rintro out1 ⟨hlen,hnewdec⟩
         step*
         apply absorb_match_post (nt:=nt.val) (keep:=chosen.val) hm
           (by simpa only [pp_post1,i12_post,i10_post1] using hnewdec) hlen k_post4 pp_post2
           (by scalar_tac) (by scalar_tac) k_post2 k_post3
           (by scalar_tac) (by scalar_tac)
  all_goals (
       apply Std.WP.spec_bind (Pₘ := fun kk => kk.val≤k.val ∧ kk.val+4≤w.val)
       · split <;> step* <;> constructor <;> scalar_tac
       · rintro k1 ⟨hk1k,hk1w⟩
         have hkmatch := Matches.back_trim k_post4 hk1k k_post3
         step*
         all_goals first
           | exact ⟨rfl,hdec,hm,rfl,le_refl _⟩
           | (have hold : NearPrefix input pp.val nl.val oldd.val := by
                rw [pp_post1]
                apply old_prefix_near hdec h0 hntl ht256 hwt
                · simp only [LZ77.tokDist,LZ77.MATCH_BASE];rw [ht];scalar_tac
                · scalar_tac
                · scalar_tac
              apply Std.WP.spec_bind (Pₘ := fun nd => NearPrefix input pp.val nl.val nd.val)
              · split <;> step*
                all_goals first | exact near_post | exact hold | exact Or.inl (by simp)
              · intro nd hnd
                split
                case isTrue hndpos =>
                  rcases hnd with hz | hndm
                  · exfalso;scalar_tac
                  · have hndm' := hndm
                    obtain ⟨hnl3,hnl258,hppnl,hnd1,hnd32,hndpp,hndmatch⟩ := hndm'
                    step*
                    exact fold_part_post hdec hm (by omega) hntl ht256 hwt hkmatch
                      (Or.inr hndm) out1_post (by omega) (by omega) (by omega)
                      pp_post1 nl_post1 (by scalar_tac) (by scalar_tac)
                      (by simp only [LZ77.mkMatch,LZ77.MATCH_BASE];scalar_tac)
                      (by scalar_tac) (by scalar_tac)
                case isFalse hndpos =>
                  exact ⟨rfl,hdec,hm,rfl,le_refl _⟩))

end EA

namespace EA
open Aeneas Aeneas.Std Result ControlFlow
open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr Matches emit_lit
  emit_match ite_ok)
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
attribute [local step] public_partial_spec verified_spec emit_step_spec

theorem public_back_step_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (prev : Array Std.U32 65536#usize) (costs : Array Std.U32 256#usize)
    (nt p l d back : Std.Usize)
    (L E P0 : Nat) (hinv : ABackInv input L d.val E P0 out nt.val p.val l.val)
    (hnt0 : 0 < nt.val) (hntl : nt.val ≤ out.length) (hdp : d.val < p.val)
    (hl : l.val < 258) (hback : back.val < 16) :
    slot.a_public_back_step input out prev nt p l d back costs ⦃ fun r =>
      ABackInv input L d.val E P0 r.2 r.1.1.val r.1.2.1.val r.1.2.2.1.val ∧
      16 - r.1.2.2.2.val < 16 - back.val ⦄ := by
  rw [slot.a_public_back_step]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  have hinv' := hinv
  obtain ⟨hdec, hL, hm, hE, hP⟩ := hinv'
  have hm' := hm
  obtain ⟨h3, h258, hpl, hd1, hd32, hdp', hmm⟩ := hm'
  have hps : p.val ≤ input.length := hdec.1
  step*
  all_goals first
    | (rw [← i_post1, getElem!_pos out.val i.val (by scalar_tac), ← t_post])
    | (refine ⟨ABackInv.lit (t := t) (x := i2) (y := i4) (i4 := i3) hinv
          i_post1 hntl (by omega) (by scalar_tac) t_post (by assumption)
          i1_post1 (by scalar_tac) i2_post (by assumption) i3_post1
          (by scalar_tac) i4_post hl hdp i5_post, by scalar_tac⟩)
    | (refine ⟨ABackInv.part hinv (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption), by scalar_tac⟩)
    | (have htv : (out.val[nt.val - 1]!).val = t.val := by
         rw [← i_post1, getElem!_pos out.val i.val (by scalar_tac), ← t_post]
       have hwv : w.val = LZ77.tokLen (out.val[nt.val - 1]!).val := by
         rw [htv]
         simp only [LZ77.tokLen, LZ77.MATCH_BASE]
         scalar_tac
       obtain ⟨hwl, hdec'⟩ := ADec.pop_match hdec hnt0 hntl (by rw [htv]; scalar_tac)
       rw [← hwv] at hdec'
       have hb := b_post (by assumption)
       have hm' := AMatchAt.back_match (w := w.val) hm (by scalar_tac) (by scalar_tac)
         (by scalar_tac) (by simpa only [i9_post1] using hb.2.2.2.2.2.2)
       rw [i_post1, i9_post1, i10_post, i11_post]
       exact ⟨⟨hdec', hL, hm', by omega, by omega⟩, by omega⟩)

attribute [local step] public_back_step_spec

theorem public_back_loop_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (prev : Array Std.U32 65536#usize) (costs : Array Std.U32 256#usize)
    (d nt p l back : Std.Usize)
    (L E P0 : Nat) (hinv : ABackInv input L d.val E P0 out nt.val p.val l.val)
    :
    slot.a_public_back_loop input out prev d costs nt p l back ⦃ fun r =>
      ABackInv input L d.val E P0 r.1 r.2.1.val r.2.2.1.val r.2.2.2.val ⦄ := by
  rw [slot.a_public_back_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 16 - r.2.2.2.2.val)
    (inv := fun r => ABackInv input L d.val E P0 r.1 r.2.1.val r.2.2.1.val
      r.2.2.2.1.val)
  · rintro ⟨out, nt, p, l, back⟩ hinv
    simp only [slot.a_public_back_loop.body]
    step*
  · exact hinv

attribute [local step] public_back_loop_spec

@[local step]
theorem public_back_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (prev : Array Std.U32 65536#usize) (costs : Array Std.U32 256#usize)
    (nt p l d : Std.Usize)
    (hdec : ADec input out nt.val p.val) (hm : AMatchAt input p.val l.val d.val) :
    slot.a_public_back input out prev nt p l d costs ⦃ fun r =>
      ABackInv input out.length d.val (p.val + l.val) p.val
        r.2 r.1.1.val r.1.2.1.val r.1.2.2.val ⦄ := by
  rw [slot.a_public_back]
  have hinv : ABackInv input out.length d.val (p.val + l.val) p.val
      out nt.val p.val l.val := ⟨hdec, rfl, hm, rfl, le_refl _⟩
  apply Std.WP.spec_bind (public_back_loop_spec input out prev costs d nt p l 0#usize
    out.length (p.val + l.val) p.val hinv)
  rintro ⟨out1, nt1, p1, l1⟩ h
  exact h

@[local step]
theorem public_back_gate_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (prev : Array Std.U32 65536#usize) (costs : Array Std.U32 256#usize)
    (nt p l d : Std.Usize)
    (hdec : ADec input out nt.val p.val) (hm : AMatchAt input p.val l.val d.val) :
    slot.a_public_back_gate input out prev nt p l d costs ⦃ fun r =>
      ABackInv input out.length d.val (p.val + l.val) p.val
        r.2 r.1.1.val r.1.2.1.val r.1.2.2.val ⦄ := by
  rw [slot.a_public_back_gate]
  have hinv : ABackInv input out.length d.val (p.val + l.val) p.val
      out nt.val p.val l.val := ⟨hdec, rfl, hm, rfl, le_refl _⟩
  have hm' := hm
  obtain ⟨h3, h258, hpl, hd1, hd32, hdp, hmm⟩ := hm'
  split
  case isTrue hgt =>
    step*
  case isFalse hle =>
    simpa using hinv

@[local step]
theorem public_emit_join_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (prev : Array Std.U32 65536#usize) (pos d l ntok : Std.Usize)
    (costs : Array Std.U32 256#usize)
    (hout : input.length ≤ out.length) (hpos : pos.val < input.length)
    (hntok : ntok.val ≤ pos.val)
    (hdec : LZ77.decode (toks out ntok.val) = some ((bytes input).take pos.val)) :
    slot.a_public_emit_join input out prev pos d l ntok costs ⦃ fun r =>
      pos.val < r.1.2.val ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.a_public_emit_join]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (verified_spec input pos d l)
  intro b hb
  split
  case isTrue hbt =>
    obtain ⟨hl3, hl258, hd1, hdmax, hdpos, hend, hmatch⟩ := hb hbt
    have hm : AMatchAt input pos.val l.val d.val :=
      ⟨hl3, hl258, hend, hd1, hdmax, hdpos, hmatch⟩
    have ha : ADec input out ntok.val pos.val := ⟨by omega, hntok, hout, hdec⟩
    apply Std.WP.spec_bind (public_back_gate_spec input out prev costs ntok pos l d ha hm)
    rintro ⟨⟨nt1, p1, l1⟩, out1⟩ hinv
    obtain ⟨hdec1, hL, hm1, hE, hP⟩ := hinv
    have hm1' := hm1
    obtain ⟨h3, h258, hpl, hd1, hd32, hdp, hmm⟩ := hm1'
    have hdec1' := hdec1
    obtain ⟨hps, hntp, hso, hde⟩ := hdec1'
    step*
    have htok : i9.val = LZ77.mkMatch d.val l1.val := by
      simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i9_post, i3_post, i2_post]
      scalar_tac
    have hdec2 := ADec.match hdec1 hm1 nt1 rfl i9 htok
    rw [← out2_post] at hdec2
    obtain ⟨hpos2, hntpos2, hout2, hdecode2⟩ := hdec2
    refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, ?_⟩
    · rw [out2_post, Std.Slice.set_length]; exact hL
    · rw [i10_post, i11_post]
      exact hdecode2
  case isFalse hbf =>
    exact emit_step_spec input out pos d l 1#usize ntok hout hpos hntok hdec

end EA

namespace EA
open Aeneas Aeneas.Std Result ControlFlow
open LZ77 (toks bytes bytes_getElem! Matches emit_lit emit_match)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local step] ld4_spec ld8_spec first_diff_spec fast_len_loop_spec fast_len_spec hashp_spec hash3_spec dextra_spec lextra_spec score_spec lg8_spec sample_loop_spec sample_spec entropy256_loop_spec entropy256_spec share_loop_spec share_spec low_mode_spec lit_cost_spec m3_mode_spec h3_mode_spec numeric_spec walk_loop_spec walk_spec lwalk_loop_spec lwalk_spec cand3_spec upd3_spec search_spec insert_range_loop_spec insert_range_spec insert_range3_loop_spec insert_range3_spec insert_match_spec tw8_spec tw4_spec tail_eq_spec short_eq_spec words_eq_spec match_len_spec emit_lits_spec emit_step_spec lazy_probe_spec ext_ok_spec fl_tw8_spec fl_tw4_spec fl_tail_eq_spec fl_short_eq_spec fl_words_eq_spec fl_match_len_spec fl_emit_lits_spec fl_emit_step_spec fl_byte_spec fl_ld4_spec fl_ld8_spec fl_len_loop_spec fl_len_spec fl_hashp_spec fl_log16_spec fl_sample_loop_spec fl_sample_spec fl_costs_loop0_spec fl_costs_loop1_spec fl_costs_spec fl_ent_loop0_spec fl_ent_loop1_spec fl_ent_spec fl_stats_loop0_spec fl_stats_loop1_spec fl_stats_spec fl_probe_chunk_loop_spec fl_weights_loop_spec fl_weights_spec fl_mode_spec fl_config_spec fl_lit_parse_spec fl_rle_parse_loop_spec fl_rle_parse_spec fl_cheap_run_loop_spec fl_cheap_run_spec fl_span_cost_loop_spec fl_dextra_spec fl_lextra_spec fl_dna_ok_spec fl_dwalk_loop_spec fl_dwalk_spec fl_dsearch_spec fl_tinsert_loop_spec fl_tinsert_spec fl_insert_loop_spec fl_insert_spec fl_dna_parse_loop_spec fl_dna_parse_spec fl_score_spec fl_lg8_spec fl_entropy256_loop_spec fl_entropy256_spec fl_lit_cost_spec fl_walk_loop_spec fl_walk_spec fl_search_spec fl_insert_match_spec fl_lits_spec fl_litq_spec fl_hsh_spec fl_lazy_parse_loop_spec fl_lazy_parse_spec fl_part_spec prepare_loop_spec prepare_spec ite_true_spec
attribute [local step] ext_ok_bound public_span_better_spec public_emit_join_spec
attribute [-step] ite_true_spec ext_ok_spec

section

@[local step]
theorem main_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize) (head0 : Array Std.U32 65536#usize) (prev0 : Array Std.U32 65536#usize) (head30 : Array Std.U32 16384#usize) (shorts0 : Array Std.U32 4096#usize) (span_costs : Array Std.U32 256#usize) (litq : Std.Usize) (hs : Std.U32) (acc : Std.U64) (depth : Std.Usize) (lz : Std.Usize) (p2 : Std.Usize) (h3on : Std.Usize) (pos0 : Std.Usize) (ntok0 : Std.Usize) (carry0 : Std.Usize) (miss0 : Std.Usize) (filled0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.a_main_parse_loop input out0 n head0 prev0 head30 shorts0 span_costs litq hs acc depth lz p2 h3on pos0 ntok0 carry0 miss0 filled0 ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.a_main_parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.2.2.1.val ≤ n.val ∧ s.2.2.2.2.2.2.1.val ≤ s.2.2.2.2.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.2.2.1.val) = some ((bytes input).take s.2.2.2.2.2.1.val))
  · rintro ⟨out, head, prev, head3, shorts, pos, ntok, carry, miss, filled⟩ ⟨hpn, hnt, hlen, hde⟩
    simp only at hpn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.a_main_parse_loop.body, lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      all_goals (repeat (first
        | (refine ⟨by scalar_tac, by scalar_tac, by assumption, by assumption, by scalar_tac⟩)
        | (intro hc; (try step*))
        | (casesm* _ × _; (try simp only []); (try step*))
        | (split <;> (try step*))
        | (step <;> (try step*))))
      all_goals (try scalar_tac)
    case isFalse hge =>
      have hpn' : pos.val = input.length := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      unfold LZ77.Valid
      rw [hde, hpn']
      simp
  · exact ⟨hp, hntok, rfl, hdec⟩

end
attribute [local step] main_parse_loop_spec

section

@[local step]
theorem main_parse_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos0 : Std.Usize) (ntok0 : Std.Usize)
    (hlen : input.length ≤ out.length)
    (hp : pos0.val ≤ input.length) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.a_main_parse input out pos0 ntok0 ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.a_main_parse]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, valid_of_decode (by assumption) (by scalar_tac)⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac)

end
attribute [local step] main_parse_spec

section

@[local step]
theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.a_parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.a_parse]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, valid_of_decode (by assumption) (by scalar_tac)⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac)

end
attribute [local step] parse_spec

end EA

namespace EB
open Aeneas Aeneas.Std Result ControlFlow

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open LZ77 (toks bytes bytes_getElem! Matches emit_lit emit_match)

@[local step]
theorem lift_spec {α : Type} (x : α) : lift x ⦃ fun y => y = x ⦄ := by
  simp [lift, WP.spec_ok]

@[local step]
theorem get0_spec (v : Slice Std.U32) (i : Std.Usize) : slot.b_get0 v i ⦃ fun _ => True ⦄ := by
  rw [slot.b_get0]; split <;> step*

@[local scalar_tac x &&& y]
theorem nat_and_le_right (x y : Nat) : x &&& y ≤ y := Nat.and_le_right

@[local scalar_tac x >>> y]
theorem nat_shiftRight_le (x y : Nat) : x >>> y ≤ x := Nat.shiftRight_le x y

theorem numBits_ge : 32 ≤ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp [*]

@[local scalar_tac System.Platform.numBits]
theorem numBits_ge' : 32 ≤ System.Platform.numBits := numBits_ge

theorem lz_le_w {w : Nat} (x : BitVec w) : BitVec.leadingZeros x ≤ w := by
  unfold BitVec.leadingZeros; split <;> omega

theorem lz32_val (x : Std.U32) :
    (core.num.U32.leading_zeros x).val = BitVec.leadingZeros x.bv := by
  simp only [core.num.U32.leading_zeros, UScalar.val]
  have := lz_le_w x.bv
  apply Nat.mod_eq_of_lt
  simp at this ⊢
  omega

theorem lz32_eq (x : Std.U32) (h : x.val ≠ 0) :
    (core.num.U32.leading_zeros x).val = 31 - Nat.log 2 x.val := by
  rw [lz32_val]
  unfold BitVec.leadingZeros
  have hx : x.bv ≠ 0 := by
    intro h0; apply h; show x.bv.toNat = 0; rw [h0]; rfl
  rw [if_neg hx, UScalar.bv_toNat]
  omega

theorem lz32_le (x : Std.U32) : (core.num.U32.leading_zeros x).val ≤ 32 := by
  rw [lz32_val]; exact lz_le_w x.bv

theorem lz32_le_of_pow_le (x : Std.U32) (k : Nat) (h : 2 ^ k ≤ x.val) :
    (core.num.U32.leading_zeros x).val + k ≤ 31 := by
  have hx : x.val ≠ 0 := by have := Nat.one_le_two_pow (n := k); omega
  rw [lz32_eq x hx]
  have hk : k ≤ Nat.log 2 x.val := Nat.le_log_of_pow_le (by norm_num) h
  have : x.val < 2 ^ 32 := by scalar_tac
  have hl : Nat.log 2 x.val < 32 := Nat.log_lt_of_lt_pow (by omega) this
  omega

theorem lz32_ge_of_lt_pow (x : Std.U32) (k : Nat) (h : x.val < 2 ^ k) :
    32 - k ≤ (core.num.U32.leading_zeros x).val := by
  by_cases hx : x.val = 0
  · rw [lz32_val]; unfold BitVec.leadingZeros
    have : x.bv = 0 := by
      apply BitVec.eq_of_toNat_eq; rw [UScalar.bv_toNat]; simpa using hx
    rw [if_pos this]; omega
  · rw [lz32_eq x hx]
    have hl : Nat.log 2 x.val < k := Nat.log_lt_of_lt_pow hx h
    omega

theorem lz64_val (x : Std.U64) :
    (core.num.U64.leading_zeros x).val = BitVec.leadingZeros x.bv := by
  simp only [core.num.U64.leading_zeros, UScalar.val]
  have := lz_le_w x.bv
  apply Nat.mod_eq_of_lt
  simp at this ⊢
  omega

theorem lz64_le (x : Std.U64) : (core.num.U64.leading_zeros x).val ≤ 64 := by
  rw [lz64_val]; exact lz_le_w x.bv

@[local scalar_tac core.num.U32.leading_zeros x]
theorem lz32_bound (x : Std.U32) :
    (core.num.U32.leading_zeros x).val ≤ 32 ∧
      (x.val = 0 ∨ (core.num.U32.leading_zeros x).val ≤ 31) := by
  refine ⟨lz32_le x, ?_⟩
  by_cases h : x.val = 0
  · exact Or.inl h
  · right; rw [lz32_eq x h]; omega

@[local scalar_tac core.num.U64.leading_zeros x]
theorem lz64_bound (x : Std.U64) : (core.num.U64.leading_zeros x).val ≤ 64 := lz64_le x

def LeAll {ty : UScalarTy} (l : List (UScalar ty)) (B : Nat) : Prop :=
  ∀ j (h : j < l.length), (l[j]).val ≤ B

theorem LeAll_get {ty : UScalarTy} {l : List (UScalar ty)} {B : Nat} (hl : LeAll l B)
    (j : Nat) (hj : j < l.length) : (l[j]).val ≤ B := hl j hj

theorem LeAll_get! {ty : UScalarTy} {l : List (UScalar ty)} {B : Nat} (hl : LeAll l B)
    (j : Nat) (hj : j < l.length) : (l[j]!).val ≤ B := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact hl j hj

theorem LeAll_mono {ty : UScalarTy} {l : List (UScalar ty)} {B B' : Nat} (hl : LeAll l B)
    (h : B ≤ B') : LeAll l B' := fun j hj => Nat.le_trans (hl j hj) h

theorem LeAll_replicate {ty : UScalarTy} (n : Nat) (x : UScalar ty) (B : Nat) (h : x.val ≤ B) :
    LeAll (List.replicate n x) B := by
  intro j hj; simp [List.getElem_replicate]; exact h

theorem LeAll_set {ty : UScalarTy} {l : List (UScalar ty)} {B : Nat} (hl : LeAll l B)
    (i : Nat) (x : UScalar ty) (hx : x.val ≤ B) : LeAll (l.set i x) B := by
  intro j hj
  rw [List.getElem_set]
  split
  · exact hx
  · exact hl j (by simpa using hj)

theorem LeAll_append {ty : UScalarTy} {l : List (UScalar ty)} {B : Nat} (hl : LeAll l B)
    (x : UScalar ty) (hx : x.val ≤ B) : LeAll (l ++ [x]) B := by
  intro j hj
  rw [List.getElem_append]
  split
  · exact hl j (by assumption)
  · simp; exact hx

theorem LeAll_set_succ {ty : UScalarTy} {l : List (UScalar ty)} {t : Nat} (hl : LeAll l t)
    (i : Nat) (x : UScalar ty) (hx : x.val ≤ t + 1) : LeAll (l.set i x) (t + 1) :=
  LeAll_set (LeAll_mono hl (Nat.le_succ t)) i x hx

def DpNextl (nextl : Array Std.U16 512#usize) : Prop := ∀ j, j < 512 → j < (nextl.val[j]!).val

theorem dp_size {n : Nat} (h : n + n ≤ Std.Usize.max) : n + 2147483648 ≤ Std.Usize.max := by
  have : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
    simp [Std.Usize.max, Std.Usize.numBits]
  rcases System.Platform.numBits_eq with h32 | h64
  · rw [this, h32] at h ⊢; omega
  · rw [this, h64] at h ⊢; omega

theorem dp_RING_val : slot.B_RING.val = 8192 := by simp [slot.B_RING]
theorem dp_WN_val : slot.B_WN.val = 32768 := by simp [slot.B_WN]
theorem dp_H3N_val : slot.B_H3N.val = 16384 := by simp [slot.B_H3N]
theorem dp_H4N_val : slot.B_H4N.val = 65536 := by simp [slot.B_H4N]
theorem dp_H7N_val : slot.B_H7N.val = 65536 := by simp [slot.B_H7N]
theorem dp_H3B_bound : 1 ≤ slot.B_H3B.val ∧ slot.B_H3B.val ≤ 32 := by simp [slot.B_H3B]
theorem dp_H4B_bound : 1 ≤ slot.B_H4B.val ∧ slot.B_H4B.val ≤ 32 := by simp [slot.B_H4B]
theorem dp_H7B_bound : 1 ≤ slot.B_H7B.val ∧ slot.B_H7B.val ≤ 64 := by simp [slot.B_H7B]
theorem dp_KB7_bound : slot.B_KB7.val ≤ 8 := by simp [slot.B_KB7]
theorem dp_UPD_bound : slot.B_UPD.val ≤ 1048576 := by simp [slot.B_UPD]
theorem dp_TMAX_bound : slot.B_TMAX.val ≤ 1048576 := by simp [slot.B_TMAX]
theorem dp_BEXT_TOP_bound : slot.B_BEXT_TOP.val ≤ 1048576 := by simp [slot.B_BEXT_TOP]

theorem dp_FRAC_le : LeAll slot.B_FRAC.val 16 := by
  unfold slot.B_FRAC LeAll; simp only [Array.make]; decide

theorem dp_shr9 (c : Std.U32) : c.val >>> 9 < 8388608 := by
  rw [Nat.shiftRight_eq_div_pow]
  have : c.val < 2 ^ 32 := by scalar_tac
  omega

theorem dp_wadd_self (n : Std.Usize) (h : n.val < (core.num.Usize.wrapping_add n n).val) :
    n.val + n.val ≤ Std.Usize.max := by
  rw [core.num.Usize.wrapping_add_val_eq] at h
  have hs : Std.Usize.max = UScalar.size .Usize - 1 := by
    simp [Std.Usize.max, Std.Usize.size, Std.Usize.numBits]
  have hn : n.val < UScalar.size .Usize := by
    have := n.hBounds; simp only [UScalar.size]; exact this
  by_contra hc
  have h2 : UScalar.size .Usize ≤ n.val + n.val := by omega
  rw [Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at h
  omega

theorem dp_or_one_le (x : Nat) : x ||| 1 ≤ x + 1 := by
  have h := Nat.two_pow_add_eq_or_of_lt (i := 1) (b := 1) (by omega) (x / 2)
  have hx : x ||| 1 = 2 ^ 1 * (x / 2) ||| 1 := by
    rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
    · have : x = 2 ^ 1 * (x / 2) := by omega
      conv_lhs => rw [this]
    · have e := Nat.two_pow_add_eq_or_of_lt (i := 1) (b := 1) (by omega) (x / 2)
      have : x = 2 ^ 1 * (x / 2) ||| 1 := by omega
      conv_lhs => rw [this]
      rw [Nat.or_assoc, Nat.or_self]
  rw [hx, ← h]
  omega

theorem dp_LeAll_repeat {ty : UScalarTy} (n : Std.Usize) (x : UScalar ty) (B : Nat) (h : x.val ≤ B) :
    LeAll (Array.repeat n x).val B := by
  rw [Array.repeat_val]; exact LeAll_replicate _ _ _ h

theorem dp_LeAll_set_of_eq {ty : UScalarTy} {n : Std.Usize} {a r : Array (UScalar ty) n} {i : Std.Usize}
    {v : UScalar ty} {B : Nat} (hr : r = a.set i v) (ha : LeAll a.val B) (hv : v.val ≤ B) : LeAll r.val B := by
  rw [hr, Array.set_val_eq]; exact LeAll_set ha _ _ hv

theorem dp_getElem!_set {ty : UScalarTy} (l : List (UScalar ty)) (i j : Nat) (x : UScalar ty)
    (hi : i < l.length) : (l.set i x)[j]! = if i = j then x else l[j]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  split
  · simp [*]
  · rfl

@[local step] theorem be8_spec (s : Slice Std.U8) (i : Std.Usize) (h : i.val + 8 ≤ Std.Usize.max) :
    slot.b_be8 s i ⦃ fun _ => True ⦄ := by
  rw [slot.b_be8]
  step*

@[local step]
theorem common_loop0_spec (s : Slice Std.U8) (a b cap k : Std.Usize) (run : Std.U32)
    (ha : a.val + cap.val + 8 ≤ Std.Usize.max) (hb : b.val + cap.val + 8 ≤ Std.Usize.max) (hk : k.val ≤ cap.val) :
    slot.b_common_loop0 s a b cap k run ⦃ fun r => r.1.val ≤ cap.val ⦄ := by
  rw [slot.b_common_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (k', run') => cap.val + 9 - k'.val + run'.val)
    (inv := fun (k', _) => k'.val ≤ cap.val)
  · rintro ⟨k', run'⟩ hk'
    simp only [slot.b_common_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals try (have := lz64_bound x)
    all_goals scalar_tac
  · exact hk

@[local step]
theorem common_loop1_spec (s : Slice Std.U8) (a b cap k : Std.Usize) (run : Std.U32)
    (ha : a.val + cap.val + 8 ≤ Std.Usize.max) (hb : b.val + cap.val + 8 ≤ Std.Usize.max) (hk : k.val ≤ cap.val) :
    slot.b_common_loop1 s a b cap k run ⦃ fun r => r.val ≤ cap.val ⦄ := by
  rw [slot.b_common_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (k', run') => cap.val + 1 - k'.val + run'.val)
    (inv := fun (k', _) => k'.val ≤ cap.val)
  · rintro ⟨k', run'⟩ hk'
    simp only [slot.b_common_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hk

@[local step] theorem common_spec (s : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val + 8 ≤ Std.Usize.max) (hb : b.val + cap.val + 8 ≤ Std.Usize.max) :
    slot.b_common s a b cap ⦃ fun r => r.val ≤ cap.val ⦄ := by
  rw [slot.b_common]
  step*

@[local step] theorem hash3_spec (x : Std.U32) : slot.b_hash3 x ⦃ fun r => r.val < 16384 ⦄ := by
  have := dp_H3B_bound
  have := dp_H3N_val
  rw [slot.b_hash3]
  step*

@[local step] theorem hash4_spec (x : Std.U32) : slot.b_hash4 x ⦃ fun r => r.val < 65536 ⦄ := by
  have := dp_H4B_bound
  have := dp_H4N_val
  rw [slot.b_hash4]
  step*

@[local step] theorem hash7_spec (x : Std.U64) : slot.b_hash7 x ⦃ fun r => r.val < 65536 ⦄ := by
  have := dp_H7B_bound
  have := dp_H7N_val
  rw [slot.b_hash7]
  step*

@[local step] theorem probe_spec (s : Slice Std.U8) (c i : Std.Usize) (b8 : Std.U64) (cap best : Std.Usize)
    (hc : c.val ≤ i.val) (hcap : 9 ≤ cap.val) (hic : i.val + cap.val ≤ s.length)
    (hs8 : s.length + 8 ≤ Std.Usize.max) :
    slot.b_probe s c i b8 cap best ⦃ fun r => r.val ≤ cap.val ∧ (r.val = 0 ∨ best.val < r.val) ⦄ := by
  rw [slot.b_probe]
  step*
  repeat' (split <;> step*)
  all_goals try (have := lz64_bound x)
  all_goals scalar_tac

@[local step]
theorem walk_loop_spec (s : Slice Std.U8) (prev) (i : Std.Usize) (b8 : Std.U64) (cap : Std.Usize)
    (cands) (nc best c k : Std.Usize)
    (hc : c.val ≤ i.val) (hcap : 9 ≤ cap.val) (hic : i.val + cap.val ≤ s.length)
    (hs8 : s.length + 8 ≤ Std.Usize.max) (hb : best.val ≤ cap.val) :
    slot.b_walk_loop s prev i b8 cap cands nc best c k ⦃ fun r => best.val ≤ r.2.2.val ∧ r.2.2.val ≤ cap.val ⦄ := by
  have hwn := dp_WN_val
  rw [slot.b_walk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, k') => k'.val)
    (inv := fun (_, _, best', c', _) => c'.val ≤ i.val ∧ best.val ≤ best'.val ∧ best'.val ≤ cap.val)
  · rintro ⟨cands', nc', best', c', k'⟩ ⟨h1, h2, h3⟩
    simp only [slot.b_walk_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hc, le_refl _, hb⟩

@[local step] theorem walk_spec (s : Slice Std.U8) (prev) (i start depth : Std.Usize) (b8 : Std.U64)
    (cap : Std.Usize) (cands) (nc0 best0 : Std.Usize)
    (hst : start.val ≤ i.val) (hcap : 9 ≤ cap.val) (hic : i.val + cap.val ≤ s.length)
    (hs8 : s.length + 8 ≤ Std.Usize.max) (hb : best0.val ≤ cap.val) :
    slot.b_walk s prev i start depth b8 cap cands nc0 best0 ⦃ fun r => best0.val ≤ r.1.2.val ∧ r.1.2.val ≤ cap.val ⦄ := by
  rw [slot.b_walk]
  step*

@[local step] theorem skip_same_spec (prev) (start depth : Std.Usize) (same : Bool) :
    slot.b_skip_same prev start depth same ⦃ fun r => r.1.val ≤ start.val ⦄ := by
  have hwn := dp_WN_val
  rw [slot.b_skip_same]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac

@[local step] theorem insert_pos_spec (head3 : Array Std.U32 16384#usize) (head4 : Array Std.U32 65536#usize)
    (prev4) (head7 : Array Std.U32 65536#usize) (prev7) (q : Std.Usize) (b8 : Std.U64) (sh7 : Std.U32) (B : Nat)
    (h3 : LeAll head3.val B) (h4 : LeAll head4.val B) (h7 : LeAll head7.val B) (hq : q.val ≤ B) :
    slot.b_insert_pos head3 head4 prev4 head7 prev7 q b8 sh7 ⦃ fun r =>
      r.1.1.val ≤ B ∧ r.1.2.1.val ≤ B ∧ r.1.2.2.val ≤ B ∧
      LeAll r.2.1.val B ∧ LeAll r.2.2.1.val B ∧ LeAll r.2.2.2.2.1.val B ⦄ := by
  have hwn := dp_WN_val
  have H3 := h3
  have H4 := h4
  have H7 := h7
  rw [slot.b_insert_pos]
  step*
  have e3 := LeAll_get H3 h3.val (by scalar_tac)
  have e4 := LeAll_get H4 h4.val (by scalar_tac)
  have e7 := LeAll_get H7 h7.val (by scalar_tac)
  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, ?_, ?_⟩
  · exact dp_LeAll_set_of_eq head31_post H3 (by scalar_tac)
  · exact dp_LeAll_set_of_eq head41_post H4 (by scalar_tac)
  · exact dp_LeAll_set_of_eq head71_post H7 (by scalar_tac)

@[local step]
theorem insert_range_loop_spec (input : Slice Std.U8) (head3 : Array Std.U32 16384#usize)
    (head4 : Array Std.U32 65536#usize) (prev4) (head7 : Array Std.U32 65536#usize) (prev7)
    (e : Std.Usize) (sh7 : Std.U32) (q : Std.Usize) (B : Nat)
    (h3 : LeAll head3.val B) (h4 : LeAll head4.val B) (h7 : LeAll head7.val B)
    (he : e.val ≤ B + 1) (he8 : e.val + 8 ≤ Std.Usize.max) :
    slot.b_insert_range_loop input head3 head4 prev4 head7 prev7 e sh7 q ⦃ fun r =>
      LeAll r.1.val B ∧ LeAll r.2.1.val B ∧ LeAll r.2.2.2.1.val B ⦄ := by
  rw [slot.b_insert_range_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, q') => e.val - q'.val)
    (inv := fun (h3', h4', _, h7', _, _) => LeAll h3'.val B ∧ LeAll h4'.val B ∧ LeAll h7'.val B)
  · rintro ⟨h3', h4', p4', h7', p7', q'⟩ ⟨i3, i4, i7⟩
    simp only [slot.b_insert_range_loop.body]
    split
    · step*
      all_goals scalar_tac
    · step*
  · exact ⟨h3, h4, h7⟩

@[local step] theorem insert_range_spec (input : Slice Std.U8) (head3 : Array Std.U32 16384#usize)
    (head4 : Array Std.U32 65536#usize) (prev4) (head7 : Array Std.U32 65536#usize) (prev7)
    (f e : Std.Usize) (sh7 : Std.U32) (B : Nat)
    (h3 : LeAll head3.val B) (h4 : LeAll head4.val B) (h7 : LeAll head7.val B)
    (he : e.val ≤ B + 1) (he8 : e.val + 8 ≤ Std.Usize.max) :
    slot.b_insert_range input head3 head4 prev4 head7 prev7 f e sh7 ⦃ fun r =>
      LeAll r.1.val B ∧ LeAll r.2.1.val B ∧ LeAll r.2.2.2.1.val B ⦄ := by
  rw [slot.b_insert_range]
  exact insert_range_loop_spec input head3 head4 prev4 head7 prev7 e sh7 f B h3 h4 h7 he he8

theorem dp_nextl_lt {nextl : Array Std.U16 512#usize} (hnx : DpNextl nextl) (j : Nat)
    (hj : j < nextl.val.length) : j < (nextl.val[j]).val := by
  have hl : nextl.val.length = 512 := by simp
  have := hnx j (by omega)
  rwa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this

@[local step] theorem relax_one_spec (pa) (slt : Std.Usize) (cost choice : Std.U32) :
    slot.b_relax_one pa slt cost choice ⦃ fun _ => True ⦄ := by
  have := dp_RING_val
  rw [slot.b_relax_one]
  step*
  repeat' (split <;> step*)

@[local step]
theorem relax_run_loop_spec (pa lc) (nextl : Array Std.U16 512#usize) (i hi : Std.Usize) (base dpack : Std.U32)
    (l : Std.Usize) (hnx : DpNextl nextl) (hhi : hi.val ≤ 512) (hih : i.val + hi.val ≤ Std.Usize.max) :
    slot.b_relax_run_loop pa lc nextl i hi base dpack l ⦃ fun _ => True ⦄ := by
  have := dp_RING_val
  rw [slot.b_relax_run_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, l') => hi.val - l'.val)
    (inv := fun _ => True)
  · rintro ⟨pa', l'⟩ _
    simp only [slot.b_relax_run_loop.body]
    split
    · step*
      repeat' (split <;> step*)
      all_goals
        have hx := dp_nextl_lt hnx i1.val (by scalar_tac)
        scalar_tac
    · step*
  · trivial

@[local step] theorem relax_run_spec (pa lc) (nextl : Array Std.U16 512#usize) (i lo hi : Std.Usize)
    (base dpack : Std.U32) (hnx : DpNextl nextl) (hhi : hi.val < 512) (hih : i.val + hi.val ≤ Std.Usize.max) :
    slot.b_relax_run pa lc nextl i lo hi base dpack ⦃ fun _ => True ⦄ := by
  have := dp_RING_val
  rw [slot.b_relax_run]
  step*
  repeat' (split <;> step*)

@[local step]
theorem back_best_loop_spec (input : Slice Std.U8) (pa lc) (i s len dd t bt : Std.Usize) (bv : Std.U32)
    (hi : i.val < input.length) (hlen : len.val < 512) (hdd : dd.val < 8388608)
    (hN : input.length + 2147483648 ≤ Std.Usize.max)
    (ht : t.val ≤ i.val) (hbt : bt.val ≤ t.val) (ht258 : t.val = 0 ∨ len.val + t.val ≤ 258) :
    slot.b_back_best_loop input pa lc i s len dd t bt bv ⦃ fun r =>
      r.1.val ≤ i.val ∧ (r.1.val = 0 ∨ len.val + r.1.val ≤ 258) ⦄ := by
  have := dp_RING_val
  rw [slot.b_back_best_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (t', _, _) => slot.B_TMAX.val - t'.val)
    (inv := fun (t', bt', _) => t'.val ≤ i.val ∧ bt'.val ≤ t'.val ∧ (t'.val = 0 ∨ len.val + t'.val ≤ 258))
  · rintro ⟨t', bt', bv'⟩ ⟨h1, h2, h3⟩
    simp only [slot.b_back_best_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨ht, hbt, ht258⟩

@[local step] theorem back_best_spec (input : Slice Std.U8) (pa lc) (i s len dd : Std.Usize)
    (hi : i.val < input.length) (hlen : len.val < 512) (hdd : dd.val < 8388608)
    (hN : input.length + 2147483648 ≤ Std.Usize.max) :
    slot.b_back_best input pa lc i s len dd ⦃ fun r => r.1.val ≤ i.val ∧ (r.1.val = 0 ∨ len.val + r.1.val ≤ 258) ⦄ := by
  rw [slot.b_back_best]
  step*

@[local step] theorem dsym_spec (dtab) (d : Std.Usize) : slot.b_dsym dtab d ⦃ fun _ => True ⦄ := by
  rw [slot.b_dsym]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac

@[local step]
theorem relax_cands_loop_spec (input : Slice Std.U8) (pa cands nc lc) (nextl : Array Std.U16 512#usize)
    (dtab dcc) (i s : Std.Usize) (base : Std.U32) (pcd lo k : Std.Usize)
    (hnx : DpNextl nextl) (hi : i.val < input.length) (hN : input.length + 2147483648 ≤ Std.Usize.max) :
    slot.b_relax_cands_loop input pa cands nc lc nextl dtab dcc i s base pcd lo k ⦃ fun _ => True ⦄ := by
  have := dp_RING_val
  have := dp_BEXT_TOP_bound
  rw [slot.b_relax_cands_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, k') => 16 - k'.val)
    (inv := fun _ => True)
  · rintro ⟨pa', lo', k'⟩ _
    simp only [slot.b_relax_cands_loop.body]
    step*
    have := dp_shr9 c

    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    · intro pa2 _
      step*
  · trivial

@[local step] theorem relax_cands_spec (input : Slice Std.U8) (pa cands nc lc) (nextl : Array Std.U16 512#usize)
    (dtab dcc) (i s : Std.Usize) (base : Std.U32) (pcd : Std.Usize)
    (hnx : DpNextl nextl) (hi : i.val < input.length) (hN : input.length + 2147483648 ≤ Std.Usize.max) :
    slot.b_relax_cands input pa cands nc lc nextl dtab dcc i s base pcd ⦃ fun _ => True ⦄ := by
  rw [slot.b_relax_cands]
  step*

@[local step]
theorem drop_farther_loop_spec (cands) (cd nc : Std.Usize) :
    slot.b_drop_farther_loop cands cd nc ⦃ fun _ => True ⦄ := by
  rw [slot.b_drop_farther_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun nc' => nc'.val)
    (inv := fun _ => True)
  · rintro nc' _
    simp only [slot.b_drop_farther_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step] theorem drop_farther_spec (cands) (nc0 cd : Std.Usize) : slot.b_drop_farther cands nc0 cd ⦃ fun _ => True ⦄ := by
  rw [slot.b_drop_farther]
  step*

@[local step] theorem next_anchor_spec (anchor i cl best : Std.Usize) : slot.b_next_anchor anchor i cl best ⦃ fun _ => True ⦄ := by
  rw [slot.b_next_anchor]
  repeat' (split <;> step*)

@[local step]
theorem ext_back_loop_spec (input : Slice Std.U8) (i d s max t : Std.Usize)
    (hi : i.val < input.length) (hd : d.val < 8388608) (hN : input.length + 2147483648 ≤ Std.Usize.max)
    (hsi : s.val ≤ i.val) (ht : t.val ≤ i.val - s.val) :
    slot.b_ext_back_loop input i d s max t ⦃ fun r => r.val ≤ i.val - s.val ⦄ := by
  rw [slot.b_ext_back_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun t' => max.val - t'.val)
    (inv := fun t' => t'.val ≤ i.val - s.val)
  · rintro t' h1
    simp only [slot.b_ext_back_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ht

@[local step] theorem ext_back_spec (input : Slice Std.U8) (i d s max : Std.Usize)
    (hi : i.val < input.length) (hd : d.val < 8388608) (hN : input.length + 2147483648 ≤ Std.Usize.max)
    (hsi : s.val ≤ i.val) :
    slot.b_ext_back input i d s max ⦃ fun r => r.val ≤ i.val - s.val ⦄ := by
  rw [slot.b_ext_back]
  step*

@[local step]
theorem open_chunk_loop_spec (pa) (s u : Std.Usize) (hs : s.val + 259 ≤ Std.Usize.max) :
    slot.b_open_chunk_loop pa s u ⦃ fun _ => True ⦄ := by
  have := dp_RING_val
  rw [slot.b_open_chunk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, u') => 259 - u'.val)
    (inv := fun _ => True)
  · rintro ⟨pa', u'⟩ _
    simp only [slot.b_open_chunk_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step] theorem open_chunk_spec (pa) (s : Std.Usize) (hs : s.val + 259 ≤ Std.Usize.max) :
    slot.b_open_chunk pa s ⦃ fun _ => True ⦄ := by
  have := dp_RING_val
  rw [slot.b_open_chunk]
  step*

@[local step]
theorem push_rev_loop_spec (plan tb lim k) : slot.b_push_rev_loop plan tb lim k ⦃ fun _ => True ⦄ := by
  have := dp_RING_val
  rw [slot.b_push_rev_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => k'.val)
    (inv := fun _ => True)
  · rintro ⟨plan', k'⟩ _
    simp only [slot.b_push_rev_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step] theorem push_rev_spec (plan tb nt lim) : slot.b_push_rev plan tb nt lim ⦃ fun _ => True ⦄ := by
  rw [slot.b_push_rev]
  step*

@[local step]
theorem backtrack_loop_spec (input : Slice Std.U8) (pa) (s : Std.Usize) (lsym dtab lf df tb) (j nt guard : Std.Usize)
    (hs : s.val ≤ j.val) (hg : nt.val + guard.val ≤ Std.Usize.max) :
    slot.b_backtrack_loop input pa s lsym dtab lf df tb j nt guard ⦃ fun _ => True ⦄ := by
  have := dp_RING_val
  rw [slot.b_backtrack_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, g') => g'.val)
    (inv := fun (_, _, _, j', nt', g') => s.val ≤ j'.val ∧ nt'.val + g'.val ≤ Std.Usize.max)
  · rintro ⟨lf', df', tb', j', nt', g'⟩ ⟨h1, h2⟩
    simp only [slot.b_backtrack_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hs, hg⟩

@[local step] theorem backtrack_spec (input : Slice Std.U8) (pa plan) (s e : Std.Usize) (lsym dtab lf df tb)
    (hse : s.val ≤ e.val) (he : e.val < Std.Usize.max) :
    slot.b_backtrack input pa plan s e lsym dtab lf df tb ⦃ fun _ => True ⦄ := by
  rw [slot.b_backtrack]
  step*

@[local step]
theorem halve_loop0_spec (lf s) : slot.b_halve_loop0 lf s ⦃ fun _ => True ⦄ := by
  rw [slot.b_halve_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, s') => 286 - s'.val)
    (inv := fun _ => True)
  · rintro ⟨lf', s'⟩ _
    simp only [slot.b_halve_loop0.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step]
theorem halve_loop1_spec (df k) : slot.b_halve_loop1 df k ⦃ fun _ => True ⦄ := by
  rw [slot.b_halve_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => 30 - k'.val)
    (inv := fun _ => True)
  · rintro ⟨df', k'⟩ _
    simp only [slot.b_halve_loop1.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step] theorem halve_spec (lf df) : slot.b_halve lf df ⦃ fun _ => True ⦄ := by
  rw [slot.b_halve]
  step*

@[local step] theorem log2_16_spec (x : Std.U32) : slot.b_log2_16 x ⦃ fun _ => True ⦄ := by
  rw [slot.b_log2_16]
  split
  · step*
  · step*
    all_goals try (have := lz32_bound x)
    repeat' (split <;> step*)
    all_goals try (have := LeAll_get dp_FRAC_le i3.val (by scalar_tac))
    all_goals scalar_tac

@[local step]
theorem costs_from_loop0_spec (freq total s) : slot.b_costs_from_loop0 freq total s ⦃ fun _ => True ⦄ := by
  rw [slot.b_costs_from_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, s') => freq.length - s'.val)
    (inv := fun _ => True)
  · rintro ⟨total', s'⟩ _
    simp only [slot.b_costs_from_loop0.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step]
theorem costs_from_loop1_spec (freq out lt t) : slot.b_costs_from_loop1 freq out lt t ⦃ fun _ => True ⦄ := by
  rw [slot.b_costs_from_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, t') => freq.length - t'.val)
    (inv := fun _ => True)
  · rintro ⟨out', t'⟩ _
    simp only [slot.b_costs_from_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step] theorem costs_from_spec (freq out) : slot.b_costs_from freq out ⦃ fun _ => True ⦄ := by
  rw [slot.b_costs_from]
  step*

@[local step]
theorem huff_slot_loop_spec (freq : Slice Std.U32) (sym) (f : Std.U32) (j : Std.Usize) (hf : 0 < freq.length) :
    slot.b_huff_slot_loop freq sym f j ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_slot_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, j') => j'.val)
    (inv := fun _ => True)
  · rintro ⟨sym', j'⟩ _
    simp only [slot.b_huff_slot_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step] theorem huff_slot_spec (freq : Slice Std.U32) (sym) (ns : Std.Usize) (f : Std.U32) (hf : 0 < freq.length) :
    slot.b_huff_slot freq sym ns f ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_slot]
  step*

@[local step]
theorem huff_sort_loop_spec (freq : Slice Std.U32) (m sym) (ns i : Std.Usize)
    (hf : 0 < freq.length) (hns : ns.val ≤ i.val) (hi : i.val ≤ 320) :
    slot.b_huff_sort_loop freq m sym ns i ⦃ fun r => r.1.val ≤ 320 ⦄ := by
  rw [slot.b_huff_sort_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, i') => 320 - i'.val)
    (inv := fun (_, ns', i') => ns'.val ≤ i'.val ∧ i'.val ≤ 320)
  · rintro ⟨sym', ns', i'⟩ ⟨h1, h2⟩
    simp only [slot.b_huff_sort_loop.body]
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Array Std.Usize 320#usize × Std.Usize) => x.2.val ≤ ns'.val + 1)
    · split
      · step*
      · step*
    · intro x hx
      rcases x with ⟨sym1, ns1⟩
      step*
      all_goals scalar_tac
  · exact ⟨hns, hi⟩

@[local step] theorem huff_sort_spec (freq : Slice Std.U32) (m sym) (hf : 0 < freq.length) :
    slot.b_huff_sort freq m sym ⦃ fun r => r.1.val ≤ 320 ⦄ := by
  rw [slot.b_huff_sort]
  step*

@[local step] theorem huff_take_spec (w) (a b ns nx : Std.Usize) (hab : a.val + b.val < Std.Usize.max) :
    slot.b_huff_take w a b ns nx ⦃ fun r => r.2.1.val + r.2.2.val = a.val + b.val + 1 ⦄ := by
  rw [slot.b_huff_take]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac

@[local step]
theorem huff_build_loop_spec (w par) (ns a b nx : Std.Usize) (hns : ns.val ≤ 320) (hnx : nx.val ≤ 639)
    (hab : a.val + b.val + ns.val = 2 * nx.val) :
    slot.b_huff_build_loop w par ns a b nx ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_build_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, nx') => 639 - nx'.val)
    (inv := fun (_, _, a', b', nx') => nx'.val ≤ 639 ∧ a'.val + b'.val + ns.val = 2 * nx'.val)
  · rintro ⟨w', par', a', b', nx'⟩ ⟨h1, h2⟩
    simp only [slot.b_huff_build_loop.body]
    step*
    rcases y with ⟨i7, a1, b1⟩
    step*
    all_goals scalar_tac
  · exact ⟨hnx, hab⟩

@[local step] theorem huff_build_spec (w par) (ns : Std.Usize) (hns : ns.val ≤ 320) :
    slot.b_huff_build w par ns ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_build]
  step*

@[local step]
theorem huff_depths_loop_spec (par depth ns mx q) : slot.b_huff_depths_loop par depth ns mx q ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_depths_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, q') => q'.val)
    (inv := fun _ => True)
  · rintro ⟨depth', mx', q'⟩ _
    simp only [slot.b_huff_depths_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step] theorem huff_depths_spec (par depth nx ns) : slot.b_huff_depths par depth nx ns ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_depths]
  step*
  repeat' (split <;> step*)

@[local step]
theorem huff_costs_loop0_spec (freq : Slice Std.U32) (sym ns w k) (hf : 0 < freq.length) :
    slot.b_huff_costs_loop0 freq sym ns w k ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_costs_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => ns.val - k'.val)
    (inv := fun _ => True)
  · rintro ⟨w', k'⟩ _
    simp only [slot.b_huff_costs_loop0.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step]
theorem huff_costs_loop1_spec (m out) (mx : Std.U32) (t : Std.Usize) (hmx : mx.val ≤ 15) :
    slot.b_huff_costs_loop1 m out mx t ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_costs_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, t') => m.val - t'.val)
    (inv := fun _ => True)
  · rintro ⟨out', t'⟩ _
    simp only [slot.b_huff_costs_loop1.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step]
theorem huff_costs_loop2_spec (out sym ns depth r) : slot.b_huff_costs_loop2 out sym ns depth r ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_costs_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, r') => ns.val - r'.val)
    (inv := fun _ => True)
  · rintro ⟨out', r'⟩ _
    simp only [slot.b_huff_costs_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step] theorem huff_costs_spec (freq : Slice Std.U32) (m out) (hf : 0 < freq.length) :
    slot.b_huff_costs freq m out ⦃ fun _ => True ⦄ := by
  rw [slot.b_huff_costs]
  step*
  apply WP.spec_bind (Pₘ := fun _ => True)
  · split
    · step*
    · step*
  · intro x _
    rcases x with ⟨depth1, mx⟩
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac

@[local step]
theorem make_costs_loop0_spec (litc llc b) : slot.b_make_costs_loop0 litc llc b ⦃ fun _ => True ⦄ := by
  rw [slot.b_make_costs_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, b') => 256 - b'.val)
    (inv := fun _ => True)
  · rintro ⟨litc', b'⟩ _
    simp only [slot.b_make_costs_loop0.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step]
theorem make_costs_loop1_spec (lsym : Array Std.U8 512#usize) (lc) (llc : Array Std.U32 286#usize) (l : Std.Usize)
    (hls : LeAll lsym.val 28) : slot.b_make_costs_loop1 lsym lc llc l ⦃ fun _ => True ⦄ := by
  rw [slot.b_make_costs_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, l') => 259 - l'.val)
    (inv := fun _ => True)
  · rintro ⟨lc', l'⟩ _
    simp only [slot.b_make_costs_loop1.body]
    step*
    all_goals try (have := LeAll_get hls l'.val (by scalar_tac))
    all_goals scalar_tac
  · trivial

@[local step]
theorem make_costs_loop2_spec (dcc dc k) : slot.b_make_costs_loop2 dcc dc k ⦃ fun _ => True ⦄ := by
  rw [slot.b_make_costs_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => 30 - k'.val)
    (inv := fun _ => True)
  · rintro ⟨dcc', k'⟩ _
    simp only [slot.b_make_costs_loop2.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step] theorem make_costs_spec (lf df) (lsym : Array Std.U8 512#usize) (litc lc dcc huff)
    (hls : LeAll lsym.val 28) : slot.b_make_costs lf df lsym litc lc dcc huff ⦃ fun _ => True ⦄ := by
  rw [slot.b_make_costs]
  step*
  apply WP.spec_bind (Pₘ := fun _ => True)
  · split
    · step*
    · step*
  · intro x _
    rcases x with ⟨llc1, dc1⟩
    step*

@[local step]
theorem update_costs_loop_spec (lf tot z) : slot.b_update_costs_loop lf tot z ⦃ fun _ => True ⦄ := by
  rw [slot.b_update_costs_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, z') => 286 - z'.val)
    (inv := fun _ => True)
  · rintro ⟨tot', z'⟩ _
    simp only [slot.b_update_costs_loop.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step] theorem update_costs_spec (lf df) (lsym : Array Std.U8 512#usize) (litc lc dcc huff)
    (hls : LeAll lsym.val 28) : slot.b_update_costs lf df lsym litc lc dcc huff ⦃ fun _ => True ⦄ := by
  rw [slot.b_update_costs]
  step*
  repeat' (split <;> step*)

@[local step]
theorem init_counts_loop0_spec (input : Slice Std.U8) (lf) (n step i : Std.Usize)
    (hn : n.val = input.length) (hstep : 1 ≤ step.val) (hns : n.val + step.val ≤ Std.Usize.max) :
    slot.b_init_counts_loop0 input lf n step i ⦃ fun _ => True ⦄ := by
  rw [slot.b_init_counts_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i') => n.val - i'.val)
    (inv := fun _ => True)
  · rintro ⟨lf', i'⟩ _
    simp only [slot.b_init_counts_loop0.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step]
theorem init_counts_loop1_spec (lf s) : slot.b_init_counts_loop1 lf s ⦃ fun _ => True ⦄ := by
  rw [slot.b_init_counts_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, s') => 286 - s'.val)
    (inv := fun _ => True)
  · rintro ⟨lf', s'⟩ _
    simp only [slot.b_init_counts_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step]
theorem init_counts_loop2_spec (df k) : slot.b_init_counts_loop2 df k ⦃ fun _ => True ⦄ := by
  rw [slot.b_init_counts_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => 30 - k'.val)
    (inv := fun _ => True)
  · rintro ⟨df', k'⟩ _
    simp only [slot.b_init_counts_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step] theorem init_counts_spec (input : Slice Std.U8) (lf df)
    (hN : input.length + input.length ≤ Std.Usize.max) :
    slot.b_init_counts input lf df ⦃ fun _ => True ⦄ := by
  rw [slot.b_init_counts]
  step*
  all_goals
    have h1 := dp_or_one_le (input.length / 8192)
    have h2 : 1 ≤ input.length / 8192 ||| 1 := Nat.right_le_or
    scalar_tac

@[local step]
theorem fill_tables_loop0_spec (lsym : Array Std.U8 512#usize) (code l : Std.Usize)
    (hc : code.val ≤ 28) (hls : LeAll lsym.val 28) :
    slot.b_fill_tables_loop0 lsym code l ⦃ fun r => LeAll r.val 28 ⦄ := by
  rw [slot.b_fill_tables_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, l') => 259 - l'.val)
    (inv := fun (ls', c', _) => c'.val ≤ 28 ∧ LeAll ls'.val 28)
  · rintro ⟨ls', c', l'⟩ ⟨h1, h2⟩
    simp only [slot.b_fill_tables_loop0.body]
    split
    · apply WP.spec_bind (Pₘ := fun (x : Std.Usize) => x.val ≤ 28)
      · repeat' (split <;> step*)
        all_goals scalar_tac
      · intro code1 hc1
        step*
        and_intros
        all_goals first
          | exact dp_LeAll_set_of_eq a_post h2 (by scalar_tac)
          | scalar_tac
    · step*
  · exact ⟨hc, hls⟩

@[local step]
theorem fill_tables_loop1_spec (dtab c j) : slot.b_fill_tables_loop1 dtab c j ⦃ fun _ => True ⦄ := by
  rw [slot.b_fill_tables_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, j') => 256 - j'.val)
    (inv := fun _ => True)
  · rintro ⟨dtab', c', j'⟩ _
    simp only [slot.b_fill_tables_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step]
theorem fill_tables_loop2_loop0_spec (c2 d) : slot.b_fill_tables_loop2_loop0 c2 d ⦃ fun _ => True ⦄ := by
  rw [slot.b_fill_tables_loop2_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun c2' => 29 - c2'.val)
    (inv := fun _ => True)
  · rintro c2' _
    simp only [slot.b_fill_tables_loop2_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

@[local step]
theorem fill_tables_loop2_spec (dtab c2 k) : slot.b_fill_tables_loop2 dtab c2 k ⦃ fun _ => True ⦄ := by
  rw [slot.b_fill_tables_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, k') => 256 - k'.val)
    (inv := fun _ => True)
  · rintro ⟨dtab', c2', k'⟩ _
    simp only [slot.b_fill_tables_loop2.body]
    step*
    all_goals scalar_tac
  · trivial

@[local step] theorem fill_tables_spec (lsym : Array Std.U8 512#usize) (dtab) (hls : LeAll lsym.val 28) :
    slot.b_fill_tables lsym dtab ⦃ fun r => LeAll r.1.val 28 ⦄ := by
  rw [slot.b_fill_tables]
  step*

@[local step]
theorem fill_nextl_loop0_loop0_spec (lsym) (l e : Std.Usize) (hl : l.val < 257) (he : e.val ≤ 258) :
    slot.b_fill_nextl_loop0_loop0 lsym l e ⦃ fun r => e.val ≤ r.val ∧ r.val ≤ 258 ⦄ := by
  rw [slot.b_fill_nextl_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun e' => 258 - e'.val)
    (inv := fun e' => e.val ≤ e'.val ∧ e'.val ≤ 258)
  · rintro e' ⟨h1, h2⟩
    simp only [slot.b_fill_nextl_loop0_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨le_refl _, he⟩

@[local step]
theorem fill_nextl_loop0_spec (lsym) (nextl : Array Std.U16 512#usize) (l : Std.Usize)
    (hl : l.val ≤ 512) (hnx : ∀ j, j < l.val → j < (nextl.val[j]!).val) :
    slot.b_fill_nextl_loop0 lsym nextl l ⦃ fun r => DpNextl r ⦄ := by
  rw [slot.b_fill_nextl_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, l') => 512 - l'.val)
    (inv := fun (nx', l') => l'.val ≤ 512 ∧ ∀ j, j < l'.val → j < (nx'.val[j]!).val)
  · rintro ⟨nx', l'⟩ ⟨h1, h2⟩
    simp only [slot.b_fill_nextl_loop0.body]
    split
    · step*
      repeat' (split <;> step*)
      all_goals
        and_intros
        all_goals first
          | scalar_tac
          | (intro j hj
             rw [a_post, Array.set_val_eq, dp_getElem!_set _ _ _ _ (by scalar_tac)]
             split
             · scalar_tac
             · exact h2 j (by scalar_tac))
    · step*
      intro j hj
      exact h2 j (by scalar_tac)
  · exact ⟨hl, hnx⟩

@[local step] theorem fill_nextl_spec (lsym) (nextl : Array Std.U16 512#usize) :
    slot.b_fill_nextl lsym nextl ⦃ fun r => DpNextl r ⦄ := by
  rw [slot.b_fill_nextl]
  apply fill_nextl_loop0_spec
  · scalar_tac
  · intro j hj; simp at hj

theorem dp_sat_sub_val (x y : Std.Usize) :
    (core.num.Usize.saturating_sub x y).val = x.val - y.val := by
  have hx := x.hBounds
  show (BitVec.ofNat _ (max 0 (x.val - y.val))).toNat = x.val - y.val
  rw [BitVec.toNat_ofNat, Nat.zero_max]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hx)

theorem dp_ite3_spec {α : Type} {a b c : Prop} [Decidable a] [Decidable b] [Decidable c]
    {X Y : Result α} {P : α → Prop} (hX : a → b → ¬c → X ⦃ P ⦄) (hY : Y ⦃ P ⦄) :
    (if a then (if b then (if c then Y else X) else Y) else Y) ⦃ P ⦄ := by
  by_cases ha : a
  · rw [if_pos ha]
    by_cases hb : b
    · rw [if_pos hb]
      by_cases hc : c
      · rw [if_pos hc]; exact hY
      · rw [if_neg hc]; exact hX ha hb hc
    · rw [if_neg hb]; exact hY
  · rw [if_neg ha]; exact hY

theorem dp_ite_spec {α : Type} {c : Prop} [Decidable c] {A B : Result α} {P : α → Prop}
    (hA : c → A ⦃ P ⦄) (hB : ¬c → B ⦃ P ⦄) : (if c then A else B) ⦃ P ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h

theorem dp_ite2_spec {α : Type} {a b : Prop} [Decidable a] [Decidable b]
    {X Y : Result α} {P : α → Prop} (hX : a → b → X ⦃ P ⦄) (hY : Y ⦃ P ⦄) :
    (if a then (if b then X else Y) else Y) ⦃ P ⦄ := by
  by_cases ha : a
  · rw [if_pos ha]
    by_cases hb : b
    · rw [if_pos hb]; exact hX ha hb
    · rw [if_neg hb]; exact hY
  · rw [if_neg ha]; exact hY

set_option maxHeartbeats 10000000 in
theorem dp_parse_loop_spec (input : Slice Std.U8) (plan) (ct lazyn d4 d7 skip h3d huff n : Std.Usize)
    (head3 : Array Std.U32 16384#usize) (head4 : Array Std.U32 65536#usize) (prev4)
    (head7 : Array Std.U32 65536#usize) (prev7 pa tb) (lsym : Array Std.U8 512#usize) (dtab)
    (nextl : Array Std.U16 512#usize) (lf df litc lc dcc) (lim : Std.Usize) (sh7 : Std.U32)
    (s next_upd : Std.Usize) (cands) (cl cd : Std.Usize) (cdc : Std.U32) (i anchor alen : Std.Usize)
    (hn : n.val = input.length) (hlim : lim.val + 8 = n.val)
    (hN : input.length + input.length ≤ Std.Usize.max)
    (hls : LeAll lsym.val 28) (hnx : DpNextl nextl)
    (hsi : s.val ≤ i.val) (hin : i.val ≤ n.val) (hcl : cl.val < 512)
    (h3 : LeAll head3.val i.val) (h4 : LeAll head4.val i.val) (h7 : LeAll head7.val i.val) :
    slot.b_dp_parse_loop input plan ct lazyn d4 d7 skip h3d huff n head3 head4 prev4 head7 prev7 pa tb
      lsym dtab nextl lf df litc lc dcc lim sh7 s next_upd cands cl cd cdc i anchor alen ⦃ fun _ => True ⦄ := by
  have hR := dp_RING_val
  have hU := dp_UPD_bound
  have hS := dp_size hN
  rw [slot.b_dp_parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, i', _, _) => lim.val - i'.val)
    (inv := fun (_, h3', h4', _, h7', _, _, _, _, _, _, _, _, s', _, _, cl', _, _, i', _, _) =>
       s'.val ≤ i'.val ∧ i'.val ≤ n.val ∧ cl'.val < 512 ∧ LeAll h3'.val i'.val ∧ LeAll h4'.val i'.val ∧
       LeAll h7'.val i'.val)
  · rintro ⟨plan', h3', h4', p4', h7', p7', pa', tb', lf', df', litc', lc', dcc', s', nu', cands', cl', cd', cdc',
      i', anc', alen'⟩ ⟨hs', hi', hcl', hh3, hh4, hh7⟩
    clear hsi hin hcl h3 h4 h7
    clear plan head3 head4 prev4 head7 prev7 pa tb lf df litc lc dcc s next_upd cands cl cd cdc i anchor alen
    simp only [slot.b_dp_parse_loop.body]
    apply dp_ite_spec
    · intro hlt
      apply WP.spec_bind (Pₘ := fun _ => True)
      · split <;> step*
        all_goals scalar_tac
      intro pa1 _
      step
      step with insert_pos_spec (B := i'.val) as ⟨hc, head31, head41, prev41, head71, prev71, hq1, hq2, hq3, hL3, hL4, hL7⟩
      step*
      apply WP.spec_bind (Pₘ := fun _ => True)
      · split <;> simp only [WP.spec_ok]
      intro lzn _
      step*
      apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Array Std.U32 16384#usize × Array Std.U32 65536#usize ×
          Array Std.U32 32768#usize × Array Std.U32 65536#usize × Array Std.U32 32768#usize × Array Std.U64 8192#usize ×
          Array Std.U32 8192#usize × Array Std.U32 320#usize × Array Std.U32 32#usize × Std.Usize × Array Std.U32 16#usize ×
          Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize × Std.Usize) =>
        match x with
        | (_, g3, g4, _, g7, _, _, _, _, _, s1, _, cl1, _, _, i12, _, _) =>
          s1.val ≤ i12.val ∧ i'.val < i12.val ∧ i12.val ≤ n.val ∧ cl1.val < 512 ∧
          LeAll g3.val i12.val ∧ LeAll g4.val i12.val ∧ LeAll g7.val i12.val)
      · apply dp_ite3_spec
        ·
          intro hct hc3 hlz
          clear * - hS hc3 hcl' hs' hi' hlt hlim hn hL3 hL4 hL7 i4_post
          step*
          exact ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, LeAll_mono hL3 (by scalar_tac),
            LeAll_mono hL4 (by scalar_tac), LeAll_mono hL7 (by scalar_tac)⟩
        ·
          clear * - hn hlim hS hnx hs' hi' hlt hq1 hq2 hq3 hL3 hL4 hL7 i4_post
          step*
          apply WP.spec_bind (Pₘ := fun (x : Std.Usize) => 9 ≤ x.val ∧ i'.val + x.val ≤ n.val)
          · split <;> simp only [WP.spec_ok] <;> scalar_tac
          rintro cap1 ⟨hcap1, hcap2⟩
          rcases hc with ⟨c3, c4, c7⟩
          step*
          apply WP.spec_bind (Pₘ := fun (x : Array Std.U32 16#usize × Std.Usize × Std.Usize × Bool) =>
            2 ≤ x.2.2.1.val ∧ x.2.2.1.val ≤ cap1.val)
          · split
            · step*
              apply WP.spec_bind (Pₘ := fun (x : Array Std.U32 16#usize × Std.Usize × Std.Usize) =>
                2 ≤ x.2.2.val ∧ x.2.2.val ≤ cap1.val)
              · split <;> step*
                all_goals scalar_tac
              rintro ⟨a, i17, i18⟩ ⟨hb1, hb2⟩
              step*
            · simp only [WP.spec_ok]; scalar_tac
          rintro ⟨cands2, nc, best, p3⟩ ⟨hb1, hb2⟩
          clear * - hn hlim hS hnx hs' hi' hlt hq2 hq3 hL3 hL4 hL7 i4_post hcap1 hcap2 hb1 hb2
          apply WP.spec_bind (Pₘ := fun _ => True)
          · split <;> simp only [WP.spec_ok]
          intro b _
          step*
          apply WP.spec_bind (Pₘ := fun _ => True)
          · split
            · simp only [WP.spec_ok]
            · split <;> simp only [WP.spec_ok, bind_tc_ok]
          rintro ⟨cands4, dep7⟩ _
          apply WP.spec_bind (Pₘ := fun _ => True)
          · repeat' split
            all_goals simp only [WP.spec_ok]
          intro b1 _
          step*
          apply WP.spec_bind (Pₘ := fun (x : Array Std.U32 16#usize × Std.Usize × Std.Usize) =>
            2 ≤ x.2.2.val ∧ x.2.2.val ≤ cap1.val)
          · apply dp_ite2_spec
            · intro hgt hle
              step*
              apply WP.spec_bind (Pₘ := fun _ => True)
              · split <;> step*
              intro i26 _
              step*
              all_goals scalar_tac
            · simp only [WP.spec_ok]; scalar_tac
          rintro ⟨cands6, nc3, best3⟩ ⟨hb3, hb4⟩
          clear * - hn hlim hS hnx hs' hi' hlt hL3 hL4 hL7 i4_post hcap1 hcap2 hb3 hb4
          apply WP.spec_bind (Pₘ := fun _ => True)
          · split <;> simp only [WP.spec_ok]
          intro pcd _
          step*
          apply WP.spec_bind (Pₘ := fun (x : Std.Usize × Std.Usize × Std.U32) => x.1.val < 512)
          · split
            · step*
              all_goals
                have := dp_sat_sub_val i24 1#usize
                scalar_tac
            · simp only [WP.spec_ok]; scalar_tac
          rintro ⟨cl2, cd2, cdc2⟩ hcl2
          clear * - hn hlim hS hnx hs' hi' hlt hL3 hL4 hL7 i4_post hcap1 hcap2 hb3 hb4 hcl2
          apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Array Std.U32 16384#usize ×
              Array Std.U32 65536#usize × Array Std.U32 32768#usize × Array Std.U32 65536#usize ×
              Array Std.U32 32768#usize × Array Std.U64 8192#usize × Array Std.U32 8192#usize ×
              Array Std.U32 320#usize × Array Std.U32 32#usize × Std.Usize × Std.Usize × Std.Usize) =>
            match x with
            | (_, g3, g4, _, g7, _, _, _, _, _, s1, cl1, i12) =>
              s1.val ≤ i12.val ∧ i'.val < i12.val ∧ i12.val ≤ n.val ∧ cl1.val < 512 ∧
              LeAll g3.val i12.val ∧ LeAll g4.val i12.val ∧ LeAll g7.val i12.val)
          · apply dp_ite2_spec
            ·
              intro hsk hnc
              have := dp_shr9
              step*
              apply WP.spec_bind (Pₘ := fun _ => True)
              · split <;> step*
                all_goals scalar_tac
              intro plan3 _
              step*
              apply WP.spec_bind (Pₘ := fun (x : Std.Usize) => x.val ≤ «end».val ∧ x.val ≤ lim.val)
              · split <;> simp only [WP.spec_ok] <;> scalar_tac
              rintro end1 ⟨he1, he2⟩
              have hE3 := LeAll_mono hL3 (show i'.val ≤ «end».val by scalar_tac)
              have hE4 := LeAll_mono hL4 (show i'.val ≤ «end».val by scalar_tac)
              have hE7 := LeAll_mono hL7 (show i'.val ≤ «end».val by scalar_tac)
              step with insert_range_spec (B := «end».val) as ⟨head33, head43, prev43, head73, prev73, hr3, hr4, hr7⟩
              step*
              exact ⟨le_refl _, by scalar_tac, by scalar_tac, by scalar_tac, hr3, hr4, hr7⟩
            ·
              step*
              exact ⟨by scalar_tac, by scalar_tac, by scalar_tac, by simpa using hcl2,
                LeAll_mono hL3 (by scalar_tac), LeAll_mono hL4 (by scalar_tac), LeAll_mono hL7 (by scalar_tac)⟩
          rintro ⟨v, a, a1, a2, a3, a4, a5, a6, a7, a8, i21, i22, i23⟩ ⟨hv1, hv2, hv3, hv4, hv5, hv6, hv7⟩
          step*
      rintro ⟨plan1, head32, head42, prev42, head72, prev72, pa3, tb1, lf1, df1, s1, cands1, cl1, cd1, cdc1, i12,
        anchor1, alen1⟩ ⟨hs1, hii, hin1, hcl1, hk3, hk4, hk7⟩
      clear * - hs1 hii hin1 hcl1 hk3 hk4 hk7 hlt hn hlim hS hls hU hR
      step*
      apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Array Std.U64 8192#usize × Array Std.U32 8192#usize ×
          Array Std.U32 320#usize × Array Std.U32 32#usize × Std.Usize) => x.2.2.2.2.2.val ≤ i12.val)
      · split <;> step*
        all_goals scalar_tac
      rintro ⟨plan2, pa4, tb2, lf2, df2, s2⟩ hs2
      split <;> step*
      all_goals
        simp only at hs2
        exact ⟨hs2, hin1, hcl1, hk3, hk4, hk7, by scalar_tac⟩
    · intro _
      step*
  · exact ⟨hsi, hin, hcl, h3, h4, h7⟩

attribute [local step] dp_parse_loop_spec

@[local step] theorem dp_parse_spec (input : Slice Std.U8) (plan) (ct lazyn d4 d7 skip h3d huff : Std.Usize)
    (h16 : 16 ≤ input.length) (hN : input.length + input.length ≤ Std.Usize.max) :
    slot.b_dp_parse input plan ct lazyn d4 d7 skip h3d huff ⦃ fun _ => True ⦄ := by
  have hS := dp_size hN
  have hk := dp_KB7_bound
  have hU := dp_UPD_bound
  have z8 : LeAll (Array.repeat 512#usize 0#u8).val 28 := dp_LeAll_repeat _ _ _ (by simp)
  have z3 : LeAll (Array.repeat 16384#usize 0#u32).val (0#usize).val := dp_LeAll_repeat _ _ _ (by simp)
  have z4 : LeAll (Array.repeat 65536#usize 0#u32).val (0#usize).val := dp_LeAll_repeat _ _ _ (by simp)
  rw [slot.b_dp_parse]
  step*
  split <;> step*
  all_goals scalar_tac

@[local step] theorem make_plan_spec (input : Slice Std.U8) (r : Std.Usize) :
    slot.b_make_plan input r ⦃ fun _ => True ⦄ := by
  rw [slot.b_make_plan]
  step*
  all_goals
    have hw := dp_wadd_self input.len (by rw [← i2_post]; scalar_tac)
    simpa using hw

theorem a_ite_spec {α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop) (ha : P a) (hb : P b) :
    (if c then (ok a : Result α) else ok b) ⦃ P ⦄ := by
  split <;> simpa [Std.WP.spec_ok]

theorem a_ite_dspec {α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop) (ha : c → P a)
    (hb : ¬c → P b) : (if c then (ok a : Result α) else ok b) ⦃ P ⦄ := by
  split
  · simpa [Std.WP.spec_ok] using ha (by assumption)
  · simpa [Std.WP.spec_ok] using hb (by assumption)

@[irreducible] def a_word8 (input : Slice Std.U8) (p : Nat) : Nat :=
  (input.val[p]!).val * 2^56 + (input.val[p + 1]!).val * 2^48 + (input.val[p + 2]!).val * 2^40
    + (input.val[p + 3]!).val * 2^32 + (input.val[p + 4]!).val * 2^24
    + (input.val[p + 5]!).val * 2^16 + (input.val[p + 6]!).val * 2^8 + (input.val[p + 7]!).val

theorem a_u8_lt (x : Std.U8) : x.val < 256 := by scalar_tac

theorem a_word8_digit (input : Slice Std.U8) (p k : Nat) (hk : k < 8) :
    (input.val[p + k]!).val = a_word8 input p / 256 ^ (7 - k) % 256 := by
  have := a_u8_lt (input.val[p]!); have := a_u8_lt (input.val[p+1]!)
  have := a_u8_lt (input.val[p+2]!); have := a_u8_lt (input.val[p+3]!)
  have := a_u8_lt (input.val[p+4]!); have := a_u8_lt (input.val[p+5]!)
  have := a_u8_lt (input.val[p+6]!); have := a_u8_lt (input.val[p+7]!)
  simp only [a_word8]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.add_zero, Nat.pow_zero, Nat.pow_succ, Nat.one_mul,
    Nat.sub_self, Nat.reduceSub] <;> omega

theorem a_word8_prefix (input : Slice Std.U8) (a b d : Nat) (hd : d ≤ 8)
    (h : a_word8 input a / 2 ^ (64 - 8 * d) = a_word8 input b / 2 ^ (64 - 8 * d)) :
    ∀ k, k < d → input.val[b + k]! = input.val[a + k]! := by
  intro k hk
  have e : (256 : Nat) ^ (7 - k) = 2 ^ (64 - 8 * d) * 2 ^ (8 * (d - 1 - k)) := by
    rw [← pow_add, show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]
    congr 1; omega
  have key : a_word8 input a / 256 ^ (7 - k) = a_word8 input b / 256 ^ (7 - k) := by
    rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]
  have ha := a_word8_digit input a k (by omega)
  have hb := a_word8_digit input b k (by omega)
  rw [key] at ha
  scalar_tac

theorem Matches.a_add_prefix {input : Slice Std.U8} {a b l d : Nat} (h : Matches input a b l)
    (hd : d ≤ 8)
    (hw : a_word8 input (a + l) / 2 ^ (64 - 8 * d) = a_word8 input (b + l) / 2 ^ (64 - 8 * d)) :
    Matches input a b (l + d) := by
  intro k hk
  by_cases hkl : k < l
  · exact h k hkl
  · have := a_word8_prefix input (a + l) (b + l) d hd hw (k - l) (by omega)
    rw [show b + l + (k - l) = b + k by omega, show a + l + (k - l) = a + k by omega] at this
    exact this

theorem a_or_eq_add_of_mod {x t : Nat} (m : Nat) (hx : x % 2 ^ m = 0) (ht : t < 2 ^ m) :
    x ||| t = x + t := by
  have h := Nat.two_pow_add_eq_or_of_lt ht (x / 2 ^ m)
  have hx' : 2 ^ m * (x / 2 ^ m) = x := by
    have := Nat.div_add_mod x (2 ^ m); omega
  rw [hx'] at h
  exact h.symm

theorem a_shl_byte {x : Nat} (k : Nat) (hx : x < 256) (hk : k ≤ 56) :
    x <<< k % U64.size = x * 2 ^ k := by
  rw [Nat.shiftLeft_eq, U64.size_def]
  apply Nat.mod_eq_of_lt
  have : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by norm_num) hk
  have : x * 2 ^ k < 256 * 2 ^ 56 := by
    calc x * 2 ^ k < 256 * 2 ^ k := by
          apply Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
      _ ≤ 256 * 2 ^ 56 := Nat.mul_le_mul_left _ this
  simp only [U64.numBits] at *
  omega

theorem a_be8_nat {a b c d e f g h : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hd : d < 256) (he : e < 256) (hf : f < 256) (hg : g < 256) (hh : h < 256) :
    (a <<< 56 % U64.size ||| b <<< 48 % U64.size ||| c <<< 40 % U64.size |||
      d <<< 32 % U64.size ||| e <<< 24 % U64.size ||| f <<< 16 % U64.size |||
      g <<< 8 % U64.size ||| h) =
    a * 2^56 + b * 2^48 + c * 2^40 + d * 2^32 + e * 2^24 + f * 2^16 + g * 2^8 + h := by
  rw [a_shl_byte 56 ha (by norm_num), a_shl_byte 48 hb (by norm_num), a_shl_byte 40 hc (by norm_num),
    a_shl_byte 32 hd (by norm_num), a_shl_byte 24 he (by norm_num), a_shl_byte 16 hf (by norm_num),
    a_shl_byte 8 hg (by norm_num)]
  rw [a_or_eq_add_of_mod 56 (x := a * 2^56) (t := b * 2^48) (by omega) (by omega)]
  rw [a_or_eq_add_of_mod 48 (x := a * 2^56 + b * 2^48) (t := c * 2^40) (by omega) (by omega)]
  rw [a_or_eq_add_of_mod 40 (x := a * 2^56 + b * 2^48 + c * 2^40) (t := d * 2^32) (by omega)
    (by omega)]
  rw [a_or_eq_add_of_mod 32 (x := a * 2^56 + b * 2^48 + c * 2^40 + d * 2^32) (t := e * 2^24)
    (by omega) (by omega)]
  rw [a_or_eq_add_of_mod 24 (x := a * 2^56 + b * 2^48 + c * 2^40 + d * 2^32 + e * 2^24)
    (t := f * 2^16) (by omega) (by omega)]
  rw [a_or_eq_add_of_mod 16
    (x := a * 2^56 + b * 2^48 + c * 2^40 + d * 2^32 + e * 2^24 + f * 2^16)
    (t := g * 2^8) (by omega) (by omega)]
  rw [a_or_eq_add_of_mod 8
    (x := a * 2^56 + b * 2^48 + c * 2^40 + d * 2^32 + e * 2^24 + f * 2^16 + g * 2^8)
    (t := h) (by omega) (by omega)]

@[local step]
theorem a_be8_spec (s : Slice Std.U8) (i : Std.Usize) (h : i.val + 8 ≤ s.length) :
    slot.b_a_be8 s i ⦃ fun v => v.val = a_word8 s i.val ⦄ := by
  rw [slot.b_a_be8]
  step*
  simp only [← getElem!_pos] at *
  simp_all only [UScalar.val_or, U8.cast_U64_val_eq]
  rw [a_be8_nat (a_u8_lt _) (a_u8_lt _) (a_u8_lt _) (a_u8_lt _) (a_u8_lt _) (a_u8_lt _) (a_u8_lt _) (a_u8_lt _)]
  simp only [a_word8]

theorem a_nat_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  have : a ^^^ (a ^^^ b) = b := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [h, Nat.xor_zero] at this; exact this

theorem a_div_eq_of_xor_lt {x y m : Nat} (hz : x ^^^ y < 2 ^ m) : x / 2 ^ m = y / 2 ^ m := by
  have h : (x ^^^ y) >>> m = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hz
  rw [Nat.shiftRight_xor_distrib] at h
  have := a_nat_xor_eq_zero h
  simpa [Nat.shiftRight_eq_div_pow] using this

theorem a_lt_pow_leadingZeros (z : BitVec 64) :
    z.toNat < 2 ^ (64 - 8 * (BitVec.leadingZeros z / 8)) := by
  unfold BitVec.leadingZeros
  split
  case isTrue h => subst h; simp
  case isFalse h =>
    have hz : z.toNat ≠ 0 := by
      intro h0; apply h; exact BitVec.eq_of_toNat_eq (by simpa using h0)
    have hlog : Nat.log 2 z.toNat < 64 := Nat.log_lt_of_lt_pow hz z.isLt
    have h1 : z.toNat < 2 ^ (Nat.log 2 z.toNat).succ := Nat.lt_pow_succ_log_self (by norm_num) _
    refine lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) ?_)
    omega

theorem a_leadingZeros_lt_of_ne (z : BitVec 64) (h : z ≠ 0) : BitVec.leadingZeros z < 64 := by
  unfold BitVec.leadingZeros
  simp only [h, if_false]
  omega

theorem a_lz_spec (x : Std.U64) :
    lift (core.num.U64.leading_zeros x) ⦃ fun r => r = core.num.U64.leading_zeros x ∧ r.val ≤ 64 ⦄ := by
  simp only [lift, Std.WP.spec_ok, true_and]
  have hle : BitVec.leadingZeros x.bv ≤ 64 := by unfold BitVec.leadingZeros; split <;> omega
  simp only [core.num.U64.leading_zeros, UScalar.val, UScalarTy.U32_numBits_eq,
    BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem a_lz_val (x : Std.U64) :
    (core.num.U64.leading_zeros x).val = BitVec.leadingZeros x.bv := by
  have hle : BitVec.leadingZeros x.bv ≤ 64 := by unfold BitVec.leadingZeros; split <;> omega
  simp only [core.num.U64.leading_zeros, UScalar.val, UScalarTy.U32_numBits_eq,
    BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem Matches.a_word_lz {input : Slice Std.U8} {a b k : Nat} {pa pb r k1 : Std.Usize}
    {x y z : Std.U64} {lz q : Std.U32}
    (h : Matches input a b k) (hpa : pa.val = a + k) (hpb : pb.val = b + k)
    (hx : x.val = a_word8 input pa.val) (hy : y.val = a_word8 input pb.val)
    (hz : z.val = (x ^^^ y).val) (hz0 : ¬z = 0#u64) (hlz : lz = core.num.U64.leading_zeros z)
    (hq : q.val = lz.val / 8) (hr : r = UScalar.cast .Usize q) (hk1 : k1.val = k + r.val) :
    Matches input a b k1.val ∧ k1.val < k + 8 := by
  have hbv : z.bv ≠ 0 := by
    intro h0; apply hz0; exact UScalar.eq_of_val_eq (by simp [UScalar.val, h0])
  have hlt : BitVec.leadingZeros z.bv < 64 := a_leadingZeros_lt_of_ne z.bv hbv
  have hrv : r.val = BitVec.leadingZeros z.bv / 8 := by
    rw [hr, U32.cast_Usize_val_eq, hq, hlz, a_lz_val]
  rw [hpa] at hx; rw [hpb] at hy
  refine ⟨?_, by omega⟩
  rw [hk1, hrv]
  have hle : BitVec.leadingZeros z.bv ≤ 64 := by unfold BitVec.leadingZeros; split <;> omega
  apply Matches.a_add_prefix h (by omega)
  rw [← hx, ← hy]
  apply a_div_eq_of_xor_lt
  rw [← UScalar.val_xor, ← hz]
  exact a_lt_pow_leadingZeros z.bv

theorem Matches.a_word_zero {input : Slice Std.U8} {a b k : Nat} {pa pb k1 : Std.Usize}
    {x y z : Std.U64}
    (h : Matches input a b k) (hpa : pa.val = a + k) (hpb : pb.val = b + k)
    (hx : x.val = a_word8 input pa.val) (hy : y.val = a_word8 input pb.val)
    (hz : z.val = (x ^^^ y).val) (hz0 : z = 0#u64) (hk1 : k1.val = k + 8) :
    Matches input a b k1.val := by
  have hxy : x.val = y.val := by
    apply a_nat_xor_eq_zero
    rw [← UScalar.val_xor, ← hz, hz0]; rfl
  rw [hpa] at hx; rw [hpb] at hy
  rw [hk1]
  apply Matches.a_add_prefix h (le_refl 8)
  rw [← hx, ← hy, hxy]

theorem Matches.a_byte' {input : Slice Std.U8} {a b l : Nat} {pa pb l1 : Std.Usize}
    {x y : Std.U8} (h : Matches input a b l) (hpa : pa.val = a + l) (hpb : pb.val = b + l)
    (hpa' : pa.val < input.val.length) (hpb' : pb.val < input.val.length)
    (hx : x = input.val[pa.val]) (hy : y = input.val[pb.val]) (hxy : x = y)
    (hl1 : l1.val = l + 1) : Matches input a b l1.val := by
  rw [hl1]
  apply LZ77.Matches.succ h
  rw [← hpa, ← hpb, getElem!_pos input.val pa.val hpa', getElem!_pos input.val pb.val hpb',
    ← hx, ← hy, hxy]

attribute [local step] a_lz_spec in
theorem a_common_loop0_spec (s : Slice Std.U8) (a b cap k : Std.Usize) (run : Std.U32)
    (ha : a.val + cap.val ≤ s.length) (hb : b.val + cap.val ≤ s.length) (hcap : cap.val ≤ 258)
    (hk : k.val ≤ cap.val) (hm : Matches s a.val b.val k.val) :
    slot.b_a_common_loop0 s a b cap k run ⦃ fun r =>
      r.1.val ≤ cap.val ∧ Matches s a.val b.val r.1.val ⦄ := by
  rw [slot.b_a_common_loop0]
  have hmax : s.length ≤ Std.Usize.max := Std.Slice.length_ineq s
  apply Std.loop.spec_decr_nat
    (measure := fun r => cap.val - r.1.val + r.2.val)
    (inv := fun r => r.1.val ≤ cap.val ∧ Matches s a.val b.val r.1.val)
  · rintro ⟨k, run⟩ ⟨hk, hm⟩
    simp only at hk hm
    simp only [slot.b_a_common_loop0.body]
    step*
    all_goals first
      | scalar_tac
      | (refine ⟨by scalar_tac, Matches.a_word_zero hm (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by scalar_tac),
          by scalar_tac⟩)
      | (have hw := Matches.a_word_lz hm (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption)
         refine ⟨by scalar_tac, hw.1, by scalar_tac⟩)
  · exact ⟨hk, hm⟩

theorem a_common_loop1_spec (s : Slice Std.U8) (a b cap k : Std.Usize) (run : Std.U32)
    (ha : a.val + cap.val ≤ s.length) (hb : b.val + cap.val ≤ s.length)
    (hk : k.val ≤ cap.val) (hm : Matches s a.val b.val k.val) :
    slot.b_a_common_loop1 s a b cap k run ⦃ fun r =>
      r.val ≤ cap.val ∧ Matches s a.val b.val r.val ⦄ := by
  rw [slot.b_a_common_loop1]
  have hmax : s.length ≤ Std.Usize.max := Std.Slice.length_ineq s
  apply Std.loop.spec_decr_nat
    (measure := fun r => cap.val - r.1.val + r.2.val)
    (inv := fun r => r.1.val ≤ cap.val ∧ Matches s a.val b.val r.1.val)
  · rintro ⟨k, run⟩ ⟨hk, hm⟩
    simp only at hk hm
    simp only [slot.b_a_common_loop1.body]
    step*
    all_goals first
      | scalar_tac
      | exact ⟨hk, hm⟩
      | (refine ⟨by scalar_tac, Matches.a_byte' hm (by assumption) (by assumption) (by scalar_tac)
          (by scalar_tac) (by assumption) (by assumption) (by assumption) (by assumption),
          by scalar_tac⟩)
  · exact ⟨hk, hm⟩

@[local step]
theorem a_common_spec (s : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ s.length) (hb : b.val + cap.val ≤ s.length) (hcap : cap.val ≤ 258) :
    slot.b_a_common s a b cap ⦃ fun l => l.val ≤ cap.val ∧ Matches s a.val b.val l.val ⦄ := by
  rw [slot.b_a_common]
  apply Std.WP.spec_bind (a_common_loop0_spec s a b cap 0#usize 1#u32 ha hb hcap (by simp)
    (LZ77.Matches.zero s a.val b.val))
  rintro ⟨k, run⟩ ⟨hk, hm⟩
  exact a_common_loop1_spec s a b cap k run ha hb hk hm

theorem Matches.a_mono_eq {input : Slice Std.U8} {a b n m : Nat} (h : Matches input a b n)
    (hm : m = n) : Matches input a b m := by subst hm; exact h

theorem Matches.a_word_eq {input : Slice Std.U8} {a b k : Nat} {pa pb k1 : Std.Usize}
    {x y : Std.U64}
    (h : Matches input a b k) (hpa : pa.val = a + k) (hpb : pb.val = b + k)
    (hx : x.val = a_word8 input pa.val) (hy : y.val = a_word8 input pb.val)
    (hxy : x = y) (hk1 : k1.val = k + 8) :
    Matches input a b k1.val := by
  rw [hpa] at hx; rw [hpb] at hy
  rw [hk1]
  apply Matches.a_add_prefix h (le_refl 8)
  rw [← hx, ← hy, hxy]

theorem a_same_loop0_spec (s : Slice Std.U8) (a b len k ok : Std.Usize)
    (ha : a.val + len.val ≤ s.length) (hb : b.val + len.val ≤ s.length) (hlen : len.val ≤ 258)
    (hk : k.val ≤ len.val) (hm : Matches s a.val b.val k.val) :
    slot.b_a_same_loop0 s a b len k ok ⦃ fun r =>
      r.1.val ≤ len.val ∧ Matches s a.val b.val r.1.val ∧ (r.2.val = 1 → len.val < r.1.val + 8) ⦄ := by
  rw [slot.b_a_same_loop0]
  have hmax : s.length ≤ Std.Usize.max := Std.Slice.length_ineq s
  apply Std.loop.spec_decr_nat
    (measure := fun r => len.val - r.1.val + r.2.val)
    (inv := fun r => r.1.val ≤ len.val ∧ Matches s a.val b.val r.1.val)
  · rintro ⟨k, ok⟩ ⟨hk, hm⟩
    simp only at hk hm
    simp only [slot.b_a_same_loop0.body]
    step*
    all_goals first
      | scalar_tac
      | (refine ⟨by scalar_tac, Matches.a_word_eq hm (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by scalar_tac), by scalar_tac⟩)
  · exact ⟨hk, hm⟩

@[local step]
theorem a_same_loop1_spec (s : Slice Std.U8) (a b len k ok : Std.Usize)
    (ha : a.val + len.val ≤ s.length) (hb : b.val + len.val ≤ s.length)
    (hk : k.val ≤ len.val) (hm : Matches s a.val b.val k.val) :
    slot.b_a_same_loop1 s a b len k ok ⦃ fun r => r.val = 1 → Matches s a.val b.val len.val ⦄ := by
  rw [slot.b_a_same_loop1]
  have hmax : s.length ≤ Std.Usize.max := Std.Slice.length_ineq s
  apply Std.loop.spec_decr_nat
    (measure := fun r => len.val - r.1.val + r.2.val)
    (inv := fun r => r.1.val ≤ len.val ∧ Matches s a.val b.val r.1.val)
  · rintro ⟨k, ok⟩ ⟨hk, hm⟩
    simp only at hk hm
    simp only [slot.b_a_same_loop1.body]
    step*
    all_goals first
      | scalar_tac
      | (refine ⟨by scalar_tac, Matches.a_byte' hm (by assumption) (by assumption) (by scalar_tac)
          (by scalar_tac) (by assumption) (by assumption) (by assumption) (by assumption),
          by scalar_tac⟩)
  · exact ⟨hk, hm⟩

@[local step]
theorem a_same_loop2_spec (s : Slice Std.U8) (a b len k ok : Std.Usize)
    (ha : a.val + len.val ≤ s.length) (hb : b.val + len.val ≤ s.length)
    (hk : k.val ≤ len.val) (hm : Matches s a.val b.val k.val) :
    slot.b_a_same_loop2 s a b len k ok ⦃ fun r => r.val = 1 → Matches s a.val b.val len.val ⦄ := by
  rw [slot.b_a_same_loop2]
  have hmax : s.length ≤ Std.Usize.max := Std.Slice.length_ineq s
  apply Std.loop.spec_decr_nat
    (measure := fun r => len.val - r.1.val + r.2.val)
    (inv := fun r => r.1.val ≤ len.val ∧ Matches s a.val b.val r.1.val)
  · rintro ⟨k, ok⟩ ⟨hk, hm⟩
    simp only at hk hm
    simp only [slot.b_a_same_loop2.body]
    step*
    all_goals first
      | scalar_tac
      | (refine ⟨by scalar_tac, Matches.a_byte' hm (by assumption) (by assumption) (by scalar_tac)
          (by scalar_tac) (by assumption) (by assumption) (by assumption) (by assumption),
          by scalar_tac⟩)
  · exact ⟨hk, hm⟩

theorem Matches.a_mask {input : Slice Std.U8} {a b k len : Nat} {pa pb : Std.Usize}
    {x y z w : Std.U64} {sh : Std.U32}
    (h : Matches input a b k) (hpa : pa.val = a + k) (hpb : pb.val = b + k)
    (hx : x.val = a_word8 input pa.val) (hy : y.val = a_word8 input pb.val)
    (hz : z.val = (x ^^^ y).val) (hw : w.val = z.val >>> sh.val) (hw0 : ¬(w != 0#u64) = true)
    (hsh : sh.val = 64 - 8 * (len - k)) (hk : k < len) (hlen : len < k + 8) :
    Matches input a b len := by
  have hw0 : w.val = 0 := by simpa using hw0
  rw [hpa] at hx; rw [hpb] at hy
  have := Matches.a_add_prefix (d := len - k) h (by omega) (by
    rw [← hx, ← hy, ← hsh]
    have h0 : (x.val ^^^ y.val) >>> sh.val = 0 := by rw [← UScalar.val_xor, ← hz, ← hw, hw0]
    rw [Nat.shiftRight_xor_distrib] at h0
    have := a_nat_xor_eq_zero h0
    simpa [Nat.shiftRight_eq_div_pow] using this)
  rw [show k + (len - k) = len by omega] at this
  exact this

@[local step]
theorem a_same_spec (s : Slice Std.U8) (a b len : Std.Usize)
    (ha : a.val + len.val ≤ s.length) (hb : b.val + len.val ≤ s.length) (hlen : len.val ≤ 258)
    (ha8 : a.val + len.val + 7 ≤ Std.Usize.max) (hb8 : b.val + len.val + 7 ≤ Std.Usize.max) :
    slot.b_a_same s a b len ⦃ fun r => r.val = 1 → Matches s a.val b.val len.val ⦄ := by
  rw [slot.b_a_same]
  apply Std.WP.spec_bind (a_same_loop0_spec s a b len 0#usize 1#usize ha hb hlen (by simp)
    (LZ77.Matches.zero s a.val b.val))
  rintro ⟨k, ok⟩ ⟨hk, hm, hok⟩
  simp only at hk hm hok
  step*

  intro _
  exact Matches.a_mask hm (by assumption) (by assumption) (by assumption) (by assumption)
    (by assumption) (by assumption) (by assumption) (by scalar_tac) (by scalar_tac)
    (by scalar_tac)

theorem a_lz32_le (x : Std.U32) (k : Nat) (hk : k < 32) (hx : 2 ^ k ≤ x.val) :
    (core.num.U32.leading_zeros x).val ≤ 31 - k := by
  have hne : x.bv ≠ 0 := by
    intro h0
    have : x.val = 0 := by simp [UScalar.val, h0]
    have : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  have hlog : k ≤ Nat.log 2 x.bv.toNat := by
    apply Nat.le_log_of_pow_le (by norm_num)
    have : x.val = x.bv.toNat := rfl
    omega
  have hle : BitVec.leadingZeros x.bv ≤ 32 := by unfold BitVec.leadingZeros; split <;> omega
  have hv : (core.num.U32.leading_zeros x).val = BitVec.leadingZeros x.bv := by
    simp only [core.num.U32.leading_zeros, UScalar.val, UScalarTy.U32_numBits_eq,
      BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  rw [hv]
  unfold BitVec.leadingZeros
  simp only [hne, if_false]
  omega

theorem a_lz32_spec (x : Std.U32) :
    lift (core.num.U32.leading_zeros x) ⦃ fun r => r = core.num.U32.leading_zeros x ∧
      (4 ≤ x.val → r.val ≤ 29) ∧ (8 ≤ x.val → r.val ≤ 28) ⦄ := by
  simp only [lift, Std.WP.spec_ok, true_and]
  exact ⟨fun h => a_lz32_le x 2 (by norm_num) (by simpa using h),
    fun h => a_lz32_le x 3 (by norm_num) (by simpa using h)⟩

theorem a_hcast_I32_spec {ty : UScalarTy} (x : UScalar ty) (h : x.val ≤ 2147483647) :
    lift (UScalar.hcast .I32 x) ⦃ fun y => y.val = x.val ⦄ :=
  UScalar.hcast_inBounds_spec .I32 x (by simp [I32.max_def, I32.numBits]; omega)

theorem a_hcast_I32_val {ty : UScalarTy} (x : UScalar ty) (h : x.val ≤ 2147483647) :
    (UScalar.hcast .I32 x).val = x.val := by
  have := a_hcast_I32_spec x h
  simpa [lift] using this

theorem a_GBASE_bound : -500000000 ≤ slot.B_A_GBASE.val ∧ slot.B_A_GBASE.val ≤ 500000000 := by
  unfold slot.B_A_GBASE
  simp

theorem a_L2B_bound : -500000000 ≤ slot.B_A_L2B.val ∧ slot.B_A_L2B.val ≤ 500000000 := by
  unfold slot.B_A_L2B
  simp

theorem a_prod_bound {i hlit : Int} {l : Nat} (hi : i = (l : Int)) (hl : l ≤ 258) (h0 : 0 ≤ hlit)
    (h1 : hlit ≤ 1000000) : 0 ≤ i * hlit ∧ i * hlit ≤ 258000000 := by
  subst hi
  refine ⟨Int.mul_nonneg (by omega) h0, ?_⟩
  calc (l : Int) * hlit ≤ 258 * hlit := Int.mul_le_mul_of_nonneg_right (by omega) h0
    _ ≤ 258000000 := by omega

attribute [local step] a_lz32_spec a_hcast_I32_spec in
theorem a_gain_spec (l d : Std.Usize) (hlit : Std.I32) (hl : l.val ≤ 258) (hd : d.val ≤ 32768)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000) :
    slot.b_a_gain l d hlit ⦃ fun r => -1000000000 ≤ r.val ∧ r.val ≤ 1000000000 ⦄ := by
  rw [slot.b_a_gain]
  have ⟨hG0, hG1⟩ := a_GBASE_bound

  apply WP.spec_bind (Pₘ := fun (c : Std.I32) =>
    slot.B_A_GBASE.val ≤ c.val ∧ c.val ≤ slot.B_A_GBASE.val + 464)
  · repeat' (split <;> step*)
    all_goals scalar_tac
  intro c hc
  apply WP.spec_bind (Pₘ := fun (c1 : Std.I32) =>
    slot.B_A_GBASE.val ≤ c1.val ∧ c1.val ≤ slot.B_A_GBASE.val + 944)
  · repeat' (split <;> step*)
    all_goals scalar_tac
  intro c1 hc1
  step*
  all_goals first
    | scalar_tac
    | (have := a_prod_bound (by assumption) hl hh0 hh1; scalar_tac)

attribute [local step] a_gain_spec

def AHeadBound {N : Std.Usize} (head : Array Std.U32 N) (B : Nat) : Prop :=
  ∀ j : Nat, j < head.val.length → (head.val[j]!).val ≤ B

theorem AHeadBound.mono {N : Std.Usize} {head : Array Std.U32 N} {B B' : Nat}
    (h : AHeadBound head B) (hB : B ≤ B') : AHeadBound head B' := fun j hj => le_trans (h j hj) hB

theorem AHeadBound.init (N : Std.Usize) : AHeadBound (Std.Array.repeat N 0#u32) 0 := by
  intro j hj
  rw [Std.Array.repeat_val] at hj ⊢
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_replicate_of_lt (by simpa using hj)]
  rfl

theorem AHeadBound.set {N : Std.Usize} {head : Array Std.U32 N} {B : Nat} (h : AHeadBound head B)
    (a : Std.Usize) (v : Std.U32) (hv : v.val ≤ B) : AHeadBound (head.set a v) B := by
  intro j hj
  rw [Std.Array.set_val_eq] at hj ⊢
  rw [List.length_set] at hj
  by_cases hja : a.val = j
  · subst hja
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hj]
    exact hv
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hja, ← List.getElem!_eq_getElem?_getD]
    exact h j hj

theorem AHeadBound.update {N : Std.Usize} {head head1 : Array Std.U32 N} {B : Nat}
    {a i : Std.Usize} {v : Std.U32} (h : AHeadBound head B) (hv : v = UScalar.cast .U32 i)
    (hi : i.val ≤ B) (h1 : head1 = head.set a v) : AHeadBound head1 B := by
  subst h1
  apply AHeadBound.set h a v
  rw [hv]
  have : (UScalar.cast .U32 i).val = i.val % 2 ^ 32 := by
    simp only [UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]
  rw [this]
  exact le_trans (Nat.mod_le _ _) hi

theorem AHeadBound.get {N : Std.Usize} {head : Array Std.U32 N} {B : Nat} (h : AHeadBound head B)
    (a : Std.Usize) (x : Std.U32) (ha : a.val < head.val.length) (hx : x = head.val[a.val]) :
    x.val ≤ B := by
  have := h a.val ha
  rw [getElem!_pos head.val a.val ha, ← hx] at this
  exact this

theorem a_cast_usize_le {x : Std.U32} {y : Std.Usize} {B : Nat} (h : y = UScalar.cast .Usize x)
    (hx : x.val ≤ B) : y.val ≤ B := by
  rw [h, U32.cast_Usize_val_eq]; exact hx

@[local step]
theorem a_be4_spec (s : Slice Std.U8) (i : Std.Usize) (hi : i.val + 4 ≤ Std.Usize.max) :
    slot.b_a_be4 s i ⦃ fun _ => True ⦄ := by
  rw [slot.b_a_be4]
  step*

@[local step]
theorem a_insert_spec (s : Slice Std.U8) {H W : Std.Usize} (head : Array Std.U32 H)
    (prev : Array Std.U32 W) (i : Std.Usize) (mask : Std.U32) (B : Nat) (hB : AHeadBound head B)
    (hi : i.val < B + 1) (hi4 : i.val + 4 ≤ Std.Usize.max) (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_insert s head prev i mask ⦃ fun r => r.1.val ≤ B ∧ AHeadBound r.2.1 B ⦄ := by
  rw [slot.b_a_insert]
  step*
  have hold : old.val ≤ B := AHeadBound.get hB a old (by scalar_tac) (by assumption)
  exact ⟨a_cast_usize_le (by assumption) hold,
    AHeadBound.update hB (by assumption) (by omega) (by assumption)⟩

@[local step]
theorem a_insert_dna_spec (s : Slice Std.U8) {H W : Std.Usize} (head : Array Std.U32 H)
    (prev : Array Std.U32 W) (i : Std.Usize) (mask : Std.U32) (B : Nat) (hB : AHeadBound head B)
    (hi : i.val < B + 1) (hi8 : i.val + 8 ≤ s.length) (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_insert_dna s head prev i mask ⦃ fun r => r.1.val ≤ B ∧ AHeadBound r.2.1 B ⦄ := by
  rw [slot.b_a_insert_dna]
  step*
  have hold : old.val ≤ B := AHeadBound.get hB a old (by scalar_tac) (by assumption)
  exact ⟨a_cast_usize_le (by assumption) hold,
    AHeadBound.update hB (by assumption) (by omega) (by assumption)⟩

def ACand (s : Slice Std.U8) (p cap best bd : Nat) : Prop :=
  bd = 0 ∨ (1 ≤ bd ∧ bd ≤ 32768 ∧ bd ≤ p ∧ best ≤ cap ∧ Matches s (p - bd) p best)

theorem a_dist_of_wrapping {p c d i : Std.Usize} (hc : c.val ≤ p.val)
    (hd : d = core.num.Usize.wrapping_sub p c) (hi : i = core.num.Usize.wrapping_sub d 1#usize)
    (hlt : i < 32768#usize) : d.val = p.val - c.val ∧ 1 ≤ d.val ∧ d.val ≤ 32768 := by
  have hsz : 4294967296 ≤ Usize.size := by scalar_tac
  have hpl : p.val < Usize.size := by scalar_tac
  have hdv : d.val = p.val - c.val := by
    rw [hd, core.num.Usize.wrapping_sub_val_eq, UScalar.size_UScalarTyUsize]
    rw [show p.val + (Usize.size - c.val) = (p.val - c.val) + Usize.size by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hiv : i.val < 32768 := by scalar_tac
  have hdl : d.val < Usize.size := by omega
  rw [hi, core.num.Usize.wrapping_sub_val_eq, UScalar.size_UScalarTyUsize] at hiv
  simp only [show (1#usize).val = 1 by simp] at hiv
  refine ⟨hdv, ?_, ?_⟩
  · by_contra h0
    have : d.val = 0 := by omega
    rw [this, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hiv
    omega
  · by_cases h0 : d.val = 0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hiv
      omega
    · rw [show d.val + (Usize.size - 1) = (d.val - 1) + Usize.size by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)] at hiv
      omega

theorem ACand.of_common {s : Slice Std.U8} {p c d i l cap : Std.Usize} (hc : c.val ≤ p.val)
    (hd : d = core.num.Usize.wrapping_sub p c) (hi : i = core.num.Usize.wrapping_sub d 1#usize)
    (hlt : i < 32768#usize) (hl : l.val ≤ cap.val) (hm : Matches s c.val p.val l.val) :
    ACand s p.val cap.val l.val d.val := by
  obtain ⟨hdv, hd1, hd2⟩ := a_dist_of_wrapping hc hd hi hlt
  refine Or.inr ⟨hd1, hd2, by omega, hl, ?_⟩
  rw [show p.val - d.val = c.val by omega]
  exact hm

theorem a_dist_of_wrapping2 {p c d i : Std.Usize} (hc : c.val ≤ p.val + 2)
    (hd : d = core.num.Usize.wrapping_sub p c) (hi : i = core.num.Usize.wrapping_sub d 1#usize)
    (hlt : i < 32768#usize) : c.val ≤ p.val := by
  by_contra hcp
  have hsz : 4294967296 ≤ Usize.size := by scalar_tac
  have hcl : c.val < Usize.size := by scalar_tac
  have hdv : d.val = Usize.size - (c.val - p.val) := by
    rw [hd, core.num.Usize.wrapping_sub_val_eq, UScalar.size_UScalarTyUsize]
    rw [show p.val + (Usize.size - c.val) = Usize.size - (c.val - p.val) by omega,
      Nat.mod_eq_of_lt (by omega)]
  have hiv : i.val < 32768 := by scalar_tac
  rw [hi, core.num.Usize.wrapping_sub_val_eq, UScalar.size_UScalarTyUsize] at hiv
  simp only [show (1#usize).val = 1 by simp] at hiv
  rw [show d.val + (Usize.size - 1) = (d.val - 1) + Usize.size by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)] at hiv
  omega

theorem a_walk_loop_spec (s : Slice Std.U8) {W : Std.Usize} (prev : Array Std.U32 W)
    (p cap gm : Std.Usize) (hlit : Std.I32) (n best bd : Std.Usize) (bg : Std.I32)
    (c k stop : Std.Usize) (pb : Std.U8)
    (hn : n.val = s.length) (hcap : p.val + cap.val ≤ s.length) (hcap258 : cap.val ≤ 258)
    (hc : c.val ≤ p.val + 2) (hbest : p.val + best.val ≤ s.length + 1)
    (hcand : ACand s p.val cap.val best.val bd.val) (hW : 0 < W.val)
    (hbg : -1000000000 ≤ bg.val ∧ bg.val ≤ 1000000000)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000) :
    slot.b_a_walk_loop s prev p cap gm hlit n best bd bg c k stop pb ⦃ fun r =>
      p.val + r.1.val ≤ s.length + 1 ∧ ACand s p.val cap.val r.1.val r.2.1.val ∧
      -1000000000 ≤ r.2.2.val ∧ r.2.2.val ≤ 1000000000 ⦄ := by
  rw [slot.b_a_walk_loop]
  have hmax : s.length ≤ Std.Usize.max := Std.Slice.length_ineq s
  apply Std.loop.spec_decr_nat
    (measure := fun r => r.2.2.2.2.1.val)
    (inv := fun r => r.2.2.2.1.val ≤ p.val + 2 ∧ p.val + r.1.val ≤ s.length + 1 ∧
      ACand s p.val cap.val r.1.val r.2.1.val ∧
      -1000000000 ≤ r.2.2.1.val ∧ r.2.2.1.val ≤ 1000000000)
  · rintro ⟨best, bd, bg, c, k, pb⟩ ⟨hc, hbest, hcand, hbg0, hbg1⟩
    simp only at hc hbest hcand
    simp only [slot.b_a_walk_loop.body]
    step*

    case hmax =>
      have hcp := a_dist_of_wrapping2 hc (by assumption) (by assumption) (by assumption)
      obtain ⟨hdv, hd1, hd2⟩ := a_dist_of_wrapping hcp (by assumption) (by assumption) (by assumption)
      scalar_tac
    have hcp := a_dist_of_wrapping2 hc (by assumption) (by assumption) (by assumption)
    obtain ⟨hdv, hd1, hd2⟩ := a_dist_of_wrapping hcp (by assumption) (by assumption) (by assumption)

    apply WP.spec_bind (Pₘ := fun (x : Std.Usize × Std.Usize × Std.I32 × Std.Usize × Std.U8) =>
      p.val + x.1.val ≤ s.length + 1 ∧ ACand s p.val cap.val x.1.val x.2.1.val ∧
      1 ≤ x.2.2.2.1.val ∧ x.2.2.2.1.val ≤ k.val ∧
      -1000000000 ≤ x.2.2.1.val ∧ x.2.2.1.val ≤ 1000000000)
    · split
      · step
        apply WP.spec_bind (Pₘ := fun (x : Std.I32 × Std.Usize) => -1000000000 ≤ x.1.val ∧ x.1.val ≤ 1000000000)
        · repeat' (split <;> step*)
        · rintro ⟨bg2, take⟩ ⟨hbg20, hbg21⟩
          apply WP.spec_bind (Pₘ := fun (x : Std.Usize × Std.Usize × Std.Usize × Std.U8) =>
            p.val + x.1.val ≤ s.length + 1 ∧ ACand s p.val cap.val x.1.val x.2.1.val ∧
            1 ≤ x.2.2.1.val ∧ x.2.2.1.val ≤ k.val)
          · split
            · repeat' (split <;> step*)
              all_goals (refine ⟨by scalar_tac, ACand.of_common hcp (by assumption)
                (by assumption) (by assumption) (by assumption) (by assumption), by scalar_tac,
                by scalar_tac⟩)
            · step*
          · rintro ⟨i3, i4, i5, i6⟩ h
            step*
      · step*
    · rintro ⟨best1, bd1, bg1, k1, pb1⟩ ⟨h1, h2, h3, h4, h5, h6⟩
      step*
  · exact ⟨hc, hbest, hcand, hbg⟩

attribute [local step] a_walk_loop_spec

@[local step]
theorem a_walk_spec (s : Slice Std.U8) {W : Std.Usize} (prev : Array Std.U32 W)
    (p start cap «have» depth nice gm : Std.Usize) (hlit : Std.I32)
    (hcap : p.val + cap.val ≤ s.length) (hcap258 : cap.val ≤ 258) (hst : start.val ≤ p.val + 2)
    (hhave : p.val + «have».val ≤ s.length + 1) (hW : 0 < W.val)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000) :
    slot.b_a_walk s prev p start cap «have» depth nice gm hlit ⦃ fun r =>
      p.val + r.1.val ≤ s.length + 1 ∧ ACand s p.val cap.val r.1.val r.2.1.val ∧
      -1000000000 ≤ r.2.2.val ∧ r.2.2.val ≤ 1000000000 ⦄ := by
  rw [slot.b_a_walk]
  have hmax : s.length ≤ Std.Usize.max := Std.Slice.length_ineq s
  repeat' (split <;> step*)
  all_goals first
    | exact Or.inl rfl
    | (rcases best_post2 with h0 | h0 <;> scalar_tac)
    | assumption
    | scalar_tac

def AMatchAt (s : Slice Std.U8) (p l d : Nat) : Prop :=
  3 ≤ l ∧ l ≤ 258 ∧ p + l ≤ s.length ∧ 1 ≤ d ∧ d ≤ 32768 ∧ d ≤ p ∧ Matches s (p - d) p l

def AFoundAt (s : Slice Std.U8) (p l d : Nat) : Prop := l < 3 ∨ AMatchAt s p l d

theorem AFoundAt.of_cand {s : Slice Std.U8} {p cap : Nat} {l d : Std.Usize}
    (hc : ACand s p cap l.val d.val) (hd : ¬d = 0#usize) (hcap : cap ≤ 258)
    (hpc : p + cap ≤ s.length) : AFoundAt s p l.val d.val := by
  have hd' : d.val ≠ 0 := by intro h; apply hd; exact UScalar.eq_of_val_eq (by simp [h])
  rcases hc with h0 | ⟨hd1, hd2, hdp, hl, hm⟩
  · exact absurd h0 hd'
  · rcases Nat.lt_or_ge l.val 3 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr ⟨h3, by omega, by omega, hd1, hd2, hdp, hm⟩

theorem ACand.len_le {s : Slice Std.U8} {p cap : Nat} {l d : Std.Usize}
    (hc : ACand s p cap l.val d.val) (hd : ¬d = 0#usize) (hcap : cap ≤ 258) : l.val ≤ 258 := by
  have hd' : d.val ≠ 0 := by intro h; apply hd; exact UScalar.eq_of_val_eq (by simp [h])
  rcases hc with h0 | ⟨_, _, _, hl, _⟩
  · exact absurd h0 hd'
  · omega

theorem ACand.dist_le {s : Slice Std.U8} {p cap l d : Nat} (hc : ACand s p cap l d) :
    d ≤ 32768 := by
  rcases hc with h0 | ⟨_, hd, _⟩ <;> omega

theorem AFoundAt.none (s : Slice Std.U8) (p : Nat) : AFoundAt s p (0#usize).val (0#usize).val :=
  Or.inl (by simp)

theorem AFoundAt.real {s : Slice Std.U8} {p l d : Nat} (hf : AFoundAt s p l d) (h3 : 3 ≤ l) :
    AMatchAt s p l d := by
  rcases hf with h | h
  · omega
  · exact h

@[local step]
theorem a_find_spec (s : Slice Std.U8) {W : Std.Usize} (prev : Array Std.U32 W)
    (p st «have» minl depth nice gm : Std.Usize) (hlit : Std.I32)
    (hp : p.val ≤ s.length) (hst : st.val ≤ p.val + 2) (hhave : p.val + «have».val ≤ s.length + 1)
    (hhave258 : «have».val ≤ 258) (hminl : 1 ≤ minl.val) (hminl' : p.val + minl.val ≤ s.length + 1)
    (hW : 0 < W.val) (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000) :
    slot.b_a_find s prev p st «have» minl depth nice gm hlit ⦃ fun r => AFoundAt s p.val r.1.val r.2.1.val ∧
      r.1.val ≤ 258 ∧ r.2.1.val ≤ 32768 ∧ -1000000000 ≤ r.2.2.val ∧ r.2.2.val ≤ 1000000000 ⦄ := by
  rw [slot.b_a_find]
  step*
  repeat' (split <;> step*)
  all_goals first
    | exact ⟨AFoundAt.none s p.val, by simp, by simp, by scalar_tac, by scalar_tac⟩
    | exact ⟨AFoundAt.of_cand (by assumption) (by assumption) (by scalar_tac) (by scalar_tac),
        ACand.len_le (by assumption) (by assumption) (by scalar_tac),
        ACand.dist_le (by assumption), by scalar_tac, by scalar_tac⟩

def ANear (s : Slice Std.U8) (p len r : Nat) : Prop :=
  r = 0 ∨ (1 ≤ r ∧ r ≤ 32768 ∧ r ≤ p ∧ Matches s (p - r) p len)

theorem ANear.none (s : Slice Std.U8) (p len : Nat) : ANear s p len (0#usize).val := Or.inl (by simp)

theorem ANear.found {s : Slice Std.U8} {p c d i len r : Std.Usize} (hc : c.val < p.val)
    (hd : d = core.num.Usize.wrapping_sub p c) (hi : i = core.num.Usize.wrapping_sub d 1#usize)
    (hlt : i < 32768#usize) (hsame : r.val = 1 → Matches s c.val p.val len.val)
    (hr : r = 1#usize) : ANear s p.val len.val d.val := by
  obtain ⟨hdv, hd1, hd2⟩ := a_dist_of_wrapping (le_of_lt hc) hd hi hlt
  refine Or.inr ⟨hd1, hd2, by omega, ?_⟩
  rw [show p.val - d.val = c.val by omega]
  exact hsame (by rw [hr]; rfl)

theorem a_closest_loop_spec (s : Slice Std.U8) {W : Std.Usize} (prev : Array Std.U32 W)
    (p len n c k res : Std.Usize) (hn : n.val = s.length) (hp : p.val + len.val + 8 ≤ s.length)
    (hlen : len.val ≤ 258) (hW : 0 < W.val) (hres : ANear s p.val len.val res.val) :
    slot.b_a_closest_loop s prev p len n c k res ⦃ fun r => ANear s p.val len.val r.val ⦄ := by
  rw [slot.b_a_closest_loop]
  have hmax : s.length ≤ Std.Usize.max := Std.Slice.length_ineq s
  apply Std.loop.spec_decr_nat
    (measure := fun r => r.2.1.val)
    (inv := fun r => ANear s p.val len.val r.2.2.val)
  · rintro ⟨c, k, res⟩ hres
    simp only at hres
    simp only [slot.b_a_closest_loop.body]
    step*
    all_goals first
      | exact ⟨hres, by scalar_tac⟩
      | exact hres
      | exact ⟨ANear.found (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption), by scalar_tac⟩
  · exact hres

@[local step]
theorem a_closest_spec (s : Slice Std.U8) {W : Std.Usize} (prev : Array Std.U32 W)
    (p start len depth : Std.Usize) (hp : p.val + len.val + 8 ≤ s.length) (hlen : len.val ≤ 258)
    (hW : 0 < W.val) :
    slot.b_a_closest s prev p start len depth ⦃ fun r => ANear s p.val len.val r.val ⦄ := by
  rw [slot.b_a_closest]
  exact a_closest_loop_spec s prev p len (Std.Slice.len s) start depth 0#usize (by simp) hp hlen hW
    (ANear.none s p.val len.val)

theorem a_copyN_take_prefix (acc : List Nat) (d : Nat) :
    ∀ n, (LZ77.copyN acc d n).take acc.length = acc := by
  intro n
  induction n with
  | zero => simp [LZ77.copyN]
  | succ m ih =>
    simp only [LZ77.copyN]
    rw [List.take_append_of_le_length (by simp)]
    exact ih

theorem a_foldlM_emit_length : ∀ (ts : List Nat) (init acc : List Nat),
    ts.foldlM LZ77.emit init = some acc → init.length + ts.length ≤ acc.length := by
  intro ts
  induction ts with
  | nil => intro init acc h; simp at h; subst h; simp
  | cons t ts ih =>
    intro init acc h
    simp only [List.foldlM_cons] at h
    cases he : LZ77.emit init t with
    | none => rw [he] at h; simp at h
    | some a =>
      rw [he] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      have h1 := ih a acc h
      have h2 : init.length + 1 ≤ a.length := by
        simp only [LZ77.emit] at he
        split at he
        · simp at he; subst he; simp
        · split at he
          · split at he
            · simp at he; subst he; rw [LZ77.copyN_length]; simp only [LZ77.tokLen]; omega
            · simp at he
          · simp at he
      simp only [List.length_cons]
      omega

theorem a_decode_length_le {ts acc : List Nat} (h : LZ77.decode ts = some acc) :
    ts.length ≤ acc.length := by
  have := a_foldlM_emit_length ts [] acc h
  simpa using this

theorem a_decode_pop_lit {ts : List Nat} {t : Nat} {inp : List Nat} {p : Nat}
    (hp : p ≤ inp.length) (hd : LZ77.decode (ts ++ [t]) = some (inp.take p)) (ht : t < 256) :
    1 ≤ p ∧ LZ77.decode ts = some (inp.take (p - 1)) := by
  rw [LZ77.decode_snoc] at hd
  cases hts : LZ77.decode ts with
  | none => rw [hts] at hd; simp at hd
  | some acc =>
    rw [hts] at hd
    simp only [Option.bind_some, LZ77.emit, if_pos ht] at hd
    have hacc : acc ++ [t] = inp.take p := Option.some.inj hd
    have hlen : acc.length + 1 = p := by
      have := congrArg List.length hacc
      simp [List.length_take] at this; omega
    refine ⟨by omega, ?_⟩
    apply congrArg some
    have := congrArg (List.take acc.length) hacc
    rw [List.take_append_of_le_length (le_refl _), List.take_length, List.take_take] at this
    rw [this, show min acc.length p = p - 1 by omega]

theorem a_decode_pop_match {ts : List Nat} {t : Nat} {inp : List Nat} {p : Nat}
    (hp : p ≤ inp.length) (hd : LZ77.decode (ts ++ [t]) = some (inp.take p)) (ht : 256 ≤ t) :
    LZ77.tokLen t ≤ p ∧ LZ77.decode ts = some (inp.take (p - LZ77.tokLen t)) := by
  rw [LZ77.decode_snoc] at hd
  cases hts : LZ77.decode ts with
  | none => rw [hts] at hd; simp at hd
  | some acc =>
    rw [hts] at hd
    simp only [Option.bind_some, LZ77.emit, if_neg (show ¬ t < 256 by omega)] at hd
    split at hd
    · split at hd
      · have hacc : LZ77.copyN acc (LZ77.tokDist t) (LZ77.tokLen t) = inp.take p := Option.some.inj hd
        have hlen : acc.length + LZ77.tokLen t = p := by
          have := congrArg List.length hacc
          simp [List.length_take] at this; omega
        refine ⟨by omega, ?_⟩
        apply congrArg some
        have := congrArg (List.take acc.length) hacc
        rw [a_copyN_take_prefix, List.take_take] at this
        rw [this, show min acc.length p = p - LZ77.tokLen t by omega]
      · simp at hd
    · simp at hd

theorem a_toks_pop (out : Slice Std.U32) (nt : Nat) (h0 : 0 < nt) (hle : nt ≤ out.length) :
    toks out nt = toks out (nt - 1) ++ [(out.val[nt - 1]!).val] := by
  have hlt : nt - 1 < out.val.length := by
    have : out.length = out.val.length := rfl
    omega
  simp only [toks]
  conv_lhs => rw [show nt = (nt - 1) + 1 by omega]
  rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append]
  simp [getElem!_pos out.val (nt - 1) hlt]

theorem a_toks_length (out : Slice Std.U32) (nt : Nat) (h : nt ≤ out.length) :
    (toks out nt).length = nt := by
  simp only [toks, List.length_map, List.length_take]
  have : out.length = out.val.length := rfl
  omega

def ADec (s : Slice Std.U8) (out : Slice Std.U32) (nt p : Nat) : Prop :=
  p ≤ s.length ∧ nt ≤ p ∧ s.length ≤ out.length ∧
    LZ77.decode (toks out nt) = some ((bytes s).take p)

theorem ADec.init (input : Slice Std.U8) (out : Slice Std.U32) (h : input.length ≤ out.length) :
    ADec input out (0#usize).val (0#usize).val :=
  ⟨by simp, by simp, h, by simp [toks, LZ77.decode]⟩

theorem ADec.lit {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat} (h : ADec s out nt p)
    (hp : p < s.length) (ntU : Std.Usize) (hnt : ntU.val = nt) (v : Std.U32)
    (hv : v.val = (s.val[p]!).val) :
    ADec s (out.set ntU v) (nt + 1) (p + 1) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  have hntl : ntU.val < out.length := by omega
  refine ⟨by omega, by omega, by rw [Std.Slice.set_length]; exact hso, ?_⟩
  rw [← hnt]
  refine emit_lit s out ntU p v (by rw [hnt]; exact hde) hp hntl ?_
  have hpl : p < s.val.length := hp
  rw [hv, bytes_getElem! s p hpl, getElem!_pos s.val p hpl]

theorem ADec.match {s : Slice Std.U8} {out : Slice Std.U32} {nt p l d : Nat} (h : ADec s out nt p)
    (hm : AMatchAt s p l d) (ntU : Std.Usize) (hnt : ntU.val = nt) (v : Std.U32)
    (hv : v.val = LZ77.mkMatch d l) :
    ADec s (out.set ntU v) (nt + 1) (p + l) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  obtain ⟨h3, h258, hpl, hd1, hd32, hdp, hmm⟩ := hm
  have hntl : ntU.val < out.length := by omega
  refine ⟨by omega, by omega, by rw [Std.Slice.set_length]; exact hso, ?_⟩
  rw [← hnt]
  exact emit_match s out ntU p d l v (by rw [hnt]; exact hde) hntl hd1 hdp hd32 h3 h258 hpl hmm hv

theorem ADec.pop_lit {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat} (h : ADec s out nt p)
    (h0 : 0 < nt) (hle : nt ≤ out.length) (ht : (out.val[nt - 1]!).val < 256) :
    1 ≤ p ∧ ADec s out (nt - 1) (p - 1) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  rw [a_toks_pop out nt h0 hle] at hde
  obtain ⟨hp1, hde'⟩ := a_decode_pop_lit (by simpa using hps) hde ht
  exact ⟨hp1, by omega, by omega, hso, hde'⟩

theorem ADec.pop_match {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat} (h : ADec s out nt p)
    (h0 : 0 < nt) (hle : nt ≤ out.length) (ht : 256 ≤ (out.val[nt - 1]!).val) :
    LZ77.tokLen (out.val[nt - 1]!).val ≤ p ∧
      ADec s out (nt - 1) (p - LZ77.tokLen (out.val[nt - 1]!).val) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  rw [a_toks_pop out nt h0 hle] at hde
  obtain ⟨hw, hde'⟩ := a_decode_pop_match (by simpa using hps) hde ht
  have hlen := a_decode_length_le hde'
  rw [a_toks_length out (nt - 1) (by omega), List.length_take, LZ77.bytes_length] at hlen
  exact ⟨hw, by omega, by omega, hso, hde'⟩

theorem ADec.done {s : Slice Std.U8} {out : Slice Std.U32} {nt p : Nat} (h : ADec s out nt p)
    (hp : s.length ≤ p) : nt ≤ s.length ∧ LZ77.Valid (bytes s) (toks out nt) := by
  obtain ⟨hps, hntp, hso, hde⟩ := h
  refine ⟨by omega, ?_⟩
  unfold LZ77.Valid
  rw [hde, show p = s.length by omega, ← LZ77.bytes_length, List.take_length]

theorem ADec.lit_step {s : Slice Std.U8} {out out1 : Slice Std.U32} {ntU nt1 pU : Std.Usize}
    {b : Std.U8} {v : Std.U32} (h : ADec s out ntU.val pU.val) (hp : pU.val < s.val.length)
    (hb : b = s.val[pU.val]) (hv : v = UScalar.cast .U32 b) (hout1 : out1 = out.set ntU v)
    (hnt1 : nt1.val = ntU.val + 1) :
    nt1.val = ntU.val + 1 ∧ out1.length = out.length ∧ ADec s out1 nt1.val (pU.val + 1) := by
  subst hout1
  refine ⟨hnt1, Std.Slice.set_length .., ?_⟩
  rw [hnt1]
  exact ADec.lit h hp ntU rfl v (by rw [hv, U8.cast_U32_val_eq, hb, getElem!_pos s.val pU.val hp])

@[local step]
theorem a_put_lit_spec (s : Slice Std.U8) (out : Slice Std.U32) (nt p : Std.Usize)
    (hdec : ADec s out nt.val p.val) (hp : p.val < s.length) :
    slot.b_a_put_lit s out nt p ⦃ fun r => r.1.val = nt.val + 1 ∧ r.2.length = out.length ∧
      ADec s r.2 r.1.val (p.val + 1) ⦄ := by
  rw [slot.b_a_put_lit]
  step*
  exact ADec.lit_step hdec (by scalar_tac) (by assumption) (by assumption) (by assumption)
    (by assumption)

theorem ADec.match_step {s : Slice Std.U8} {out out1 : Slice Std.U32} {ntU nt1 pU dU lU e : Std.Usize}
    {v : Std.U32} (h : ADec s out ntU.val pU.val) (hm : AMatchAt s pU.val lU.val dU.val)
    (hout1 : out1 = out.set ntU v) (hv : v.val = LZ77.mkMatch dU.val lU.val)
    (hnt1 : nt1.val = ntU.val + 1) (he : e.val = pU.val + lU.val) :
    nt1.val = ntU.val + 1 ∧ e.val = pU.val + lU.val ∧ out1.length = out.length ∧
      ADec s out1 nt1.val e.val := by
  subst hout1
  refine ⟨hnt1, he, Std.Slice.set_length .., ?_⟩
  rw [hnt1, he]
  exact ADec.match h hm ntU rfl v hv

@[local step]
theorem a_put_match_spec (s : Slice Std.U8) (out : Slice Std.U32) (nt p d l : Std.Usize)
    (hdec : ADec s out nt.val p.val) (hm : AMatchAt s p.val l.val d.val) :
    slot.b_a_put_match s out nt p d l ⦃ fun r => r.1.1.val = nt.val + 1 ∧
      r.1.2.val = p.val + l.val ∧ r.2.length = out.length ∧ ADec s r.2 r.1.1.val r.1.2.val ⦄ := by
  rw [slot.b_a_put_match]
  have hm' := hm
  obtain ⟨h3, h258, hpl, hd1, hd32, hdp, _⟩ := hm'
  step*

  exact ADec.match_step hdec hm (by assumption)
    (by simp only [LZ77.mkMatch, LZ77.MATCH_BASE]; scalar_tac) (by assumption) (by assumption)

theorem AMatchAt.back_lit {s : Slice Std.U8} {p l d : Nat} (h : AMatchAt s p l d) (hl : l < 258)
    (hdp : d < p) (heq : s.val[p - 1]! = s.val[p - 1 - d]!) : AMatchAt s (p - 1) (l + 1) d := by
  obtain ⟨h3, h258, hpl, hd1, hd32, _, hm⟩ := h
  refine ⟨by omega, by omega, by omega, hd1, hd32, by omega, ?_⟩
  intro k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    rw [Nat.add_zero, Nat.add_zero, show p - 1 - d = p - 1 - d by rfl]
    exact heq
  · have := hm (k - 1) (by omega)
    rw [show p - 1 + k = p + (k - 1) by omega, show p - 1 - d + k = p - d + (k - 1) by omega]
    exact this

theorem AMatchAt.back_match {s : Slice Std.U8} {p l d w : Nat} (h : AMatchAt s p l d)
    (hlw : l + w ≤ 258) (hw : w ≤ p) (hdw : d ≤ p - w) (hmw : Matches s (p - w - d) (p - w) w) :
    AMatchAt s (p - w) (l + w) d := by
  obtain ⟨h3, h258, hpl, hd1, hd32, _, hm⟩ := h
  refine ⟨by omega, by omega, by omega, hd1, hd32, hdw, ?_⟩
  intro k hk
  rcases Nat.lt_or_ge k w with hkw | hkw
  · have := hmw k hkw
    rw [show p - w - d = p - w - d by rfl] at this
    exact this
  · have := hm (k - w) (by omega)
    rw [show p - w + k = p + (k - w) by omega, show p - w - d + k = p - d + (k - w) by omega]
    exact this

def ABackInv (input : Slice Std.U8) (L d E P0 : Nat) (out : Slice Std.U32) (nt p l : Nat) : Prop :=
  ADec input out nt p ∧ out.length = L ∧ AMatchAt input p l d ∧ p + l = E ∧ p ≤ P0

theorem ABackInv.lit {input : Slice Std.U8} {out : Slice Std.U32} {L d E P0 : Nat}
    {nt p l i1 i2 i4 l1 : Std.Usize} {t : Std.U32} {x y : Std.U8}
    (h : ABackInv input L d E P0 out nt.val p.val l.val)
    (hi1 : i1.val = nt.val - 1) (hntl : nt.val ≤ out.length) (hnt0 : 1 ≤ nt.val)
    (hi1l : i1.val < out.val.length) (ht : t = out.val[i1.val]) (ht256 : t < 256#u32)
    (hi2 : i2.val = p.val - 1) (hi2l : i2.val < input.val.length) (hx : x = input.val[i2.val])
    (hxy : x = y) (hi4 : i4.val = i2.val - d) (hi4l : i4.val < input.val.length)
    (hy : y = input.val[i4.val]) (hl : l.val < 258) (hdp : d < p.val)
    (hl1 : l1.val = l.val + 1) :
    ABackInv input L d E P0 out i1.val i2.val l1.val := by
  obtain ⟨hdec, hL, hm, hE, hP⟩ := h
  have ht' : (out.val[nt.val - 1]!).val < 256 := by
    rw [← hi1, getElem!_pos out.val i1.val hi1l, ← ht]; scalar_tac
  obtain ⟨hp1, hdec'⟩ := ADec.pop_lit hdec (by omega) hntl ht'
  have heq : input.val[p.val - 1]! = input.val[p.val - 1 - d]! := by
    rw [← hi2, getElem!_pos input.val i2.val hi2l, show i2.val - d = i4.val by omega,
      getElem!_pos input.val i4.val hi4l, ← hx, ← hy, hxy]
  have hm' := AMatchAt.back_lit hm hl hdp heq
  rw [hi1, hi2, hl1]
  exact ⟨hdec', hL, hm', by omega, by omega⟩

theorem ABackInv.match {input : Slice Std.U8} {out : Slice Std.U32} {L d E P0 : Nat}
    {nt p l i1 w i9 i10 i11 i12 : Std.Usize} {t : Std.U32}
    (h : ABackInv input L d E P0 out nt.val p.val l.val)
    (hi1 : i1.val = nt.val - 1) (hntl : nt.val ≤ out.length) (hnt0 : 1 ≤ nt.val)
    (hi1l : i1.val < out.val.length) (ht : t = out.val[i1.val])
    (hsame : i12.val = 1 → Matches input i11.val i10.val w.val) (hi12 : i12 = 1#usize)
    (ht24 : 16777216 ≤ t.val) (hwv : w.val = (t.val - 16777216) % 256 + 3)
    (hi9 : i9.val = l.val + w.val) (hi9' : i9.val ≤ 258) (hi10 : i10.val = p.val - w.val)
    (hwp : w.val ≤ p.val) (hdw : d ≤ i10.val) (hi11 : i11.val = i10.val - d) :
    ABackInv input L d E P0 out i1.val i10.val i9.val := by
  obtain ⟨hdec, hL, hm, hE, hP⟩ := h
  have htv : (out.val[nt.val - 1]!).val = t.val := by
    rw [← hi1, getElem!_pos out.val i1.val hi1l, ← ht]
  have hwv' : w.val = LZ77.tokLen (out.val[nt.val - 1]!).val := by
    rw [htv, hwv]
    simp only [LZ77.tokLen, LZ77.MATCH_BASE]
  obtain ⟨hwl, hdec'⟩ := ADec.pop_match hdec (by omega) hntl (by omega)
  rw [← hwv'] at hdec'
  have hmw : Matches input (p.val - w.val - d) (p.val - w.val) w.val := by
    have := hsame (by rw [hi12]; rfl)
    rw [hi11, hi10] at this
    exact this
  have hm' := AMatchAt.back_match hm (by omega) hwp (by omega) hmw
  rw [hi1, hi10, hi9]
  exact ⟨hdec', hL, hm', by omega, by omega⟩

theorem ABackInv.part {input : Slice Std.U8} {out out1 : Slice Std.U32} {L d E P0 : Nat}
    {nt p l : Nat} {p1 l1 : Std.Usize} (h : ABackInv input L d E P0 out nt p l)
    (hlen : out1.length = out.length) (hdec : ADec input out1 nt p1.val)
    (hm : AMatchAt input p1.val l1.val d) (hE : p1.val + l1.val = p + l) (hp : p1.val ≤ p) :
    ABackInv input L d E P0 out1 nt p1.val l1.val := by
  obtain ⟨_, hL, _, hE0, hP⟩ := h
  exact ⟨hdec, by rw [hlen, hL], hm, by omega, by omega⟩

theorem ABackInv.lit_step {input : Slice Std.U8} {out : Slice Std.U32} {L E P0 : Nat}
    {nt p l d back i1 i2 i4 l1 back1 : Std.Usize} {t : Std.U32} {x y : Std.U8}
    (h : ABackInv input L d.val E P0 out nt.val p.val l.val)
    (hbk : back < slot.B_A_BACKTOK) (hntl : nt ≤ Std.Slice.len out) (hl : l < 258#usize) (hdp : d < p)
    (hi1 : i1.val = nt.val - 1) (hnt0 : 1 ≤ nt.val) {hb1 : i1.val < out.val.length}
    (ht : t = out.val[i1.val]'hb1) (ht256 : t < 256#u32)
    (hi2 : i2.val = p.val - 1) {hb2 : i2.val < input.val.length} (hx : x = input.val[i2.val]'hb2)
    (hi4 : i4.val = i2.val - d.val) {hb4 : i4.val < input.val.length}
    (hy : y = input.val[i4.val]'hb4) (hxy : x = y)
    (hl1 : l1.val = l.val + 1) (hb1' : back1.val = back.val + 1) :
    ABackInv input L d.val E P0 out i1.val i2.val l1.val ∧
      slot.B_A_BACKTOK.val - back1.val < slot.B_A_BACKTOK.val - back.val :=
  ⟨ABackInv.lit h hi1 (by scalar_tac) hnt0 hb1 ht ht256 hi2 hb2 hx hxy hi4 hb4 hy
    (by scalar_tac) (by scalar_tac) hl1, by scalar_tac⟩

theorem ABackInv.match_step {input : Slice Std.U8} {out : Slice Std.U32} {L E P0 : Nat}
    {nt p l d back i1 w i9 i10 i11 i12 back1 : Std.Usize} {t i6 i7 i8 : Std.U32}
    (h : ABackInv input L d.val E P0 out nt.val p.val l.val)
    (hbk : back < slot.B_A_BACKTOK) (hntl : nt ≤ Std.Slice.len out)
    (hi1 : i1.val = nt.val - 1) (hnt0 : 1 ≤ nt.val) {hb1 : i1.val < out.val.length}
    (ht : t = out.val[i1.val]'hb1) (hi6 : i6.val = t.val - 16777216) (ht24 : 16777216 ≤ t.val)
    (hi7 : i7.val = i6.val % 256) (hi8 : i8.val = i7.val + 3) (hw : w = UScalar.cast .Usize i8)
    (hi9 : i9.val = l.val + w.val) (hi9' : i9 ≤ 258#usize) (hi10 : i10.val = p.val - w.val)
    (hwp : w.val ≤ p.val) (hdw : d ≤ i10) (hi11 : i11.val = i10.val - d.val)
    (hsame : i12.val = 1 → Matches input i11.val i10.val w.val) (hi12 : i12 = 1#usize)
    (hb1' : back1.val = back.val + 1) :
    ABackInv input L d.val E P0 out i1.val i10.val i9.val ∧
      slot.B_A_BACKTOK.val - back1.val < slot.B_A_BACKTOK.val - back.val := by
  have hwv : w.val = (t.val - 16777216) % 256 + 3 := by rw [hw]; scalar_tac
  exact ⟨ABackInv.match h hi1 (by scalar_tac) hnt0 hb1 ht hsame hi12 ht24 hwv hi9 (by scalar_tac)
    hi10 hwp (by scalar_tac) hi11, by scalar_tac⟩

theorem ABackInv.part_step {input : Slice Std.U8} {out out1 : Slice Std.U32} {L E P0 : Nat}
    {nt p l d back p1 l1 : Std.Usize} (h : ABackInv input L d.val E P0 out nt.val p.val l.val)
    (hbk : back < slot.B_A_BACKTOK) (hlen : out1.length = out.length)
    (hdec : ADec input out1 nt.val p1.val) (hm : AMatchAt input p1.val l1.val d.val)
    (hE : p1.val + l1.val = p.val + l.val) (hp : p1.val ≤ p.val) :
    ABackInv input L d.val E P0 out1 nt.val p1.val l1.val ∧
      slot.B_A_BACKTOK.val - slot.B_A_BACKTOK.val < slot.B_A_BACKTOK.val - back.val :=
  ⟨ABackInv.part h hlen hdec hm hE hp, by scalar_tac⟩

theorem Matches.a_cons {input : Slice Std.U8} {a b n : Nat} (h : Matches input (a + 1) (b + 1) n)
    (heq : input.val[b]! = input.val[a]!) : Matches input a b (n + 1) := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with h0 | hk0
  · subst h0; simpa using heq
  · have := h (k - 1) (by omega)
    rw [show b + 1 + (k - 1) = b + k by omega, show a + 1 + (k - 1) = a + k by omega] at this
    exact this

theorem Matches.a_append {input : Slice Std.U8} {a b k l : Nat} (h1 : Matches input a b k)
    (h2 : Matches input (a + k) (b + k) l) : Matches input a b (k + l) := by
  intro j hj
  rcases Nat.lt_or_ge j k with hjk | hjk
  · exact h1 j hjk
  · have := h2 (j - k) (by omega)
    rw [show b + k + (j - k) = b + j by omega, show a + k + (j - k) = a + j by omega] at this
    exact this

theorem AMatchAt.back_part {s : Slice Std.U8} {p l d k : Nat} (h : AMatchAt s p l d)
    (hmk : Matches s (p - k - d) (p - k) k) (hlk : l + k ≤ 258) (hdk : d + k ≤ p) :
    AMatchAt s (p - k) (l + k) d := by
  obtain ⟨h3, h258, hpl, hd1, hd32, _, hm⟩ := h
  refine ⟨by omega, hlk, by omega, hd1, hd32, by omega, ?_⟩
  have hm' : Matches s (p - k - d + k) (p - k + k) l := by
    rw [show p - k - d + k = p - d by omega, show p - k + k = p by omega]; exact hm
  have := Matches.a_append hmk hm'
  rw [show k + l = l + k by omega] at this
  exact this

theorem Matches.a_back_step {input : Slice Std.U8} {p d k : Nat} {i4 i7 k1 : Std.Usize}
    {x y : Std.U8} (h : Matches input (p - k - d) (p - k) k) (hdk : d + k < p)
    (hi4 : i4.val = p - 1 - k) (hi4l : i4.val < input.val.length) (hx : x = input.val[i4.val])
    (hi7 : i7.val = p - 1 - k - d) (hi7l : i7.val < input.val.length)
    (hy : y = input.val[i7.val]) (hxy : x = y) (hk1 : k1.val = k + 1) :
    Matches input (p - k1.val - d) (p - k1.val) k1.val := by
  rw [hk1]
  apply Matches.a_cons
  · rw [show p - (k + 1) - d + 1 = p - k - d by omega, show p - (k + 1) + 1 = p - k by omega]
    exact h
  · rw [show p - (k + 1) - d = i7.val by omega, show p - (k + 1) = i4.val by omega,
      getElem!_pos input.val i4.val hi4l, getElem!_pos input.val i7.val hi7l, ← hx, ← hy, hxy]

theorem a_part_merge_loop_spec (input : Slice Std.U8) (p0 l0 d w k : Std.Usize)
    (hp0 : p0.val ≤ input.length) (hkw : k.val ≤ w.val) (hl0 : l0.val + k.val ≤ 258)
    (hdk : d.val + k.val ≤ p0.val)
    (hm : Matches input (p0.val - k.val - d.val) (p0.val - k.val) k.val) :
    slot.b_a_part_merge_loop input p0 l0 d w k ⦃ fun r =>
      r.val ≤ w.val ∧ l0.val + r.val ≤ 258 ∧ d.val + r.val ≤ p0.val ∧
      Matches input (p0.val - r.val - d.val) (p0.val - r.val) r.val ⦄ := by
  rw [slot.b_a_part_merge_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun r => w.val - r.val)
    (inv := fun r => r.val ≤ w.val ∧ l0.val + r.val ≤ 258 ∧ d.val + r.val ≤ p0.val ∧
      Matches input (p0.val - r.val - d.val) (p0.val - r.val) r.val)
  · rintro k ⟨hkw, hl0, hdk, hm⟩
    simp only [slot.b_a_part_merge_loop.body]
    step*
    all_goals first
      | exact ⟨hkw, hl0, hdk, hm⟩
      | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
          Matches.a_back_step (i4 := i4) (i7 := i7) (x := i5) (y := i8) hm (by scalar_tac)
            (by scalar_tac) (by scalar_tac) (by assumption) (by scalar_tac) (by scalar_tac)
            (by assumption) (by assumption) (by scalar_tac),
          by scalar_tac⟩)
  · exact ⟨hkw, hl0, hdk, hm⟩

@[local step]
theorem a_part_merge_loop_spec0 (input : Slice Std.U8) (p0 l0 d w : Std.Usize)
    (hp0 : p0.val ≤ input.length) (hl0 : l0.val ≤ 258) (hdk : d.val ≤ p0.val) :
    slot.b_a_part_merge_loop input p0 l0 d w 0#usize ⦃ fun r =>
      r.val ≤ w.val ∧ l0.val + r.val ≤ 258 ∧ d.val + r.val ≤ p0.val ∧
      Matches input (p0.val - r.val - d.val) (p0.val - r.val) r.val ⦄ :=
  a_part_merge_loop_spec input p0 l0 d w 0#usize hp0 (by simp) (by simpa using hl0)
    (by simpa using hdk) (by simpa using LZ77.Matches.zero input (p0.val - d.val) p0.val)

theorem a_part_post {input : Slice Std.U8} {out out1 : Slice Std.U32}
    {nt p l d w k c nl pp p1 l1 : Nat} {ntU : Std.Usize} {v : Std.U32}
    (hdec : ADec input out nt p) (hm : AMatchAt input p l d)
    (hnt0 : 1 ≤ nt) (hntl : nt ≤ out.length) (ht24 : 256 ≤ (out.val[nt - 1]!).val)
    (hw : w = LZ77.tokLen (out.val[nt - 1]!).val)
    (hmk : Matches input (p - k - d) (p - k) k) (hc : ANear input pp nl c)
    (hout1 : out1 = out.set ntU v)
    (hlk : l + k ≤ 258) (hdk : d + k ≤ p) (hk : k ≤ w) (hpp : pp = p - w) (hnl : nl = w - k)
    (hnl3 : 3 ≤ nl) (hnl258 : nl ≤ 258) (hc0 : 0 < c) (hcp : c ≤ pp)
    (hntU : ntU.val = nt - 1) (hv : v.val = LZ77.mkMatch c nl) (hp1 : p1 = p - k)
    (hl1 : l1 = l + k) :
    out1.length = out.length ∧ ADec input out1 nt p1 ∧ AMatchAt input p1 l1 d ∧
      p1 + l1 = p + l ∧ p1 ≤ p := by
  subst hp1 hl1 hpp
  obtain ⟨hwp, hdec'⟩ := ADec.pop_match hdec (by omega) hntl ht24
  rw [← hw] at hdec' hwp
  have hpn : p ≤ input.length := hdec.1
  have hmc : AMatchAt input (p - w) nl c := by
    rcases hc with h0 | ⟨hc1, hc32, _, hmm⟩
    · omega
    · exact ⟨hnl3, hnl258, by omega, hc1, hc32, hcp, hmm⟩
  have hd2 := ADec.match hdec' hmc ntU hntU v hv
  rw [show nt - 1 + 1 = nt by omega, show p - w + nl = p - k by omega, ← hout1] at hd2
  refine ⟨by rw [hout1, Std.Slice.set_length], hd2, AMatchAt.back_part hm hmk hlk hdk,
    by omega, by omega⟩

@[local step]
theorem a_part_merge_spec {W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (prev : Array Std.U32 W) (nt p l d : Std.Usize) (t : Std.U32) (w «partial» : Std.Usize)
    (hdec : ADec input out nt.val p.val) (hm : AMatchAt input p.val l.val d.val)
    (hp8 : p.val + 8 ≤ input.length) (hnt0 : 1 ≤ nt.val) (hntl : nt.val ≤ out.length)
    (ht : (out.val[nt.val - 1]!).val = t.val) (ht24 : 16777216 ≤ t.val)
    (hw : w.val = (t.val - 16777216) % 256 + 3) (hW : 0 < W.val) :
    slot.b_a_part_merge input out prev nt p l d t w «partial» ⦃ fun r =>
      r.2.length = out.length ∧ ADec input r.2 nt.val r.1.1.val ∧
      AMatchAt input r.1.1.val r.1.2.val d.val ∧ r.1.1.val + r.1.2.val = p.val + l.val ∧
      r.1.1.val ≤ p.val ⦄ := by
  rw [slot.b_a_part_merge]
  have hm' := hm
  obtain ⟨h3, h258, hpl, hd1, hd32, hdp, _⟩ := hm'
  have hwt : w.val = LZ77.tokLen (out.val[nt.val - 1]!).val := by
    rw [ht, hw]; simp only [LZ77.tokLen, LZ77.MATCH_BASE]
  have ht256 : 256 ≤ (out.val[nt.val - 1]!).val := by rw [ht]; omega
  step*
  all_goals first
    | exact ⟨rfl, hdec, hm, rfl, le_refl _⟩
    | exact a_part_post hdec hm hnt0 hntl ht256 hwt (by assumption) (by assumption)
        (by assumption) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by scalar_tac) (by omega) (by scalar_tac) (by omega)
        (by simp only [LZ77.mkMatch, LZ77.MATCH_BASE]; scalar_tac) (by omega) (by omega)

def ALazyInv (input : Slice Std.U8) (L lim : Nat) (out : Slice Std.U32) (nt p : Nat)
    {N : Std.Usize} (head : Array Std.U32 N) (ins l d : Nat) : Prop :=
  ADec input out nt p ∧ out.length = L ∧ AMatchAt input p l d ∧ AHeadBound head (p + 2) ∧
    p < lim ∧ ins ≤ p + 3

theorem ALazyInv.accept {input : Slice Std.U8} {L lim p' B : Nat} {out1 : Slice Std.U32}
    {nt1 i ins1 l1 d1 minl : Std.Usize} {N : Std.Usize} {head1 : Array Std.U32 N}
    (hdec : ADec input out1 nt1.val p') (hi : i.val = p') (hlen : out1.length = L)
    (hf : AFoundAt input i.val l1.val d1.val) (hl1 : minl.val ≤ l1.val) (hminl : 3 ≤ minl.val)
    (hB : AHeadBound head1 B) (hBi : B ≤ i.val + 2) (hilim : i.val < lim)
    (hins : ins1.val ≤ i.val + 3) :
    ALazyInv input L lim out1 nt1.val i.val head1 ins1.val l1.val d1.val := by
  subst hi
  refine ⟨hdec, hlen, ?_, AHeadBound.mono hB hBi, hilim, hins⟩
  rcases hf with h | h
  · omega
  · exact h

theorem ALazyInv.reject {input : Slice Std.U8} {L lim : Nat} {out : Slice Std.U32}
    {nt p ins ins1 l d B : Nat} {N : Std.Usize} {head head1 : Array Std.U32 N}
    (h : ALazyInv input L lim out nt p head ins l d) (hB : AHeadBound head1 B) (hBp : B ≤ p + 2)
    (hins1 : ins1 ≤ p + 3) : ALazyInv input L lim out nt p head1 ins1 l d := by
  obtain ⟨hdec, hlen, hm, _, hplim, _⟩ := h
  exact ⟨hdec, hlen, hm, AHeadBound.mono hB hBp, hplim, hins1⟩

theorem ALazyInv.accept_step {input : Slice Std.U8} {L : Nat} {lim : Std.Usize}
    {out out1 : Slice Std.U32} {nt p ins l d nt1 i ins1 l1 d1 minl : Std.Usize} {B q : Nat}
    {N : Std.Usize} {head head1 : Array Std.U32 N}
    (h : ALazyInv input L lim.val out nt.val p.val head ins.val l.val d.val)
    (hminl : 3 ≤ minl.val) (hilim : i < lim) (hf : AFoundAt input i.val l1.val d1.val)
    (hl1 : l1 ≥ minl) (hB : AHeadBound head1 B) (hBi : B ≤ i.val + 2) (hpi : p.val < i.val)
    (hins1 : ins1.val ≤ i.val + 3) (hlen : out1.length = out.length)
    (hdec : ADec input out1 nt1.val q) (hq : q = i.val) :
    ALazyInv input L lim.val out1 nt1.val i.val head1 ins1.val l1.val d1.val ∧
      lim.val - i.val + (1#u32 : Std.U32).val < lim.val - p.val + (1#u32 : Std.U32).val := by
  obtain ⟨_, hL, _, _, _, _⟩ := h
  exact ⟨ALazyInv.accept hdec hq.symm (by rw [hlen, hL]) hf (by scalar_tac) hminl hB hBi
    (by scalar_tac) hins1, by scalar_tac⟩

theorem ALazyInv.reject_step {input : Slice Std.U8} {L : Nat} {lim : Std.Usize}
    {out : Slice Std.U32} {nt p ins l d ins1 : Std.Usize} {B : Nat}
    {N : Std.Usize} {head head1 : Array Std.U32 N}
    (h : ALazyInv input L lim.val out nt.val p.val head ins.val l.val d.val)
    (hB : AHeadBound head1 B) (hBp : B ≤ p.val + 2) (hins1 : ins1.val ≤ p.val + 3) :
    ALazyInv input L lim.val out nt.val p.val head1 ins1.val l.val d.val ∧
      lim.val - p.val + (0#u32 : Std.U32).val < lim.val - p.val + (1#u32 : Std.U32).val := by
  refine ⟨ALazyInv.reject h hB hBp hins1, by simp⟩

theorem ADec.cast {s : Slice Std.U8} {out : Slice Std.U32} {nt p p' : Nat} (h : ADec s out nt p)
    (hp : p' = p) : ADec s out nt p' := by
  subst hp; exact h

theorem a_lazy_loop_inv {H W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p : Std.Usize) (mask : Std.U32) (minl l2d lazy nice ldep : Std.Usize) (hlit : Std.I32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins l d : Std.Usize) (gain : Std.I32) (go : Std.U32)
    (L : Nat) (hlim : lim.val + 8 = input.length)
    (hminl : 3 ≤ minl.val) (hminl8 : minl.val ≤ 8) (hH : 0 < H.val) (hW : 0 < W.val)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000)
    (hinv : ALazyInv input L lim.val out nt.val p.val head ins.val l.val d.val) :
    slot.b_a_run_loop0_loop1 input out nt p mask minl l2d lazy nice ldep hlit head prev lim ins l d gain go
      ⦃ fun r => ALazyInv input L lim.val r.1 r.2.1.val r.2.2.1.val r.2.2.2.1
        r.2.2.2.2.2.1.val r.2.2.2.2.2.2.1.val r.2.2.2.2.2.2.2.val ⦄ := by
  rw [slot.b_a_run_loop0_loop1]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  have ⟨hL0, hL1⟩ := a_L2B_bound
  apply Std.loop.spec_decr_nat
    (measure := fun r => lim.val - r.2.2.1.val + r.2.2.2.2.2.2.2.2.2.val)
    (inv := fun r => ALazyInv input L lim.val r.1 r.2.1.val r.2.2.1.val r.2.2.2.1
      r.2.2.2.2.2.1.val r.2.2.2.2.2.2.1.val r.2.2.2.2.2.2.2.1.val)
  · clear hinv
    rintro ⟨out, nt, p, head, prev, ins, l, d, gain, go⟩ hinv
    simp only at hinv
    have hinv' := hinv
    obtain ⟨hdec, hL, hm, hB, hplim, hins⟩ := hinv'
    have hdec' := hdec
    have hm' := hm
    obtain ⟨hps, hntp, hso, -⟩ := hdec'
    obtain ⟨h3, h258, hpl, hd1, hd32, hdp, -⟩ := hm'
    simp only [slot.b_a_run_loop0_loop1.body]
    step*

    apply WP.spec_bind (Pₘ := fun (h : Std.Usize) => h.val + 1 ≤ l.val)
    · split
      · step*
      · simp only [Std.WP.spec_ok]; scalar_tac
    intro «have» hhave
    step*
    all_goals first
      | exact ALazyInv.reject_step hinv (by assumption) (by omega) (by omega)
      | exact ALazyInv.accept_step hinv hminl (by assumption) (by assumption) (by assumption)
          (by assumption) (by omega) (by omega) (by omega) (by omega) (by assumption) (by omega)
      | exact ADec.cast (by assumption) (by scalar_tac)
  · exact hinv

@[local step]
theorem a_lazy_loop_spec {H W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p : Std.Usize) (mask : Std.U32) (minl l2d lazy nice ldep : Std.Usize) (hlit : Std.I32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins l d : Std.Usize) (gain : Std.I32) (go : Std.U32)
    (L : Nat) (hlim : lim.val + 8 = input.length)
    (hminl : 3 ≤ minl.val) (hminl8 : minl.val ≤ 8) (hH : 0 < H.val) (hW : 0 < W.val)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000)
    (hdec : ADec input out nt.val p.val) (hlen : out.length = L)
    (hm : AMatchAt input p.val l.val d.val) (hB : AHeadBound head (p.val + 2))
    (hplim : p.val < lim.val) (hins : ins.val ≤ p.val + 3) :
    slot.b_a_run_loop0_loop1 input out nt p mask minl l2d lazy nice ldep hlit head prev lim ins l d gain go
      ⦃ fun r =>
      ADec input r.1 r.2.1.val r.2.2.1.val ∧ r.1.length = L ∧
      AMatchAt input r.2.2.1.val r.2.2.2.2.2.2.1.val r.2.2.2.2.2.2.2.val ∧
      AHeadBound r.2.2.2.1 (r.2.2.1.val + r.2.2.2.2.2.2.1.val) ∧ r.2.2.1.val < lim.val ∧
      r.2.2.2.2.2.1.val ≤ r.2.2.1.val + 3 ∧ 3 ≤ r.2.2.2.2.2.2.1.val ⦄ := by
  apply Std.WP.spec_mono (a_lazy_loop_inv input out nt p mask minl l2d lazy nice ldep hlit head prev
    lim ins l d gain go L hlim hminl hminl8 hH hW hh0 hh1 ⟨hdec, hlen, hm, hB, hplim, hins⟩)
  rintro ⟨out', nt', p', head', prev', ins', l', d'⟩ ⟨hdec', hlen', hm', hB', hplim', hins'⟩
  exact ⟨hdec', hlen', hm', AHeadBound.mono hB' (by have := hm'.1; omega), hplim', hins', hm'.1⟩

theorem a_idx_bang {out : Slice Std.U32} {nt i1 : Std.Usize} {t : Std.U32}
    (hi1 : i1.val = nt.val - 1) (hl : i1.val < out.val.length) (ht : t = out.val[i1.val]) :
    (out.val[nt.val - 1]!).val = t.val := by
  rw [← hi1, getElem!_pos out.val i1.val hl, ← ht]

theorem a_idx_step {out : Slice Std.U32} {nt i1 : Std.Usize} {t : Std.U32}
    (hi1 : i1.val = nt.val - 1) {hb : i1.val < out.val.length} (ht : t = out.val[i1.val]'hb) :
    (out.val[nt.val - 1]!).val = t.val :=
  a_idx_bang hi1 hb ht

theorem a_back_loop_inv {W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p «partial» : Std.Usize) (prev : Array Std.U32 W) (l d back : Std.Usize) (L E P0 : Nat)
    (hP0 : P0 + 8 ≤ input.length) (hW : 0 < W.val)
    (hinv : ABackInv input L d.val E P0 out nt.val p.val l.val) :
    slot.b_a_run_loop0_loop2 input out nt p «partial» prev l d back ⦃ fun r =>
      ABackInv input L d.val E P0 r.1 r.2.1.val r.2.2.1.val r.2.2.2.val ⦄ := by
  rw [slot.b_a_run_loop0_loop2]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.loop.spec_decr_nat
    (measure := fun r => slot.B_A_BACKTOK.val - r.2.2.2.2.val)
    (inv := fun r => ABackInv input L d.val E P0 r.1 r.2.1.val r.2.2.1.val r.2.2.2.1.val)
  · rintro ⟨out, nt, p, l, back⟩ hinv
    simp only at hinv
    have hinv' := hinv
    obtain ⟨hdec, hL, hm, hE, hp0⟩ := hinv'
    have hdec' := hdec
    have hm' := hm
    obtain ⟨hps, hntp, hso, _⟩ := hdec'
    obtain ⟨h3, h258, hpl, hd1, hd32, hdp, _⟩ := hm'
    simp only [slot.b_a_run_loop0_loop2.body]
    step*
    all_goals first
      | exact a_idx_step (by assumption) (by assumption)
      | exact ABackInv.part_step hinv (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption)
      | exact ABackInv.lit_step (t := t) (x := i3) (y := i5) (i4 := i4) hinv (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | exact ABackInv.match_step (t := t) (i6 := i6) (i7 := i7) (i8 := i8) (w := w) (i11 := i11)
          (i12 := i12) hinv (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      | exact ⟨hinv, by scalar_tac⟩
      | (exfalso; scalar_tac)
  · exact hinv

@[local step]
theorem a_back_loop_spec {W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p «partial» : Std.Usize) (prev : Array Std.U32 W) (l d back : Std.Usize)
    (hp8 : p.val + 8 ≤ input.length) (hW : 0 < W.val) (hdec : ADec input out nt.val p.val)
    (hm : AMatchAt input p.val l.val d.val) :
    slot.b_a_run_loop0_loop2 input out nt p «partial» prev l d back ⦃ fun r =>
      ADec input r.1 r.2.1.val r.2.2.1.val ∧ r.1.length = out.length ∧
      AMatchAt input r.2.2.1.val r.2.2.2.val d.val ∧
      r.2.2.1.val + r.2.2.2.val = p.val + l.val ∧ r.2.2.1.val ≤ p.val ⦄ := by
  apply Std.WP.spec_mono (a_back_loop_inv input out nt p «partial» prev l d back out.length (p.val + l.val)
    p.val hp8 hW ⟨hdec, rfl, hm, rfl, le_refl _⟩)
  intro r h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem a_sat_add_val (x y : Std.Usize) :
    (core.num.Usize.saturating_add x y).val = min Std.Usize.max (x.val + y.val) := by
  have hsz : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    rw [Std.Usize.max_def, Std.Usize.numBits]
    have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    omega
  show (BitVec.ofNat _ (min (UScalar.max UScalarTy.Usize) (x.val + y.val))).toNat = _
  rw [BitVec.toNat_ofNat, UScalar.max_USize_eq, Nat.mod_eq_of_lt (by omega)]

theorem a_sat_add_spec (x y : Std.Usize) :
    lift (core.num.Usize.saturating_add x y) ⦃ fun r =>
      r.val = x.val + y.val ∨ (r.val = Std.Usize.max ∧ Std.Usize.max < x.val + y.val) ⦄ := by
  simp only [lift, Std.WP.spec_ok]
  rw [a_sat_add_val]
  omega

theorem a_sat_sub_val (x y : Std.Usize) :
    (core.num.Usize.saturating_sub x y).val = x.val - y.val := by
  have hx := x.hBounds
  show (BitVec.ofNat _ (max 0 (x.val - y.val))).toNat = x.val - y.val
  rw [BitVec.toNat_ofNat, Nat.zero_max]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hx)

theorem a_sat_sub_spec (x y : Std.Usize) :
    lift (core.num.Usize.saturating_sub x y) ⦃ fun r => r.val = x.val - y.val ⦄ := by
  simp only [lift, Std.WP.spec_ok]
  exact a_sat_sub_val x y

theorem a_tail_sub_ok {ins e t i : Std.Usize} (hi : i = core.num.Usize.wrapping_add ins t)
    (hlt : i < e) (hie : ins.val ≤ e.val) (ht : t.val ≤ 2147483648) : t.val ≤ e.val := by
  have hsz : 4294967296 ≤ Usize.size := by scalar_tac
  have hil : i.val < e.val := by scalar_tac
  have hel : e.val < Usize.size := by scalar_tac
  rw [hi, core.num.Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize] at hil
  by_cases hw : ins.val + t.val < Usize.size
  · rw [Nat.mod_eq_of_lt hw] at hil; omega
  · omega

theorem a_tail_ite_spec {ins e t i : Std.Usize} (hi : i = core.num.Usize.wrapping_add ins t)
    (hie : ins.val ≤ e.val) (ht : t.val ≤ 2147483648) :
    (if i < e then e - t else ok ins) ⦃ fun _ => True ⦄ := by
  split
  · have := a_tail_sub_ok hi (by assumption) hie ht
    step*
  · simp only [Std.WP.spec_ok]

@[local step]
theorem a_ins_loop0_spec {H W : Std.Usize} (input : Slice Std.U8) (p : Std.Usize) (mask : Std.U32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (ins : Std.Usize) (B : Nat)
    (hB : AHeadBound head B) (hpB : p.val < B + 1) (hp4 : p.val + 4 ≤ Std.Usize.max)
    (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_loop0_loop0 input p mask head prev ins ⦃ fun r => AHeadBound r.1 B ⦄ := by
  rw [slot.b_a_run_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun r => p.val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B)
  · rintro ⟨head, prev, ins⟩ hB
    simp only at hB
    simp only [slot.b_a_run_loop0_loop0.body]
    step*
  · exact hB

@[local step]
theorem a_ins_loop3_spec {H W : Std.Usize} (input : Slice Std.U8) (mask : Std.U32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (ins stop : Std.Usize) (B : Nat)
    (hB : AHeadBound head B) (hsB : stop.val < B + 1) (hs4 : stop.val + 4 ≤ Std.Usize.max)
    (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_loop0_loop3 input mask head prev ins stop ⦃ fun r =>
      AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ stop.val) ⦄ := by
  rw [slot.b_a_run_loop0_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun r => stop.val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ stop.val))
  · rintro ⟨head, prev, ins'⟩ ⟨hB, hins⟩
    simp only at hB hins
    simp only [slot.b_a_run_loop0_loop3.body]
    step*
  · exact ⟨hB, Or.inl (le_refl _)⟩

@[local step]
theorem a_stride_loop_spec {H W : Std.Usize} (input : Slice Std.U8) (mask : Std.U32)
    (stride : Std.Usize) (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins e2 : Std.Usize)
    (B : Nat) (hB : AHeadBound head B) (heB : e2.val < B + 1) (hl4 : lim.val + 4 ≤ Std.Usize.max)
    (hH : 0 < H.val) (hW : 0 < W.val) (hS : 0 < stride.val)
    (hS2 : e2.val + stride.val ≤ Std.Usize.max) :
    slot.b_a_run_loop0_loop4 input mask stride head prev lim ins e2 ⦃ fun r =>
      AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ (0 < e2.val ∧ r.2.2.val < e2.val + stride.val)) ⦄ := by
  rw [slot.b_a_run_loop0_loop4]
  apply Std.loop.spec_decr_nat
    (measure := fun r => e2.val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B ∧
      (r.2.2.val ≤ ins.val ∨ (0 < e2.val ∧ r.2.2.val < e2.val + stride.val)))
  · rintro ⟨head, prev, ins'⟩ ⟨hB, hins⟩
    simp only at hB hins
    simp only [slot.b_a_run_loop0_loop4.body]
    step*
    all_goals first
      | exact ⟨hB, hins⟩
      | exact ⟨by assumption, by scalar_tac, by scalar_tac⟩
  · exact ⟨hB, Or.inl (le_refl _)⟩

@[local step]
theorem a_ins_loop5_spec {H W : Std.Usize} (input : Slice Std.U8) (mask : Std.U32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins «end» : Std.Usize) (B : Nat)
    (hB : AHeadBound head B) (heB : «end».val < B + 1) (hl4 : lim.val + 4 ≤ Std.Usize.max)
    (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_loop0_loop5 input mask head prev lim ins «end» ⦃ fun r =>
      AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ «end».val) ⦄ := by
  rw [slot.b_a_run_loop0_loop5]
  apply Std.loop.spec_decr_nat
    (measure := fun r => «end».val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ «end».val))
  · rintro ⟨head, prev, ins'⟩ ⟨hB, hins⟩
    simp only at hB hins
    simp only [slot.b_a_run_loop0_loop5.body]
    step*
  · exact ⟨hB, Or.inl (le_refl _)⟩

@[local step]
theorem a_ins_loop6_spec {H W : Std.Usize} (input : Slice Std.U8) (mask : Std.U32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins «end» : Std.Usize) (B : Nat)
    (hB : AHeadBound head B) (heB : «end».val < B + 1) (hl4 : lim.val + 4 ≤ Std.Usize.max)
    (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_loop0_loop6 input mask head prev lim ins «end» ⦃ fun r =>
      AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ «end».val) ⦄ := by
  rw [slot.b_a_run_loop0_loop6]
  apply Std.loop.spec_decr_nat
    (measure := fun r => «end».val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ «end».val))
  · rintro ⟨head, prev, ins'⟩ ⟨hB, hins⟩
    simp only at hB hins
    simp only [slot.b_a_run_loop0_loop6.body]
    step*
  · exact ⟨hB, Or.inl (le_refl _)⟩

@[local step]
theorem a_skip_loop_spec (input : Slice Std.U8) (out : Slice Std.U32) (nt p lim step : Std.Usize)
    (hdec : ADec input out nt.val p.val) (hlim : lim.val ≤ input.length) :
    slot.b_a_run_loop0_loop7 input out nt p lim step ⦃ fun r =>
      ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length ∧ p.val ≤ r.2.2.val ⦄ := by
  rw [slot.b_a_run_loop0_loop7]
  apply Std.loop.spec_decr_nat
    (measure := fun r => r.2.2.2.val)
    (inv := fun r => ADec input r.1 r.2.1.val r.2.2.1.val ∧ r.1.length = out.length ∧
      p.val ≤ r.2.2.1.val)
  · rintro ⟨out', nt', p', step'⟩ ⟨hdec', hlen', hp'⟩
    simp only at hdec' hlen' hp'
    simp only [slot.b_a_run_loop0_loop7.body]
    step*
  · exact ⟨hdec, rfl, le_refl _⟩

@[local step]
theorem a_tail_loop1_spec (input : Slice Std.U8) (out : Slice Std.U32) (n nt p : Std.Usize)
    (hn : n.val = input.length) (hdec : ADec input out nt.val p.val) :
    slot.b_a_run_loop1 input out n nt p ⦃ fun r => r.1.val ≤ input.length ∧
      r.2.length = out.length ∧ LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_run_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun r => n.val - r.2.2.val)
    (inv := fun r => ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length)
  · rintro ⟨out', nt', p'⟩ ⟨hdec', hlen'⟩
    simp only at hdec' hlen'
    simp only [slot.b_a_run_loop1.body]
    step*
    have hd := ADec.done hdec' (by scalar_tac)
    exact ⟨hd.1, hlen', hd.2⟩
  · exact ⟨hdec, rfl⟩

@[local step]
theorem a_tail_loop2_spec (input : Slice Std.U8) (out : Slice Std.U32) (n nt p : Std.Usize)
    (hn : n.val = input.length) (hdec : ADec input out nt.val p.val) :
    slot.b_a_run_loop2 input out n nt p ⦃ fun r => r.1.val ≤ input.length ∧
      r.2.length = out.length ∧ LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_run_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun r => n.val - r.2.2.val)
    (inv := fun r => ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length)
  · rintro ⟨out', nt', p'⟩ ⟨hdec', hlen'⟩
    simp only at hdec' hlen'
    simp only [slot.b_a_run_loop2.body]
    step*
    have hd := ADec.done hdec' (by scalar_tac)
    exact ⟨hd.1, hlen', hd.2⟩
  · exact ⟨hdec, rfl⟩

@[local step]
theorem a_tail_loop3_spec (input : Slice Std.U8) (out : Slice Std.U32) (n nt p : Std.Usize)
    (hn : n.val = input.length) (hdec : ADec input out nt.val p.val) :
    slot.b_a_run_loop3 input out n nt p ⦃ fun r => r.1.val ≤ input.length ∧
      r.2.length = out.length ∧ LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_run_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun r => n.val - r.2.2.val)
    (inv := fun r => ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length)
  · rintro ⟨out', nt', p'⟩ ⟨hdec', hlen'⟩
    simp only at hdec' hlen'
    simp only [slot.b_a_run_loop3.body]
    step*
    have hd := ADec.done hdec' (by scalar_tac)
    exact ⟨hd.1, hlen', hd.2⟩
  · exact ⟨hdec, rfl⟩

def AMainInv (input : Slice Std.U8) (L : Nat) (out : Slice Std.U32) (nt p : Nat)
    {N : Std.Usize} (head : Array Std.U32 N) (miss : Nat) : Prop :=
  ADec input out nt p ∧ out.length = L ∧ AHeadBound head p ∧ miss ≤ p

theorem AMainInv.mk' {input : Slice Std.U8} {L : Nat} {out : Slice Std.U32} {nt p m B : Nat}
    {N : Std.Usize} {head : Array Std.U32 N} (hdec : ADec input out nt p) (hlen : out.length = L)
    (hB : AHeadBound head B) (hBp : B ≤ p) (hm : m ≤ p) : AMainInv input L out nt p head m :=
  ⟨hdec, hlen, AHeadBound.mono hB hBp, hm⟩

set_option maxHeartbeats 16000000 in
attribute [local step] a_sat_add_spec a_sat_sub_spec in
theorem a_main_loop_spec {H W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p : Std.Usize) (mask : Std.U32)
    (minl depth l2d «partial» lazy skip skcap nice ldep insm stride : Std.Usize) (hlit : Std.I32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins miss fuel : Std.Usize) (L : Nat)
    (hlim : lim.val + 8 = input.length) (hminl : 3 ≤ minl.val)
    (hminl8 : minl.val ≤ 8) (hskip : skip.val < 32) (hH : 0 < H.val) (hW : 0 < W.val)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000)
    (hinv : AMainInv input L out nt.val p.val head miss.val) :
    slot.b_a_run_loop0 input out nt p mask minl depth l2d «partial» lazy skip skcap nice ldep insm stride hlit
      head prev lim ins miss fuel ⦃ fun r => ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = L ⦄ := by
  rw [slot.b_a_run_loop0]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.loop.spec_decr_nat
    (measure := fun r => r.2.2.2.2.2.2.2.val)
    (inv := fun r => AMainInv input L r.1 r.2.1.val r.2.2.1.val r.2.2.2.1 r.2.2.2.2.2.2.1.val)
  · rintro ⟨out, nt, p, head, prev, ins, miss, fuel⟩ hinv
    simp only at hinv
    have hinv' := hinv
    obtain ⟨hdec, hL, hB, hmiss⟩ := hinv'
    simp only [slot.b_a_run_loop0.body]
    step*
    case hm => exact AFoundAt.real (by assumption) (by scalar_tac)
    case hB => exact AHeadBound.mono (by assumption) (by omega)
    case hy => have := numBits_ge; scalar_tac
    ·
      apply WP.spec_bind (a_ite_dspec _ _ _ (fun (x : Std.Usize) => x.val ≤ «end».val)
        (fun h => by scalar_tac) (fun _ => le_refl _))
      intro stop hstop
      apply WP.spec_bind (a_ite_dspec _ _ _
        (fun (x : Std.Usize) => x.val ≤ «end».val ∧ x.val ≤ lim.val)
        (fun h => ⟨by scalar_tac, le_refl _⟩) (fun h => ⟨hstop, by scalar_tac⟩))
      intro stop1 hstop1
      step*
      case heB => scalar_tac
      case hS2 => scalar_tac
      all_goals
        apply WP.spec_bind (a_tail_ite_spec (by assumption) (by scalar_tac) (by scalar_tac))
        intro ins5 _
        step*
        all_goals (refine ⟨AMainInv.mk' (by assumption) (by omega) (by assumption) (by omega)
          (by simp), by omega⟩)
    ·
      apply WP.spec_bind (a_ite_spec _ _ _ (fun _ => True) trivial trivial)
      intro step1 _
      step*
      all_goals first
        | (refine ⟨AMainInv.mk' (by assumption) (by omega) (by assumption) (by omega)
            (by omega), by omega⟩)
        | exact ADec.cast (by assumption) (by omega)
  · exact hinv

@[local step]
theorem a_main_loop_spec' {H W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p : Std.Usize) (mask : Std.U32)
    (minl depth l2d «partial» lazy skip skcap nice ldep insm stride : Std.Usize) (hlit : Std.I32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins miss fuel : Std.Usize)
    (hlim : lim.val + 8 = input.length) (hminl : 3 ≤ minl.val)
    (hminl8 : minl.val ≤ 8) (hskip : skip.val < 32) (hH : 0 < H.val) (hW : 0 < W.val)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000)
    (hdec : ADec input out nt.val p.val) (hB : AHeadBound head p.val) (hmiss : miss.val ≤ p.val) :
    slot.b_a_run_loop0 input out nt p mask minl depth l2d «partial» lazy skip skcap nice ldep insm stride hlit
      head prev lim ins miss fuel ⦃ fun r =>
        ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length ⦄ :=
  a_main_loop_spec input out nt p mask minl depth l2d «partial» lazy skip skcap nice ldep insm stride hlit head
    prev lim ins miss fuel out.length hlim hminl hminl8 hskip hH hW hh0 hh1
    ⟨hdec, rfl, hB, hmiss⟩

theorem a_lazy_dna_inv {H W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p minl lazy : Std.Usize) (hlit : Std.I32) (head : Array Std.U32 H)
    (prev : Array Std.U32 W) (lim ins l d : Std.Usize) (go : Std.U32) (L : Nat)
    (hlim : lim.val + 8 = input.length) (hminl : 3 ≤ minl.val) (hminl10 : minl.val ≤ 10)
    (hH : 0 < H.val) (hW : 0 < W.val) (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000)
    (hinv : ALazyInv input L lim.val out nt.val p.val head ins.val l.val d.val) :
    slot.b_a_run_dna_loop0_loop1 input out nt p minl lazy hlit head prev lim ins l d go ⦃ fun r =>
      ALazyInv input L lim.val r.1 r.2.1.val r.2.2.1.val r.2.2.2.1 r.2.2.2.2.2.1.val
        r.2.2.2.2.2.2.1.val r.2.2.2.2.2.2.2.val ⦄ := by
  rw [slot.b_a_run_dna_loop0_loop1]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.loop.spec_decr_nat
    (measure := fun r => lim.val - r.2.2.1.val + r.2.2.2.2.2.2.2.2.val)
    (inv := fun r => ALazyInv input L lim.val r.1 r.2.1.val r.2.2.1.val r.2.2.2.1
      r.2.2.2.2.2.1.val r.2.2.2.2.2.2.1.val r.2.2.2.2.2.2.2.1.val)
  · clear hinv
    rintro ⟨out, nt, p, head, prev, ins, l, d, go⟩ hinv
    simp only at hinv
    have hinv' := hinv
    obtain ⟨hdec, hL, hm, hB, hplim, hins⟩ := hinv'
    have hdec' := hdec
    have hm' := hm
    obtain ⟨hps, hntp, hso, -⟩ := hdec'
    obtain ⟨h3, h258, hpl, hd1, hd32, hdp, -⟩ := hm'
    simp only [slot.b_a_run_dna_loop0_loop1.body]
    step*

    apply WP.spec_bind (Pₘ := fun (h : Std.Usize) => h.val + 1 ≤ l.val)
    · split
      · step*
      · simp only [Std.WP.spec_ok]; scalar_tac
    intro «have» hhave
    step*
    all_goals first
      | exact ALazyInv.reject_step hinv (by assumption) (by omega) (by omega)
      | exact ALazyInv.accept_step hinv hminl (by assumption) (by assumption) (by assumption)
          (by assumption) (by omega) (by omega) (by omega) (by omega) (by assumption) (by omega)
  · exact hinv

@[local step]
theorem a_lazy_dna_spec {H W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p minl lazy : Std.Usize) (hlit : Std.I32) (head : Array Std.U32 H)
    (prev : Array Std.U32 W) (lim ins l d : Std.Usize) (go : Std.U32) (L : Nat)
    (hlim : lim.val + 8 = input.length) (hminl : 3 ≤ minl.val) (hminl10 : minl.val ≤ 10)
    (hH : 0 < H.val) (hW : 0 < W.val) (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000)
    (hdec : ADec input out nt.val p.val) (hlen : out.length = L)
    (hm : AMatchAt input p.val l.val d.val) (hB : AHeadBound head (p.val + 2))
    (hplim : p.val < lim.val) (hins : ins.val ≤ p.val + 3) :
    slot.b_a_run_dna_loop0_loop1 input out nt p minl lazy hlit head prev lim ins l d go ⦃ fun r =>
      ADec input r.1 r.2.1.val r.2.2.1.val ∧ r.1.length = L ∧
      AMatchAt input r.2.2.1.val r.2.2.2.2.2.2.1.val r.2.2.2.2.2.2.2.val ∧
      AHeadBound r.2.2.2.1 (r.2.2.1.val + r.2.2.2.2.2.2.1.val) ∧ r.2.2.1.val < lim.val ∧
      r.2.2.2.2.2.1.val ≤ r.2.2.1.val + 3 ∧ 3 ≤ r.2.2.2.2.2.2.1.val ⦄ := by
  apply Std.WP.spec_mono (a_lazy_dna_inv input out nt p minl lazy hlit head prev lim ins l d go L
    hlim hminl hminl10 hH hW hh0 hh1 ⟨hdec, hlen, hm, hB, hplim, hins⟩)
  rintro ⟨out', nt', p', head', prev', ins', l', d'⟩ ⟨hdec', hlen', hm', hB', hplim', hins'⟩
  exact ⟨hdec', hlen', hm', AHeadBound.mono hB' (by have := hm'.1; omega), hplim', hins', hm'.1⟩

theorem a_back_dna_inv (input : Slice Std.U8) (out : Slice Std.U32) (nt p l d back : Std.Usize)
    (L E P0 : Nat) (hP0 : P0 + 8 ≤ input.length)
    (hinv : ABackInv input L d.val E P0 out nt.val p.val l.val) :
    slot.b_a_run_dna_loop0_loop2 input out nt p l d back ⦃ fun r =>
      ABackInv input L d.val E P0 out r.1.val r.2.1.val r.2.2.val ⦄ := by
  rw [slot.b_a_run_dna_loop0_loop2]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.loop.spec_decr_nat
    (measure := fun r => slot.B_A_BACKTOK.val - r.2.2.2.val)
    (inv := fun r => ABackInv input L d.val E P0 out r.1.val r.2.1.val r.2.2.1.val)
  · rintro ⟨nt, p, l, back⟩ hinv
    simp only at hinv
    have hinv' := hinv
    obtain ⟨⟨hps, hntp, hso, _⟩, hL, ⟨h3, h258, hpl, hd1, hd32, hdp, _⟩, hE, hp0⟩ := hinv'
    simp only [slot.b_a_run_dna_loop0_loop2.body]
    step*
    all_goals first
      | exact ABackInv.lit_step (t := t) (x := i3) (y := i5) (i4 := i4) hinv (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption)
      | exact ABackInv.match_step (t := t) (i6 := i6) (i7 := i7) (i8 := i8) (w := w) (i11 := i11)
          (i12 := i12) hinv (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  · exact hinv

@[local step]
theorem a_back_dna_spec (input : Slice Std.U8) (out : Slice Std.U32) (nt p l d back : Std.Usize)
    (hp8 : p.val + 8 ≤ input.length) (hdec : ADec input out nt.val p.val)
    (hm : AMatchAt input p.val l.val d.val) :
    slot.b_a_run_dna_loop0_loop2 input out nt p l d back ⦃ fun r =>
      ADec input out r.1.val r.2.1.val ∧ AMatchAt input r.2.1.val r.2.2.val d.val ∧
      r.2.1.val + r.2.2.val = p.val + l.val ∧ r.2.1.val ≤ p.val ⦄ := by
  apply Std.WP.spec_mono (a_back_dna_inv input out nt p l d back out.length (p.val + l.val) p.val hp8
    ⟨hdec, rfl, hm, rfl, le_refl _⟩)
  intro r h
  obtain ⟨h1, _, h3, h4, h5⟩ := h
  exact ⟨h1, h3, h4, h5⟩

@[local step]
theorem a_ins_dna0_spec {H W : Std.Usize} (input : Slice Std.U8) (p : Std.Usize)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (ins : Std.Usize) (B : Nat)
    (hB : AHeadBound head B) (hpB : p.val < B + 1) (hp8 : p.val + 8 ≤ input.length)
    (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_dna_loop0_loop0 input p head prev ins ⦃ fun r => AHeadBound r.1 B ⦄ := by
  rw [slot.b_a_run_dna_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun r => p.val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B)
  · rintro ⟨head, prev, ins⟩ hB
    simp only at hB
    simp only [slot.b_a_run_dna_loop0_loop0.body]
    step*
  · exact hB

@[local step]
theorem a_ins_dna3_spec {H W : Std.Usize} (input : Slice Std.U8)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (ins stop : Std.Usize) (B : Nat)
    (hB : AHeadBound head B) (hsB : stop.val < B + 1) (hs8 : stop.val + 8 ≤ input.length)
    (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_dna_loop0_loop3 input head prev ins stop ⦃ fun r =>
      AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ stop.val) ⦄ := by
  rw [slot.b_a_run_dna_loop0_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun r => stop.val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ stop.val))
  · rintro ⟨head, prev, ins'⟩ ⟨hB, hins⟩
    simp only at hB hins
    simp only [slot.b_a_run_dna_loop0_loop3.body]
    step*
  · exact ⟨hB, Or.inl (le_refl _)⟩

@[local step]
theorem a_stride_dna_spec {H W : Std.Usize} (input : Slice Std.U8)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins e2 : Std.Usize)
    (B : Nat) (hB : AHeadBound head B) (heB : e2.val < B + 1) (hl8 : lim.val + 8 = input.length)
    (hH : 0 < H.val) (hW : 0 < W.val) (hS : 0 < slot.B_A_STRIDE.val)
    (hS2 : e2.val + slot.B_A_STRIDE.val ≤ Std.Usize.max) :
    slot.b_a_run_dna_loop0_loop4 input head prev lim ins e2 ⦃ fun r =>
      AHeadBound r.1 B ∧
        (r.2.2.val ≤ ins.val ∨ (0 < e2.val ∧ r.2.2.val < e2.val + slot.B_A_STRIDE.val)) ⦄ := by
  rw [slot.b_a_run_dna_loop0_loop4]
  apply Std.loop.spec_decr_nat
    (measure := fun r => e2.val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B ∧
      (r.2.2.val ≤ ins.val ∨ (0 < e2.val ∧ r.2.2.val < e2.val + slot.B_A_STRIDE.val)))
  · rintro ⟨head, prev, ins'⟩ ⟨hB, hins⟩
    simp only at hB hins
    simp only [slot.b_a_run_dna_loop0_loop4.body]
    step*
    all_goals first
      | exact ⟨hB, hins⟩
      | exact ⟨by assumption, by scalar_tac, by scalar_tac⟩
  · exact ⟨hB, Or.inl (le_refl _)⟩

@[local step]
theorem a_ins_dna5_spec {H W : Std.Usize} (input : Slice Std.U8)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins «end» : Std.Usize) (B : Nat)
    (hB : AHeadBound head B) (heB : «end».val < B + 1) (hl8 : lim.val + 8 = input.length)
    (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_dna_loop0_loop5 input head prev lim ins «end» ⦃ fun r =>
      AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ «end».val) ⦄ := by
  rw [slot.b_a_run_dna_loop0_loop5]
  apply Std.loop.spec_decr_nat
    (measure := fun r => «end».val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ «end».val))
  · rintro ⟨head, prev, ins'⟩ ⟨hB, hins⟩
    simp only at hB hins
    simp only [slot.b_a_run_dna_loop0_loop5.body]
    step*
  · exact ⟨hB, Or.inl (le_refl _)⟩

@[local step]
theorem a_ins_dna6_spec {H W : Std.Usize} (input : Slice Std.U8)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins «end» : Std.Usize) (B : Nat)
    (hB : AHeadBound head B) (heB : «end».val < B + 1) (hl8 : lim.val + 8 = input.length)
    (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_dna_loop0_loop6 input head prev lim ins «end» ⦃ fun r =>
      AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ «end».val) ⦄ := by
  rw [slot.b_a_run_dna_loop0_loop6]
  apply Std.loop.spec_decr_nat
    (measure := fun r => «end».val - r.2.2.val)
    (inv := fun r => AHeadBound r.1 B ∧ (r.2.2.val ≤ ins.val ∨ r.2.2.val ≤ «end».val))
  · rintro ⟨head, prev, ins'⟩ ⟨hB, hins⟩
    simp only at hB hins
    simp only [slot.b_a_run_dna_loop0_loop6.body]
    step*
  · exact ⟨hB, Or.inl (le_refl _)⟩

@[local step]
theorem a_skip_dna_spec (input : Slice Std.U8) (out : Slice Std.U32) (nt p lim step : Std.Usize)
    (hdec : ADec input out nt.val p.val) (hlim : lim.val ≤ input.length) :
    slot.b_a_run_dna_loop0_loop7 input out nt p lim step ⦃ fun r =>
      ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length ∧ p.val ≤ r.2.2.val ⦄ := by
  rw [slot.b_a_run_dna_loop0_loop7]
  apply Std.loop.spec_decr_nat
    (measure := fun r => r.2.2.2.val)
    (inv := fun r => ADec input r.1 r.2.1.val r.2.2.1.val ∧ r.1.length = out.length ∧
      p.val ≤ r.2.2.1.val)
  · rintro ⟨out', nt', p', step'⟩ ⟨hdec', hlen', hp'⟩
    simp only at hdec' hlen' hp'
    simp only [slot.b_a_run_dna_loop0_loop7.body]
    step*
  · exact ⟨hdec, rfl, le_refl _⟩

@[local step]
theorem a_tail_dna1_spec (input : Slice Std.U8) (out : Slice Std.U32) (n nt p : Std.Usize)
    (hn : n.val = input.length) (hdec : ADec input out nt.val p.val) :
    slot.b_a_run_dna_loop1 input out n nt p ⦃ fun r => r.1.val ≤ input.length ∧
      r.2.length = out.length ∧ LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_run_dna_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun r => n.val - r.2.2.val)
    (inv := fun r => ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length)
  · rintro ⟨out', nt', p'⟩ ⟨hdec', hlen'⟩
    simp only at hdec' hlen'
    simp only [slot.b_a_run_dna_loop1.body]
    step*
    have hd := ADec.done hdec' (by scalar_tac)
    exact ⟨hd.1, hlen', hd.2⟩
  · exact ⟨hdec, rfl⟩

@[local step]
theorem a_tail_dna2_spec (input : Slice Std.U8) (out : Slice Std.U32) (n nt p : Std.Usize)
    (hn : n.val = input.length) (hdec : ADec input out nt.val p.val) :
    slot.b_a_run_dna_loop2 input out n nt p ⦃ fun r => r.1.val ≤ input.length ∧
      r.2.length = out.length ∧ LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_run_dna_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun r => n.val - r.2.2.val)
    (inv := fun r => ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length)
  · rintro ⟨out', nt', p'⟩ ⟨hdec', hlen'⟩
    simp only at hdec' hlen'
    simp only [slot.b_a_run_dna_loop2.body]
    step*
    have hd := ADec.done hdec' (by scalar_tac)
    exact ⟨hd.1, hlen', hd.2⟩
  · exact ⟨hdec, rfl⟩

set_option maxHeartbeats 16000000 in
attribute [local step] a_sat_add_spec a_sat_sub_spec in
theorem a_main_dna_spec {H W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p minl depth lazy skip skcap : Std.Usize) (hlit : Std.I32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins miss fuel : Std.Usize) (L : Nat)
    (hlim : lim.val + 8 = input.length) (hminl : 3 ≤ minl.val) (hminl10 : minl.val ≤ 10)
    (hskip : skip.val < 32) (hH : 0 < H.val) (hW : 0 < W.val)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000)
    (hinv : AMainInv input L out nt.val p.val head miss.val) :
    slot.b_a_run_dna_loop0 input out nt p minl depth lazy skip skcap hlit head prev lim ins miss fuel
      ⦃ fun r => ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = L ⦄ := by
  rw [slot.b_a_run_dna_loop0]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.loop.spec_decr_nat
    (measure := fun r => r.2.2.2.2.2.2.2.val)
    (inv := fun r => AMainInv input L r.1 r.2.1.val r.2.2.1.val r.2.2.2.1 r.2.2.2.2.2.2.1.val)
  · rintro ⟨out, nt, p, head, prev, ins, miss, fuel⟩ hinv
    simp only at hinv
    have hinv' := hinv
    obtain ⟨hdec, hL, hB, hmiss⟩ := hinv'
    simp only [slot.b_a_run_dna_loop0.body]
    step*
    case hm => exact AFoundAt.real (by assumption) (by scalar_tac)
    case hB => exact AHeadBound.mono (by assumption) (by omega)
    case hy => have := numBits_ge; scalar_tac
    ·
      apply WP.spec_bind (a_ite_dspec _ _ _ (fun (x : Std.Usize) => x.val ≤ «end».val)
        (fun h => by scalar_tac) (fun _ => le_refl _))
      intro stop hstop
      apply WP.spec_bind (a_ite_dspec _ _ _
        (fun (x : Std.Usize) => x.val ≤ «end».val ∧ x.val ≤ lim.val)
        (fun h => ⟨by scalar_tac, le_refl _⟩) (fun h => ⟨hstop, by scalar_tac⟩))
      intro stop1 hstop1
      step*
      all_goals first
        | (apply WP.spec_bind (a_tail_ite_spec (by assumption) (by scalar_tac) (by scalar_tac))
           intro ins5 _
           step*
           all_goals (refine ⟨AMainInv.mk' (by assumption) (by omega) (by assumption) (by omega)
             (by simp), by omega⟩))
        | scalar_tac
    ·
      apply WP.spec_bind (a_ite_spec _ _ _ (fun _ => True) trivial trivial)
      intro step1 _
      step*
      all_goals first
        | (refine ⟨AMainInv.mk' (by assumption) (by omega) (by assumption) (by omega)
            (by omega), by omega⟩)
        | exact ADec.cast (by assumption) (by omega)
  · exact hinv

@[local step]
theorem a_main_dna_spec' {H W : Std.Usize} (input : Slice Std.U8) (out : Slice Std.U32)
    (nt p minl depth lazy skip skcap : Std.Usize) (hlit : Std.I32)
    (head : Array Std.U32 H) (prev : Array Std.U32 W) (lim ins miss fuel : Std.Usize)
    (hlim : lim.val + 8 = input.length) (hminl : 3 ≤ minl.val) (hminl10 : minl.val ≤ 10)
    (hskip : skip.val < 32) (hH : 0 < H.val) (hW : 0 < W.val)
    (hh0 : 0 ≤ hlit.val) (hh1 : hlit.val ≤ 1000000)
    (hdec : ADec input out nt.val p.val) (hB : AHeadBound head p.val) (hmiss : miss.val ≤ p.val) :
    slot.b_a_run_dna_loop0 input out nt p minl depth lazy skip skcap hlit head prev lim ins miss fuel
      ⦃ fun r => ADec input r.1 r.2.1.val r.2.2.val ∧ r.1.length = out.length ⦄ :=
  a_main_dna_spec input out nt p minl depth lazy skip skcap hlit head prev lim ins miss fuel
    out.length hlim hminl hminl10 hskip hH hW hh0 hh1 ⟨hdec, rfl, hB, hmiss⟩

def ACntBound (cnt : Array Std.U32 256#usize) (T : Nat) : Prop :=
  ∀ j : Nat, j < 256 → (cnt.val[j]!).val ≤ T

theorem ACntBound.init : ACntBound (Std.Array.repeat 256#usize 0#u32) 0 := by
  intro j hj
  rw [Std.Array.repeat_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_replicate_of_lt (by simpa using hj)]
  rfl

theorem ACntBound.get {cnt : Array Std.U32 256#usize} {T : Nat} (h : ACntBound cnt T)
    (a : Std.Usize) (x : Std.U32) (ha : a.val < cnt.val.length) (hx : x = cnt.val[a.val]) :
    x.val ≤ T := by
  have := h a.val (by simpa using ha)
  rw [getElem!_pos cnt.val a.val ha, ← hx] at this
  exact this

theorem a_cnt_index_spec (cnt : Array Std.U32 256#usize) (T : Nat) (h : ACntBound cnt T)
    (i : Std.Usize) (hi : i.val < 256) :
    Std.Array.index_usize cnt i ⦃ fun x => x = cnt.val[i.val]! ∧ x.val ≤ T ⦄ := by
  have hl : i.val < cnt.val.length := by simp; omega
  have := Std.Array.index_usize_spec cnt i (by simpa using hl)
  apply Std.WP.spec_mono this
  intro x hx
  refine ⟨by rw [getElem!_pos cnt.val i.val hl]; exact hx, ACntBound.get h i x hl hx⟩

theorem ACntBound.update {cnt : Array Std.U32 256#usize} {T : Nat} (h : ACntBound cnt T)
    (a : Std.Usize) (v : Std.U32) (hv : v.val ≤ T + 1) : ACntBound (cnt.set a v) (T + 1) := by
  intro j hj
  rw [Std.Array.set_val_eq]
  by_cases hja : a.val = j
  · subst hja
    have hlen : a.val < cnt.val.length := by simp; omega
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hlen]
    exact hv
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hja, ← List.getElem!_eq_getElem?_getD]
    exact le_trans (h j hj) (by omega)

theorem ACntBound.step {cnt a : Array Std.U32 256#usize} {T : Nat} {x : Std.Usize}
    {v tot1 : Std.U32} (hc : ACntBound cnt T) (ha : a = cnt.set x v) (hv : v.val ≤ T + 1)
    (ht1 : tot1.val = T + 1) : ACntBound a tot1.val := by
  rw [ha, ht1]
  exact ACntBound.update hc x v hv

theorem ACntBound.mono {cnt : Array Std.U32 256#usize} {T T' : Nat} (h : ACntBound cnt T)
    (hT : T ≤ T') : ACntBound cnt T' := fun j hj => le_trans (h j hj) hT

attribute [local step] a_cnt_index_spec in
theorem a_sniff_loop0_spec (s : Slice Std.U8) (n : Std.Usize) (cnt : Array Std.U32 256#usize)
    (step i : Std.Usize) (tot : Std.U32) (hn : n.val = s.length) (hc : ACntBound cnt tot.val)
    (ht : tot.val ≤ 4097) :
    slot.b_a_sniff_loop0 s n cnt step i tot ⦃ fun r => ACntBound r.1 r.2.val ∧ r.2.val ≤ 4097 ⦄ := by
  rw [slot.b_a_sniff_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 4097 - r.2.2.val)
    (inv := fun r => ACntBound r.1 r.2.2.val ∧ r.2.2.val ≤ 4097)
  · rintro ⟨cnt, i, tot⟩ ⟨hc, ht⟩
    simp only at hc ht
    simp only [slot.b_a_sniff_loop0.body]
    step*
    all_goals first
      | exact ⟨hc, ht⟩
      | exact ⟨ACntBound.step hc (by assumption) (by scalar_tac) (by scalar_tac), by scalar_tac,
          by scalar_tac⟩
  · exact ⟨hc, ht⟩

attribute [local step] a_cnt_index_spec in
theorem a_sniff_loop1_spec (cnt : Array Std.U32 256#usize) (text high words : Std.U32) (b : Std.Usize)
    (hc : ACntBound cnt 4097) (htext : text.val ≤ (b.val + 3) * 4097)
    (hhigh : high.val ≤ b.val * 4097) (hwords : words.val ≤ (b.val + 1) * 4097)
    (hb : b.val ≤ 256) :
    slot.b_a_sniff_loop1 cnt text high words b ⦃ fun _ => True ⦄ := by
  rw [slot.b_a_sniff_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 256 - r.2.2.2.val)
    (inv := fun r => r.1.val ≤ (r.2.2.2.val + 3) * 4097 ∧ r.2.1.val ≤ r.2.2.2.val * 4097 ∧
      r.2.2.1.val ≤ (r.2.2.2.val + 1) * 4097 ∧ r.2.2.2.val ≤ 256)
  · rintro ⟨text, high, words, b⟩ ⟨htext, hhigh, hwords, hb⟩
    simp only at htext hhigh hwords hb
    simp only [slot.b_a_sniff_loop1.body]
    split
    ·
      apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ text.val + 4097)
      · split
        · step*
        · simp only [Std.WP.spec_ok]; omega
      intro text1 ht1
      apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ high.val + 4097)
      · split
        · step*
        · simp only [Std.WP.spec_ok]; omega
      intro high1 hh1
      apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ words.val + 4097)
      · repeat' (split <;> step*)
        all_goals (simp only [Std.WP.spec_ok]; omega)
      intro words1 hw1
      step*
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> scalar_tac
    · step*
  · exact ⟨htext, hhigh, hwords, hb⟩

attribute [local step] a_sniff_loop1_spec

attribute [local step] a_cnt_index_spec in

theorem a_sniff_loop2_spec (cnt : Array Std.U32 256#usize) (mx : Std.U32) (sq : Std.U64)
    (b2 : Std.Usize) (hc : ACntBound cnt 4097) (hb : b2.val ≤ 256) :
    slot.b_a_sniff_loop2 cnt mx sq b2 ⦃ fun _ => True ⦄ := by
  rw [slot.b_a_sniff_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 256 - r.2.2.val)
    (inv := fun r => r.2.2.val ≤ 256)
  · rintro ⟨mx, sq, b2⟩ hb
    simp only at hb
    simp only [slot.b_a_sniff_loop2.body]
    step*
    repeat' (split <;> step*)
  · exact hb

attribute [local step] a_sniff_loop2_spec

attribute [local step] a_cnt_index_spec in

theorem a_sniff_loop3_spec (cnt : Array Std.U32 256#usize) (mx : Std.U32) (sq : Std.U64)
    (b2 : Std.Usize) (hc : ACntBound cnt 4097) (hb : b2.val ≤ 256) :
    slot.b_a_sniff_loop3 cnt mx sq b2 ⦃ fun _ => True ⦄ := by
  rw [slot.b_a_sniff_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 256 - r.2.2.val)
    (inv := fun r => r.2.2.val ≤ 256)
  · rintro ⟨mx, sq, b2⟩ hb
    simp only at hb
    simp only [slot.b_a_sniff_loop3.body]
    step*
    repeat' (split <;> step*)
  · exact hb

attribute [local step] a_sniff_loop3_spec

attribute [local step] a_cnt_index_spec in

theorem a_sniff_loop4_spec (cnt : Array Std.U32 256#usize) (mx : Std.U32) (sq : Std.U64)
    (b2 : Std.Usize) (hc : ACntBound cnt 4097) (hb : b2.val ≤ 256) :
    slot.b_a_sniff_loop4 cnt mx sq b2 ⦃ fun _ => True ⦄ := by
  rw [slot.b_a_sniff_loop4]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 256 - r.2.2.val)
    (inv := fun r => r.2.2.val ≤ 256)
  · rintro ⟨mx, sq, b2⟩ hb
    simp only at hb
    simp only [slot.b_a_sniff_loop4.body]
    step*
    repeat' (split <;> step*)
  · exact hb

attribute [local step] a_sniff_loop4_spec

attribute [local step] a_cnt_index_spec in

theorem a_sniff_loop5_spec (cnt : Array Std.U32 256#usize) (mx : Std.U32) (sq : Std.U64)
    (b2 : Std.Usize) (hc : ACntBound cnt 4097) (hb : b2.val ≤ 256) :
    slot.b_a_sniff_loop5 cnt mx sq b2 ⦃ fun _ => True ⦄ := by
  rw [slot.b_a_sniff_loop5]
  apply Std.loop.spec_decr_nat
    (measure := fun r => 256 - r.2.2.val)
    (inv := fun r => r.2.2.val ≤ 256)
  · rintro ⟨mx, sq, b2⟩ hb
    simp only at hb
    simp only [slot.b_a_sniff_loop5.body]
    step*
    repeat' (split <;> step*)
  · exact hb

attribute [local step] a_sniff_loop5_spec

@[local step]
theorem a_sniff_spec (s : Slice Std.U8) : slot.b_a_sniff s ⦃ fun _ => True ⦄ := by

  have hcnt := @a_cnt_index_spec
  rw [slot.b_a_sniff]
  step*
  apply Std.WP.spec_bind (a_sniff_loop0_spec s (Std.Slice.len s) _ step 0#usize 0#u32 (by simp)
    (by simpa using ACntBound.init) (by simp))
  rintro ⟨cnt1, tot⟩ ⟨hc, ht⟩
  simp only at hc ht
  have hc4 := ACntBound.mono hc ht
  clear hc
  step*
  repeat' (split <;> step*)

set_option maxHeartbeats 16000000 in
attribute [local step] a_hcast_I32_spec a_sat_add_spec in
theorem a_run_spec (H W : Std.Usize) (input : Slice Std.U8) (out : Slice Std.U32) (cls lvl : Std.Usize)
    (hlen : input.length ≤ out.length) (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run H W input out cls lvl ⦃ fun r => r.1.val ≤ input.length ∧ r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_run]
  have hB : (UScalar.hcast .I32 slot.B_A_B_HLIT).val = slot.B_A_B_HLIT.val :=
    a_hcast_I32_val _ (by scalar_tac)

  apply WP.spec_bind (a_ite_spec _ _ _ (fun _ => True) trivial trivial); intro depth _
  apply WP.spec_bind (a_ite_spec _ _ _ (fun _ => True) trivial trivial); intro l2d _
  apply WP.spec_bind (a_ite_spec _ _ _ (fun _ => True) trivial trivial); intro «partial» _
  apply WP.spec_bind (a_ite_spec _ _ _ (fun _ => True) trivial trivial); intro insm _
  apply WP.spec_bind (a_ite_spec _ _ _ (fun _ => True) trivial trivial); intro stride _
  step
  apply WP.spec_bind (a_ite_spec _ _ _ (fun _ => True) trivial trivial)
  rintro ⟨depth1, lazy, nice, ldep, insm1, stride1⟩ -
  apply WP.spec_bind (a_ite_spec _ _ _
    (fun (x : Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize) =>
      x.2.2.1.val < 32) (by scalar_tac) (by scalar_tac))
  rintro ⟨depth2, lazy1, skip, nice1, ldep1, insm2, stride2⟩ hskip
  simp only at hskip
  apply WP.spec_bind (Pₘ := fun (x : Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize ×
      Std.Usize × Std.Usize × Std.Usize) => x.2.2.1.val < 32)
  · repeat' (split <;> step*)
    all_goals scalar_tac
  rintro ⟨depth3, lazy2, skip1, skcap, nice2, ldep2, insm3, stride3⟩ hskip1
  simp only at hskip1
  apply WP.spec_bind (Pₘ := fun (h : Std.I32) => 0 ≤ h.val ∧ h.val ≤ 1000000)
  · repeat' split
    all_goals (simp only [Std.WP.spec_ok]; scalar_tac)
  intro hlit1 hhl
  apply WP.spec_bind (a_ite_spec _ _ _
    (fun (x : Std.U32 × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize ×
      Std.Usize × Std.Usize) => 3 ≤ x.2.1.val ∧ x.2.1.val ≤ 8 ∧ x.2.2.2.2.1.val < 32)
    (by scalar_tac) (by simp only; scalar_tac))
  rintro ⟨mask, minl, depth4, lazy3, skip2, nice3, ldep3, insm4, stride4⟩ hms
  simp only at hms
  apply WP.spec_bind (a_ite_spec _ _ _
    (fun (x : Std.U32 × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize ×
      Std.Usize × Std.Usize) => 3 ≤ x.2.1.val ∧ x.2.1.val ≤ 8 ∧ x.2.2.2.2.1.val < 32)
    (by scalar_tac) (by simp only; scalar_tac))
  rintro ⟨mask1, minl1, depth5, lazy4, skip3, nice4, ldep4, insm5, stride5⟩ hms1
  simp only at hms1
  step*
  all_goals first
    | exact ADec.init input out hlen
    | exact AHeadBound.init _

attribute [local step] a_run_spec

attribute [local step] a_hcast_I32_spec a_sat_add_spec in
theorem a_run_dna_spec (H W : Std.Usize) (input : Slice Std.U8) (out : Slice Std.U32)
    (cls : Std.Usize) (hlen : input.length ≤ out.length) (hH : 0 < H.val) (hW : 0 < W.val) :
    slot.b_a_run_dna H W input out cls ⦃ fun r => r.1.val ≤ input.length ∧ r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_run_dna]
  step*
  repeat' (split <;> step*)
  all_goals first
    | exact ADec.init input out hlen
    | exact AHeadBound.init _

attribute [local step] a_run_dna_spec

theorem a_run_rest_spec (input : Slice Std.U8) (out : Slice Std.U32) (cls lvl : Std.Usize)
    (hlen : input.length ≤ out.length) :
    slot.b_a_run_rest input out cls lvl ⦃ fun r => r.1.val ≤ input.length ∧ r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_run_rest]
  split
  · split
    · exact a_run_spec _ _ input out _ _ hlen (by simp) (by simp)
    · exact a_run_spec _ _ input out _ _ hlen (by simp) (by simp)
  · exact a_run_spec _ _ input out _ _ hlen (by simp) (by simp)

@[local step]
theorem a_parse_cls_spec (input : Slice Std.U8) (out : Slice Std.U32) (cls lvl : Std.Usize)
    (hlen : input.length ≤ out.length) :
    slot.b_a_parse_cls input out cls lvl ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out.length ∧ LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_a_parse_cls]
  repeat' ((try dsimp only); split)
  all_goals first
    | exact a_run_spec _ _ input out _ _ hlen (by simp) (by simp)
    | exact a_run_rest_spec input out _ _ hlen
    | exact a_run_dna_spec _ _ input out _ hlen (by simp) (by simp)

open LZ77 (Matches)

theorem sp_SBS_pos : 1 ≤ slot.B_SBS.val := by simp [slot.B_SBS]

theorem sp_SBLOCKS_SBS_lt : slot.B_SBLOCKS.val * slot.B_SBS.val < 4194304 := by
  simp [slot.B_SBLOCKS, slot.B_SBS]

def sp_word8 (input : Slice Std.U8) (p : Nat) : Nat :=
  ((((((((input.val[p]!).val * 256 + (input.val[p + 1]!).val) * 256
    + (input.val[p + 2]!).val) * 256 + (input.val[p + 3]!).val) * 256
    + (input.val[p + 4]!).val) * 256 + (input.val[p + 5]!).val) * 256
    + (input.val[p + 6]!).val) * 256 + (input.val[p + 7]!).val)

theorem sp_u8_lt (x : Std.U8) : x.val < 256 := by scalar_tac

theorem sp_word8_digit (input : Slice Std.U8) (p k : Nat) (hk : k < 8) :
    (input.val[p + k]!).val = sp_word8 input p / 256 ^ (7 - k) % 256 := by
  have := sp_u8_lt (input.val[p]!); have := sp_u8_lt (input.val[p+1]!)
  have := sp_u8_lt (input.val[p+2]!); have := sp_u8_lt (input.val[p+3]!)
  have := sp_u8_lt (input.val[p+4]!); have := sp_u8_lt (input.val[p+5]!)
  have := sp_u8_lt (input.val[p+6]!); have := sp_u8_lt (input.val[p+7]!)
  simp only [sp_word8]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.add_zero, Nat.pow_zero,
    Nat.pow_succ, Nat.one_mul, Nat.sub_self, Nat.reduceSub] <;> omega

theorem sp_word8_prefix (input : Slice Std.U8) (a b d : Nat) (hd : d ≤ 8)
    (h : sp_word8 input a / 2 ^ (64 - 8 * d) = sp_word8 input b / 2 ^ (64 - 8 * d)) :
    ∀ k, k < d → input.val[b + k]! = input.val[a + k]! := by
  intro k hk
  have e : (256 : Nat) ^ (7 - k) = 2 ^ (64 - 8 * d) * 2 ^ (8 * (d - 1 - k)) := by
    rw [← pow_add, show (256 : Nat) = 2 ^ 8 by norm_num, ← pow_mul]
    congr 1; omega
  have key : sp_word8 input a / 256 ^ (7 - k) = sp_word8 input b / 256 ^ (7 - k) := by
    rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]
  have ha := sp_word8_digit input a k (by omega)
  have hb := sp_word8_digit input b k (by omega)
  rw [key] at ha
  scalar_tac

theorem Matches.sp_add_prefix {input : Slice Std.U8} {a b l d : Nat} (h : Matches input a b l)
    (hd : d ≤ 8)
    (hw : sp_word8 input (a + l) / 2 ^ (64 - 8 * d) = sp_word8 input (b + l) / 2 ^ (64 - 8 * d)) :
    Matches input a b (l + d) := by
  intro k hk
  by_cases hkl : k < l
  · exact h k hkl
  · have := sp_word8_prefix input (a + l) (b + l) d hd hw (k - l) (by omega)
    rw [show b + l + (k - l) = b + k by omega, show a + l + (k - l) = a + k by omega] at this
    exact this

theorem Matches.sp_word {input : Slice Std.U8} {a b l l' : Nat} {pa pb d : Std.Usize}
    {x y : Std.U64} (h : Matches input a b l) (hpa : pa.val = a + l) (hpb : pb.val = b + l)
    (hx : x.val = sp_word8 input pa.val) (hy : y.val = sp_word8 input pb.val)
    (hd8 : d.val ≤ 8) (hdiv : x.val / 2 ^ (64 - 8 * d.val) = y.val / 2 ^ (64 - 8 * d.val))
    (hl' : l' = l + d.val) : Matches input a b l' := by
  subst hl'
  rw [hx, hy, hpa, hpb] at hdiv
  exact Matches.sp_add_prefix h hd8 hdiv

theorem Matches.sp_word_eq {input : Slice Std.U8} {a b l l' : Nat} {pa pb : Std.Usize}
    {x y : Std.U64} (h : Matches input a b l) (hpa : pa.val = a + l) (hpb : pb.val = b + l)
    (hx : x.val = sp_word8 input pa.val) (hy : y.val = sp_word8 input pb.val)
    (hxy : ¬(x != y) = true) (hl' : l' = l + 8) : Matches input a b l' := by
  have hxy' : x.val = y.val := by simpa using hxy
  subst hl'
  apply Matches.sp_add_prefix h (le_refl 8)
  rw [← hpa, ← hpb, ← hx, ← hy, hxy']

theorem Matches.sp_byte {input : Slice Std.U8} {a b l l' : Nat} {pa pb : Std.Usize}
    {x y : Std.U8} (h : Matches input a b l) (hpa : pa.val = a + l) (hpb : pb.val = b + l)
    (hpa' : pa.val < input.val.length) (hpb' : pb.val < input.val.length)
    (hx : x = input.val[pa.val]) (hy : y = input.val[pb.val]) (hxy : x = y)
    (hl' : l' = l + 1) : Matches input a b l' := by
  subst hl' hxy
  apply LZ77.Matches.succ h
  rw [← hpa, ← hpb, getElem!_pos input.val pa.val hpa', getElem!_pos input.val pb.val hpb',
    ← hx, ← hy]

theorem sp_nat_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  have : a ^^^ (a ^^^ b) = b := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [h, Nat.xor_zero] at this; exact this

theorem sp_div_eq_of_xor_lt {x y m : Nat} (hz : x ^^^ y < 2 ^ m) : x / 2 ^ m = y / 2 ^ m := by
  have h : (x ^^^ y) >>> m = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hz
  rw [Nat.shiftRight_xor_distrib] at h
  have := sp_nat_xor_eq_zero h
  simpa [Nat.shiftRight_eq_div_pow] using this

theorem sp_lt_pow_leadingZeros (z : BitVec 64) :
    z.toNat < 2 ^ (64 - 8 * (BitVec.leadingZeros z / 8)) := by
  unfold BitVec.leadingZeros
  split
  case isTrue h => subst h; simp
  case isFalse h =>
    have hz : z.toNat ≠ 0 := by
      intro h0; apply h; exact BitVec.eq_of_toNat_eq (by simpa using h0)
    have hlog : Nat.log 2 z.toNat < 64 := Nat.log_lt_of_lt_pow hz z.isLt
    have h1 : z.toNat < 2 ^ (Nat.log 2 z.toNat).succ := Nat.lt_pow_succ_log_self (by norm_num) _
    refine lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) ?_)
    omega

@[local step]
theorem load8_spec (input : Slice Std.U8) (p : Std.Usize) (hp : p.val + 8 ≤ input.length) :
    slot.b_load8 input p ⦃ fun v => v.val = sp_word8 input p.val ⦄ := by
  have hlift := @lift_spec
  rw [slot.b_load8]
  step*
  simp only [← getElem!_pos] at *
  simp only [sp_word8]
  simp_all only [U8.cast_U64_val_eq]

@[local step]
theorem first_diff_spec (x y : Std.U64) :
    slot.b_first_diff x y ⦃ fun d => d.val ≤ 8 ∧
      x.val / 2 ^ (64 - 8 * d.val) = y.val / 2 ^ (64 - 8 * d.val) ⦄ := by
  have hlift := @lift_spec
  rw [slot.b_first_diff]
  step*
  have hle : BitVec.leadingZeros z.bv ≤ 64 := by unfold BitVec.leadingZeros; split <;> omega
  have hlz : lz.val = BitVec.leadingZeros z.bv := by
    rw [lz_post]
    simp only [core.num.U64.leading_zeros, UScalar.val, UScalarTy.U32_numBits_eq,
      BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have hd : (UScalar.cast UScalarTy.Usize bytes).val = BitVec.leadingZeros z.bv / 8 := by
    simp only [U32.cast_Usize_val_eq, bytes_post, hlz]
  have hz : z.bv.toNat = x.val ^^^ y.val := by
    have : z.val = z.bv.toNat := rfl
    rw [← this, z_post, UScalar.val_xor]
  refine ⟨by rw [hd]; omega, ?_⟩
  rw [hd]
  apply sp_div_eq_of_xor_lt
  rw [← hz]
  exact sp_lt_pow_leadingZeros z.bv

@[local step]
theorem mlen_loop0_loop0_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.b_mlen_loop0_loop0 input a b cap l0 ⦃ fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.b_mlen_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val)
  · rintro l ⟨hle, hm⟩
    simp only [slot.b_mlen_loop0_loop0.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    exact Matches.sp_byte hm (by assumption) (by assumption) (by scalar_tac) (by scalar_tac)
      (by assumption) (by assumption) (by assumption) (by scalar_tac)
  · exact ⟨hl0, h0⟩

@[local step]
theorem mlen_loop0_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.b_mlen_loop0 input a b cap l0 ⦃ fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.b_mlen_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val)
  · rintro l ⟨hle, hm⟩
    simp only [slot.b_mlen_loop0.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input

    step*
    ·
      refine ⟨by scalar_tac, ?_⟩
      exact Matches.sp_word hm (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (by scalar_tac)
    ·
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      exact Matches.sp_word_eq hm (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by scalar_tac)
  · exact ⟨hl0, h0⟩

@[local step]
theorem mlen_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.b_mlen input a b cap ⦃ fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ :=
  mlen_loop0_spec input a b cap 0#usize ha hb (by simp) (LZ77.Matches.zero input a.val b.val)

@[local step]
theorem check_spec (input : Slice Std.U8) (p len dist : Std.Usize) :
    slot.b_check input p len dist ⦃ fun valid => valid = true →
      3 ≤ len.val ∧ len.val ≤ 258 ∧ 1 ≤ dist.val ∧ dist.val ≤ 32768 ∧ dist.val ≤ p.val ∧
      p.val + len.val ≤ input.length ∧ Matches input (p.val - dist.val) p.val len.val ⦄ := by
  rw [slot.b_check]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  intro hvalid
  have hl : l = len := by simpa using hvalid
  subst hl
  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac,
    by scalar_tac, ?_⟩
  rw [← src_post1]
  exact l_post2

@[local step]
theorem emit_loop_spec (input : Slice Std.U8) (plan out0 : Slice Std.U32)
    (n ntok0 k0 owed0 p0 : Std.Usize) (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp0 : p0.val ≤ n.val) (hntok0 : ntok0.val ≤ p0.val) (hk0 : k0.val ≤ p0.val)
    (hdec0 : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take p0.val)) :
    slot.b_emit_loop input plan out0 n ntok0 k0 owed0 p0 ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
      LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  have hlift := @lift_spec
  rw [slot.b_emit_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, p) => n.val - p.val)
    (inv := fun (out, ntok, k, _, p) => p.val ≤ n.val ∧ ntok.val ≤ p.val ∧ k.val ≤ p.val ∧
      out.length = out0.length ∧
      LZ77.decode (toks out ntok.val) = some ((bytes input).take p.val))
  · rintro ⟨out, ntok, k, owed, p⟩ ⟨hp, hnt, hk, hlen, hde⟩
    simp only [slot.b_emit_loop.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    split
    case isTrue hlt =>
      have hntok_lt : ntok.val < out.length := by scalar_tac
      step*
      ·
        have hlit : i1.val = (bytes input)[p.val]! := by
          rw [bytes_getElem! input p.val (by scalar_tac)]
          scalar_tac
        refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by rw [s_post]; simpa using hlen, ?_,
          by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show p1.val = p.val + 1 by scalar_tac]
        exact emit_lit input out ntok p.val i1 hde (by scalar_tac) hntok_lt hlit
      ·
        obtain ⟨h3, h258, hd1, hd32k, hdp, hend, hm⟩ := valid_post (by assumption)
        have htok : tok.val = LZ77.mkMatch dist.val len.val := by
          simp only [LZ77.mkMatch, LZ77.MATCH_BASE]
          scalar_tac
        refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by rw [s_post]; simpa using hlen, ?_,
          by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show p1.val = p.val + len.val by scalar_tac]
        exact emit_match input out ntok p.val dist.val len.val tok hde hntok_lt hd1 hdp hd32k
          h3 h258 hend hm htok
      all_goals

        have hlit : i3.val = (bytes input)[p.val]! := by
          rw [bytes_getElem! input p.val (by scalar_tac)]
          scalar_tac
        subst index_mut_back
        refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by simpa using hlen, ?_, by scalar_tac⟩
        rw [show ntok1.val = ntok.val + 1 by scalar_tac, show p1.val = p.val + 1 by scalar_tac]
        exact emit_lit input out ntok p.val i3 hde (by scalar_tac) hntok_lt hlit
    case isFalse hge =>
      have hpn : p.val = input.length := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      rw [hde, hpn]
      simp
  · exact ⟨hp0, hntok0, hk0, rfl, hdec0⟩

@[local step]
theorem emit_spec (input : Slice Std.U8) (plan out : Slice Std.U32)
    (hout : input.length ≤ out.length) :
    slot.b_emit input plan out ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.b_emit]
  exact emit_loop_spec input plan out (Std.Slice.len input) 0#usize 0#usize 0#usize 0#usize
    (by simp) hout (by simp) (by simp) (by simp) (by simp [toks, LZ77.decode])

@[local step]
theorem high_share_loop_spec (input : Slice Std.U8) (n step i hi tot : Std.Usize)
    (hn : n.val = input.length) (hh : hi.val ≤ tot.val) (ht : tot.val ≤ 2049) :
    slot.b_high_share_loop input n step i hi tot ⦃ fun r => r.1.val ≤ r.2.val ∧ r.2.val ≤ 2049 ⦄ := by
  have hlift := @lift_spec
  rw [slot.b_high_share_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, tot') => 2049 - tot'.val)
    (inv := fun (_, hi', tot') => hi'.val ≤ tot'.val ∧ tot'.val ≤ 2049)
  · rintro ⟨i', hi', tot'⟩ ⟨h1, h2⟩
    simp only [slot.b_high_share_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hh, ht⟩

@[local step]
theorem high_share_spec (input : Slice Std.U8) : slot.b_high_share input ⦃ fun _ => True ⦄ := by
  have hlift := @lift_spec
  rw [slot.b_high_share]
  step*
  all_goals scalar_tac

@[local step]
theorem sample_block_loop_spec (input : Slice Std.U8) (st e : Std.Usize) (tab) (lb i : Std.Usize)
    (hst : st.val ≤ i.val) (hi : i.val ≤ e.val) (hlb : lb.val ≤ i.val - st.val)
    (he : e.val + 8 ≤ Std.Usize.max) :
    slot.b_sample_block_loop input st e tab lb i ⦃ fun r => r.1.val ≤ e.val - st.val ⦄ := by
  have hlift := @lift_spec
  rw [slot.b_sample_block_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, i') => e.val - i'.val)
    (inv := fun (_, lb', i') => st.val ≤ i'.val ∧ i'.val ≤ e.val ∧ lb'.val ≤ i'.val - st.val)
  · rintro ⟨tab', lb', i'⟩ ⟨h1, h2, h3⟩
    simp only [slot.b_sample_block_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hst, hi, hlb⟩

@[local step]
theorem sample_block_spec (input : Slice Std.U8) (st e : Std.Usize) (tab)
    (hst : st.val ≤ e.val) (he : e.val + 8 ≤ Std.Usize.max) :
    slot.b_sample_block input st e tab ⦃ fun r => r.1.val ≤ e.val - st.val ⦄ :=
  sample_block_loop_spec input st e tab 0#usize st (le_refl _) hst (by simp) he

theorem sp_block_start {n S B b i i1 i2 i3 : Nat} (hS : S < n) (hb : b < B)
    (hBS : B * S < 4194304) (hS1 : 1 ≤ S)
    (hi : i = n - S) (hi1 : i1 = B + 1) (hi2 : i2 = i / i1) (hi3 : i3 = b + 1) :
    i2 * i3 + S ≤ n ∧ (i2 * i3 + S + 8 ≤ n ∨ n < 37748744) := by
  subst hi hi1 hi2 hi3
  have hq := Nat.div_mul_le_self (n - S) (B + 1)
  have h8 : 8 ≤ (n - S) / (B + 1) ∨ n - S < 8 * (B + 1) := by
    by_cases h : 8 ≤ (n - S) / (B + 1)
    · exact Or.inl h
    · exact Or.inr ((Nat.div_lt_iff_lt_mul (by omega)).mp (by omega))
  have hS' : S ≤ B * S := Nat.le_mul_of_pos_left S (by omega)
  have hB' : B ≤ B * S := Nat.le_mul_of_pos_right B (by omega)
  generalize (n - S) / (B + 1) = q at *
  have h1 : q * (b + 1) + q ≤ q * (B + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  omega

@[local step]
theorem sample_long_loop_spec (input : Slice Std.U8) (n lb tot b : Std.Usize)
    (hn : n.val = input.length) (hlb : lb.val ≤ tot.val) (htot : tot.val = b.val * slot.B_SBS.val)
    (hb : b.val ≤ slot.B_SBLOCKS.val) :
    slot.b_sample_long_loop input n lb tot b ⦃ fun r => r.1.val ≤ r.2.val ∧ r.2.val ≤ slot.B_SBLOCKS.val * slot.B_SBS.val ⦄ := by
  have hS := sp_SBS_pos
  have hBS := sp_SBLOCKS_SBS_lt
  rw [slot.b_sample_long_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, b') => slot.B_SBLOCKS.val - b'.val)
    (inv := fun (lb', tot', b') => lb'.val ≤ tot'.val ∧ tot'.val = b'.val * slot.B_SBS.val ∧
      b'.val ≤ slot.B_SBLOCKS.val)
  · rintro ⟨lb', tot', b'⟩ ⟨h1, h2, h3⟩
    simp only [slot.b_sample_long_loop.body]
    step*

    all_goals
      have hblk := sp_block_start (by scalar_tac) (by scalar_tac) hBS hS i_post1 i1_post i2_post
        i3_post
    all_goals first
      | scalar_tac
      | (have hmul : i3.val * slot.B_SBS.val = b'.val * slot.B_SBS.val + slot.B_SBS.val := by
           rw [i3_post, Nat.add_mul, Nat.one_mul]
         scalar_tac)
  · exact ⟨hlb, htot, hb⟩

@[local step]
theorem sample_long_spec (input : Slice Std.U8) : slot.b_sample_long input ⦃ fun _ => True ⦄ := by
  rw [slot.b_sample_long]
  have := sp_SBLOCKS_SBS_lt
  step*
  all_goals scalar_tac

@[local step]
theorem route_spec (input : Slice Std.U8) (cls : Std.Usize) : slot.b_route input cls ⦃ fun _ => True ⦄ := by
  rw [slot.b_route]
  step*
  repeat' (split <;> step*)

theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.b_parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_parse]
  step*
  all_goals (first | assumption | (refine ⟨by assumption, by assumption, ?_⟩; unfold LZ77.Valid; assumption))

end EB

set_option hygiene false in
local notation "T1!" => (by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h)
set_option hygiene false in
local notation "T2!" q0__:max => (by
  rw [q0__]
  try simp only [lift, Array.to_slice_mut]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac)
set_option hygiene false in
local notation "T3!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 40 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T4!" q0__:max => (by
  rw [q0__]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac)
set_option hygiene false in
local notation "T5!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 8192 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T6!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T7!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => probes.val - s.2.1.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5, x6⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T8!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «to».val - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T9!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «to».val - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T10!" => (by
  unfold w8 at h
  have b0 := (input.val[p]!).hBounds
  have b1 := (input.val[p + 1]!).hBounds
  have b2 := (input.val[p + 2]!).hBounds
  have b3 := (input.val[p + 3]!).hBounds
  have b4 := (input.val[p + 4]!).hBounds
  have b5 := (input.val[p + 5]!).hBounds
  have b6 := (input.val[p + 6]!).hBounds
  have b7 := (input.val[p + 7]!).hBounds
  have c0 := (input.val[q]!).hBounds
  have c1 := (input.val[q + 1]!).hBounds
  have c2 := (input.val[q + 2]!).hBounds
  have c3 := (input.val[q + 3]!).hBounds
  have c4 := (input.val[q + 4]!).hBounds
  have c5 := (input.val[q + 5]!).hBounds
  have c6 := (input.val[q + 6]!).hBounds
  have c7 := (input.val[q + 7]!).hBounds
  simp only [Std.UScalarTy.numBits] at *
  intro k hk
  apply UScalar.eq_imp
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero]) <;> omega)
set_option hygiene false in
local notation "T11!" => (by
  unfold w4 at h
  have b0 := (input.val[p]!).hBounds
  have b1 := (input.val[p + 1]!).hBounds
  have b2 := (input.val[p + 2]!).hBounds
  have b3 := (input.val[p + 3]!).hBounds
  have c0 := (input.val[q]!).hBounds
  have c1 := (input.val[q + 1]!).hBounds
  have c2 := (input.val[q + 2]!).hBounds
  have c3 := (input.val[q + 3]!).hBounds
  simp only [Std.UScalarTy.numBits] at *
  intro k hk
  apply UScalar.eq_imp
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with
    rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero]) <;> omega)
set_option hygiene false in
local notation "T12!" => (by
  have hb := w8_bytes input (a + l) (b + l) hw
  intro k hk
  by_cases hkl : k < l
  · exact h k hkl
  · have := hb (k - l) (by omega)
    rw [show b + k = b + l + (k - l) by omega, show a + k = a + l + (k - l) by omega]
    exact this)
set_option hygiene false in
local notation "T13!" => (by
  have hb := w8_bytes input (a + (c - 8)) (b + (c - 8)) hw
  intro k hk
  by_cases hkl : k < l
  · exact h k hkl
  · have := hb (k - (c - 8)) (by omega)
    rw [show b + k = b + (c - 8) + (k - (c - 8)) by omega,
      show a + k = a + (c - 8) + (k - (c - 8)) by omega]
    exact this)
set_option hygiene false in
local notation "T14!" => (by
  have h0 := w4_bytes input a b hw0
  have h1 := w4_bytes input (a + (c - 4)) (b + (c - 4)) hw1
  intro k hk
  by_cases hk4 : k < 4
  · exact h0 k hk4
  · have := h1 (k - (c - 4)) (by omega)
    rw [show b + k = b + (c - 4) + (k - (c - 4)) by omega,
      show a + k = a + (c - 4) + (k - (c - 4)) by omega]
    exact this)
set_option hygiene false in
local notation "T15!" q0__:max => (by
  rw [q0__]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  unfold w8
  rw [getElem!_pos input.val p.val (by scalar_tac), getElem!_pos input.val (p.val + 1) (by scalar_tac),
    getElem!_pos input.val (p.val + 2) (by scalar_tac), getElem!_pos input.val (p.val + 3) (by scalar_tac),
    getElem!_pos input.val (p.val + 4) (by scalar_tac), getElem!_pos input.val (p.val + 5) (by scalar_tac),
    getElem!_pos input.val (p.val + 6) (by scalar_tac), getElem!_pos input.val (p.val + 7) (by scalar_tac)]
  scalar_tac)
set_option hygiene false in
local notation "T16!" q0__:max => (by
  rw [q0__]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  unfold w4
  rw [getElem!_pos input.val p.val (by scalar_tac), getElem!_pos input.val (p.val + 1) (by scalar_tac),
    getElem!_pos input.val (p.val + 2) (by scalar_tac), getElem!_pos input.val (p.val + 3) (by scalar_tac)]
  scalar_tac)
set_option hygiene false in
local notation "T17!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [q1__]
    step*
    all_goals first
      | exact ⟨hle, hinv⟩
      | (refine ⟨by scalar_tac, ?_, by scalar_tac⟩
         rw [show l1.val = l.val + 8 by scalar_tac]
         apply Matches.add8 hinv
         rw [show a.val + l.val = i1.val by scalar_tac, show b.val + l.val = i3.val by scalar_tac,
           ← i2_post, ← i4_post, ‹i2 = i4›])
  · exact ⟨hl0, h0⟩)
set_option hygiene false in
local notation "T18!" q0__:max => (by
  rw [q0__]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals first
    | (intro h; simp at h)
    | (intro _
       refine ⟨by scalar_tac, by scalar_tac, ?_⟩
       rw [show a.val + (cap.val - 8) = i2.val by scalar_tac,
         show b.val + (cap.val - 8) = i4.val by scalar_tac, ← i3_post, ← i5_post, ‹i3 = i5›])
    | (refine ⟨by scalar_tac, by scalar_tac, ?_⟩
       rw [show a.val + (cap.val - 8) = i2.val by scalar_tac,
         show b.val + (cap.val - 8) = i4.val by scalar_tac, ← i3_post, ← i5_post, ‹i3 = i5›]))
set_option hygiene false in
local notation "T19!" q0__:max => (by
  rw [q0__]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals first
    | (intro h; simp at h)
    | (intro _
       refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
       · rw [← i_post, ← i1_post]
         simp_all
       · rw [show a.val + (cap.val - 4) = i3.val by scalar_tac,
           show b.val + (cap.val - 4) = i5.val by scalar_tac, ← i4_post, ← i6_post, ‹i4 = i6›])
    | (refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
       · rw [← i_post, ← i1_post]
         simp_all
       · rw [show a.val + (cap.val - 4) = i3.val by scalar_tac,
           show b.val + (cap.val - 4) = i5.val by scalar_tac, ← i4_post, ← i6_post, ‹i4 = i6›]))
set_option hygiene false in
local notation "T20!" q0__:max q1__:max => (by
  (
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ LZ77.Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    simp only [q1__]
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
local notation "T21!" q0__:max => (by
  rw [q0__]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  intro hv
  have hv' : ch.val ≤ v.val := by simpa using hv
  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac,
    by scalar_tac, ?_⟩
  rw [show pos.val - d.val = i1.val by scalar_tac]
  exact Matches.mono v_post2 hv')
set_option hygiene false in
local notation "T22!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.1.val)
    (inv := fun s =>
      s.2.1.val ≤ n.val ∧ s.2.1.val = k0.val + s.2.2.1.val ∧ s.2.2.2.val ≤ s.2.1.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.val) = some ((bytes input).take s.2.1.val))
  · rintro ⟨out, k, c, ntok⟩ ⟨hkn, hkc, hnt, hlen, hde⟩
    simp only at hkn hkc hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [q1__]
    split
    case isTrue hklt =>
      split
      case isTrue hc =>
        have hntok_lt : ntok.val < out.length := by scalar_tac
        have hposlen : k.val < input.length := by scalar_tac
        step*
        have hval : i1.val = (bytes input)[k.val]! := by
          rw [bytes_getElem! input k.val hposlen, i1_post, Std.U8.cast_U32_val_eq, i_post]
        refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show k1.val = k.val + 1 by scalar_tac]
        exact emit_lit input out ntok k.val i1 hde hposlen hntok_lt hval
      case isFalse hc =>
        exact ⟨hkn, by scalar_tac, hnt, hlen, hde⟩
    case isFalse hge =>
      exact ⟨hkn, by scalar_tac, hnt, hlen, hde⟩
  · exact ⟨hk, by scalar_tac, hntok, rfl, hdec⟩)
set_option hygiene false in
local notation "T23!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ LZ77.Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    simp only [q1__]
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
  · exact ⟨hl0, h0⟩)
set_option hygiene false in
local notation "T24!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T25!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.2.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T26!" q0__:max q1__:max q2__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => q1__ - s.2.2.2.1.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4⟩ _
    simp only [q2__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T27!" q0__:max => (by
  rw [q0__]
  try simp only [lift, Array.to_slice_mut, ite_ok]
  step*
  repeat (first
    | (intro hc; (try step*))
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac)
set_option hygiene false in
local notation "T28!" q0__:max => (by
  rw [q0__]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by assumption⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac))
set_option hygiene false in
local notation "T29!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.1.val)
    (inv := fun s =>
      s.2.1.val ≤ n.val ∧ s.2.2.val ≤ s.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.val) = some ((bytes input).take s.2.1.val))
  · rintro ⟨out, pos, ntok⟩ ⟨hpn, hnt, hlen, hde⟩
    simp only at hpn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [q1__, lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      all_goals (repeat (first
        | (refine ⟨by scalar_tac, by scalar_tac, by assumption, by assumption, by scalar_tac⟩)
        | (intro hc; (try step*))
        | (casesm* _ × _; (try simp only []); (try step*))
        | (split <;> (try step*))
        | (step <;> (try step*))))
      all_goals (try scalar_tac)
    case isFalse hge =>
      exact ⟨hpn, hnt, hlen, hde⟩
  · exact ⟨hp, hntok, rfl, hdec⟩)
set_option hygiene false in
local notation "T30!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.val)
    (inv := fun s => True)
  · rintro x0 _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T31!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => l.val - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T32!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => depth.val - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T33!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.1.val ≤ n.val ∧ s.2.2.2.2.val ≤ s.2.2.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.val) = some ((bytes input).take s.2.2.2.1.val))
  · rintro ⟨out, head, prev, pos, ntok⟩ ⟨hpn, hnt, hlen, hde⟩
    simp only at hpn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [q1__, lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      all_goals (repeat (first
        | (refine ⟨by scalar_tac, by scalar_tac, by assumption, by assumption, by scalar_tac⟩)
        | (intro hc; (try step*))
        | (casesm* _ × _; (try simp only []); (try step*))
        | (split <;> (try step*))
        | (step <;> (try step*))))
      all_goals (try scalar_tac)
    case isFalse hge =>
      exact ⟨hpn, hnt, hlen, hde⟩
  · exact ⟨hp, hntok, rfl, hdec⟩)
set_option hygiene false in
local notation "T34!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => depth.val - s.2.2.2.2.1.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5, x6⟩ _
    simp only [q1__, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
set_option hygiene false in
local notation "T35!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.1.val ≤ n.val ∧ s.2.2.2.2.1.val ≤ s.2.2.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.1.val) = some ((bytes input).take s.2.2.2.1.val))
  · rintro ⟨out, head, prev, pos, ntok, carry, miss⟩ ⟨hpn, hnt, hlen, hde⟩
    simp only at hpn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [q1__, lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      all_goals (repeat (first
        | (refine ⟨by scalar_tac, by scalar_tac, by assumption, by assumption, by scalar_tac⟩)
        | (intro hc; (try step*))
        | (casesm* _ × _; (try simp only []); (try step*))
        | (split <;> (try step*))
        | (step <;> (try step*))))
      all_goals (try scalar_tac)
    case isFalse hge =>
      exact ⟨hpn, hnt, hlen, hde⟩
  · exact ⟨hp, hntok, rfl, hdec⟩)
set_option hygiene false in
local notation "T36!" => (by
  have hlt : nt - 1 < out.val.length := by
    have : out.length = out.val.length := rfl
    omega
  simp only [toks]
  conv_lhs => rw [show nt = (nt - 1) + 1 by omega]
  rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.map_append]
  simp [getElem!_pos out.val (nt - 1) hlt])
set_option hygiene false in
local notation "T37!" => (by
  simp only [toks, List.length_map, List.length_take]
  have : out.length = out.val.length := rfl
  omega)
set_option hygiene false in
local notation "T38!" q0__:max => (by
  rw [q0__]
  have h0 := decode_nil input out
  try simp only [lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (first
    | (refine ⟨by scalar_tac, by scalar_tac, valid_of_decode (by assumption) (by scalar_tac)⟩)
    | (intro hc; (try step*))
    | (casesm* _ × _; (try simp only []); (try step*))
    | (split <;> (try step*))
    | (step <;> (try step*))))
  all_goals (try scalar_tac))

namespace EY
open Aeneas Aeneas.Std Result ControlFlow
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
open LZ77 (toks bytes bytes_length bytes_getElem! Matches emit_lit emit_match ite_ok)
theorem spec_ite_cut {α : Type} (c : Prop) [Decidable c] (a b : Result α) (Q : α → Prop)
    (ha : c → a ⦃ Q ⦄) (hb : ¬c → b ⦃ Q ⦄) : (if c then a else b) ⦃ Q ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h
set_option hygiene false in
local notation "T39!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 30 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [q1__, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
@[local step]
theorem sum_df_loop_spec (a : Array Std.U32 32#usize) (s : Std.U32) (i : Std.Usize)  :
    slot.y_sum_df_loop a s i ⦃ fun _ => True ⦄ := T39! slot.y_sum_df_loop slot.y_sum_df_loop.body
set_option hygiene false in
local notation "T40!" q0__:max => (by
  rw [q0__]
  simp only [lift]
  step*
  repeat (first
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac)
@[local step]
theorem log2_16_spec (v : Std.U32) :
    slot.y_log2_16 v ⦃ fun _ => True ⦄ := T40! slot.y_log2_16
set_option hygiene false in
local notation "T41!" q0__:max => (by
  rw [q0__]
  step*
  repeat (first
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac)
@[local step]
theorem dp_sym_cost_spec (f : Std.U32) (lt : Std.U32) :
    slot.y_dp_sym_cost f lt ⦃ fun _ => True ⦄ := T41! slot.y_dp_sym_cost
@[local step]
theorem dist_costs_loop0_spec (df : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (lt : Std.U32) (s : Std.Usize)  :
    slot.y_dist_costs_loop0 df scost lt s ⦃ fun _ => True ⦄ := T39! slot.y_dist_costs_loop0 slot.y_dist_costs_loop0.body
set_option hygiene false in
local notation "T42!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [q1__, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
@[local step]
theorem dist_costs_loop1_spec (scost : Array Std.U32 32#usize) (dct : Array Std.U32 512#usize) (j : Std.Usize)  :
    slot.y_dist_costs_loop1 scost dct j ⦃ fun _ => True ⦄ := T42! slot.y_dist_costs_loop1 slot.y_dist_costs_loop1.body
@[local step]
theorem dist_costs_spec (df : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (dct : Array Std.U32 512#usize) :
    slot.y_dist_costs df scost dct ⦃ fun _ => True ⦄ := T41! slot.y_dist_costs
set_option hygiene false in
local notation "T43!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 29 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [q1__, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
@[local step]
theorem len_costs_loop0_spec (llf : Array Std.U32 512#usize) (lt : Std.U32) (scost : Array Std.U32 32#usize) (s : Std.Usize)  :
    slot.y_len_costs_loop0 llf lt scost s ⦃ fun _ => True ⦄ := T43! slot.y_len_costs_loop0 slot.y_len_costs_loop0.body
@[local step]
theorem len_costs_loop1_spec (scost : Array Std.U32 32#usize) (lcost : Array Std.U64 512#usize) (l : Std.Usize)  :
    slot.y_len_costs_loop1 scost lcost l ⦃ fun _ => True ⦄ := by
  rw [slot.y_len_costs_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 259 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.y_len_costs_loop1.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem len_costs_spec (llf : Array Std.U32 512#usize) (lt : Std.U32) (scost : Array Std.U32 32#usize) (lcost : Array Std.U64 512#usize) :
    slot.y_len_costs llf lt scost lcost ⦃ fun _ => True ⦄ := T41! slot.y_len_costs
@[local step]
theorem lit_costs_loop_spec (llf : Array Std.U32 512#usize) (lt : Std.U32) (litc : Array Std.U32 256#usize) (b : Std.Usize)  :
    slot.y_lit_costs_loop llf lt litc b ⦃ fun _ => True ⦄ := T42! slot.y_lit_costs_loop slot.y_lit_costs_loop.body
@[local step]
theorem sum_arr_loop_spec (a : Array Std.U32 512#usize) (m : Std.Usize) (s : Std.U32) (i : Std.Usize)  :
    slot.y_sum_arr_loop a m s i ⦃ fun _ => True ⦄ := by
  rw [slot.y_sum_arr_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => m.val - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.y_sum_arr_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem all_costs_spec (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) :
    slot.y_all_costs llf df scost litc lcost dct ⦃ fun _ => True ⦄ := T41! slot.y_all_costs
set_option hygiene false in
local notation "T44!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 32 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [q1__, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
@[local step]
theorem clear32_loop_spec (a : Array Std.U32 32#usize) (i : Std.Usize)  :
    slot.y_clear32_loop a i ⦃ fun _ => True ⦄ := T44! slot.y_clear32_loop slot.y_clear32_loop.body
set_option hygiene false in
local notation "T45!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 512 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [q1__, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
@[local step]
theorem clear512_loop_spec (a : Array Std.U32 512#usize) (i : Std.Usize)  :
    slot.y_clear512_loop a i ⦃ fun _ => True ⦄ := T45! slot.y_clear512_loop slot.y_clear512_loop.body
@[local step]
theorem copy32_loop_spec (dst : Array Std.U32 32#usize) (src : Array Std.U32 32#usize) (i : Std.Usize)  :
    slot.y_copy32_loop dst src i ⦃ fun _ => True ⦄ := T44! slot.y_copy32_loop slot.y_copy32_loop.body
@[local step]
theorem copy512_loop_spec (dst : Array Std.U32 512#usize) (src : Array Std.U32 512#usize) (i : Std.Usize)  :
    slot.y_copy512_loop dst src i ⦃ fun _ => True ⦄ := T45! slot.y_copy512_loop slot.y_copy512_loop.body
@[local step]
theorem mix32_loop_spec (dst : Array Std.U32 32#usize) (cur : Array Std.U32 32#usize) (prv : Array Std.U32 32#usize) (i : Std.Usize)  :
    slot.y_mix32_loop dst cur prv i ⦃ fun _ => True ⦄ := T44! slot.y_mix32_loop slot.y_mix32_loop.body
@[local step]
theorem mix_loop_spec (dst : Array Std.U32 512#usize) (cur : Array Std.U32 512#usize) (prv : Array Std.U32 512#usize) (i : Std.Usize)  :
    slot.y_mix_loop dst cur prv i ⦃ fun _ => True ⦄ := T45! slot.y_mix_loop slot.y_mix_loop.body
@[local step]
theorem refresh_spec (full : Bool) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (pllf : Array Std.U32 512#usize) (pdf : Array Std.U32 32#usize) (tllf : Array Std.U32 512#usize) (tdf : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) (st : Array Std.Usize 4#usize) :
    slot.y_refresh full llf df pllf pdf tllf tdf scost litc lcost dct st ⦃ fun _ => True ⦄ := T41! slot.y_refresh
@[local step]
theorem clamp_block_spec (e : Std.Usize) (rest : Std.Usize) :
    slot.y_clamp_block e rest ⦃ fun r => 1 ≤ r.val ∧ (r.val = 1 ∨ r.val ≤ rest.val) ⦄ := T41! slot.y_clamp_block
@[local step]
theorem dist_sym_spec (d : Std.Usize) :
    slot.y_dist_sym d ⦃ fun _ => True ⦄ := T40! slot.y_dist_sym
@[local step]
theorem byte_at_spec (input : Slice Std.U8) (i : Std.Usize) :
    slot.y_byte_at input i ⦃ fun _ => True ⦄ := T41! slot.y_byte_at
@[local step]
theorem set_spec (v : Slice Std.U32) (i : Std.Usize) (x : Std.U32) :
    slot.y_set v i x ⦃ fun _ => True ⦄ := T41! slot.y_set
@[local step]
theorem backtrack_loop_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (plan_len : Slice Std.U32) (plan_dist : Slice Std.U32) (start : Std.Usize) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (e : Std.Usize) (cnt : Std.Usize) (lits : Std.Usize) (guard : Std.Usize)  :
    slot.y_backtrack_loop input arr plan_len plan_dist start llf df e cnt lits guard ⦃ fun _ => True ⦄ := by
  rw [slot.y_backtrack_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 8192 - s.2.2.2.2.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ _
    simp only [slot.y_backtrack_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem backtrack_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (plan_len : Slice Std.U32) (plan_dist : Slice Std.U32) (start : Std.Usize) («end» : Std.Usize) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) :
    slot.y_backtrack input arr plan_len plan_dist start «end» llf df ⦃ fun _ => True ⦄ := T40! slot.y_backtrack
@[local step]
theorem block_stop_spec (bend : Std.Usize) (lim : Std.Usize) (reach : Std.Usize) :
    slot.y_block_stop bend lim reach ⦃ fun _ => True ⦄ := T41! slot.y_block_stop
@[local step]
theorem skip_off_spec (cur : Std.Usize) (reach : Std.Usize) :
    slot.y_skip_off cur reach ⦃ fun _ => True ⦄ := T40! slot.y_skip_off
@[local step]
theorem sp_skip_spec (cur : Std.Usize) (reach : Std.Usize) (sparse : Std.Usize) :
    slot.y_sp_skip cur reach sparse ⦃ fun _ => True ⦄ := T40! slot.y_sp_skip
@[local step]
theorem lbucket_spec (l : Std.Usize) :
    slot.y_lbucket l ⦃ fun _ => True ⦄ := T41! slot.y_lbucket
@[local step]
theorem upd_spec (arr : Array Std.U64 8192#usize) (j : Std.Usize) (cand : Std.U64) :
    slot.y_upd arr j cand ⦃ fun _ => True ⦄ := T41! slot.y_upd
@[local step]
theorem lit_step_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (i : Std.Usize) (cur : Std.Usize) (price : Std.U32) :
    slot.y_lit_step input arr litc i cur price ⦃ fun _ => True ⦄ := T40! slot.y_lit_step
@[local step]
theorem fill_inf_loop_spec (arr : Array Std.U64 8192#usize) (j : Std.Usize)  :
    slot.y_fill_inf_loop arr j ⦃ fun _ => True ⦄ := by
  rw [slot.y_fill_inf_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.Y_ARRN.val - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.y_fill_inf_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem hash3w_spec (w : Std.U32) :
    slot.y_hash3w w ⦃ fun _ => True ⦄ := T40! slot.y_hash3w
@[local step]
theorem hash4_spec (w : Std.U32) :
    slot.y_hash4 w ⦃ fun r => r.val < 65536 ⦄ := T40! slot.y_hash4
@[local step]
theorem load_le32_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.y_load_le32 input p ⦃ fun _ => True ⦄ := T40! slot.y_load_le32
@[local step]
theorem insert_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) (i : Std.Usize) :
    slot.y_insert input head prev h3 i ⦃ fun _ => True ⦄ := T40! slot.y_insert
set_option hygiene false in
local notation "T46!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => cnt.val - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [q1__, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
@[local step]
theorem insert_range_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) («from» : Std.Usize) (cnt : Std.Usize) (it : Std.Usize)  :
    slot.y_insert_range_loop input head prev h3 «from» cnt it ⦃ fun _ => True ⦄ := T46! slot.y_insert_range_loop slot.y_insert_range_loop.body
@[local step]
theorem insert_range_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) («from» : Std.Usize) («to» : Std.Usize) :
    slot.y_insert_range input head prev h3 «from» «to» ⦃ fun _ => True ⦄ := T41! slot.y_insert_range
@[local step]
theorem dist_cost_spec (dct : Array Std.U32 512#usize) (d : Std.Usize) :
    slot.y_dist_cost dct d ⦃ fun _ => True ⦄ := T40! slot.y_dist_cost
@[local step]
theorem rel3_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) (pos : Std.Usize) (cur : Std.Usize) (price : Std.U32) (s3 : Std.Usize) (w4 : Std.U32) :
    slot.y_rel3 input arr lcost dct pos cur price s3 w4 ⦃ fun _ => True ⦄ := T40! slot.y_rel3
@[local step]
theorem quick_ok_spec (input : Slice Std.U8) (c : Std.Usize) (pos : Std.Usize) (best : Std.Usize) :
    slot.y_quick_ok input c pos best ⦃ fun _ => True ⦄ := T40! slot.y_quick_ok
@[local step]
theorem relax_range_loop_spec (arr : Array Std.U64 8192#usize) (lcost : Array Std.U64 512#usize) (cur : Std.Usize) (lo : Std.Usize) (cnt : Std.Usize) (bb : Std.U64) (it : Std.Usize)  :
    slot.y_relax_range_loop arr lcost cur lo cnt bb it ⦃ fun _ => True ⦄ := by
  rw [slot.y_relax_range_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => cnt.val - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.y_relax_range_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem relax_range_spec (arr : Array Std.U64 8192#usize) (lcost : Array Std.U64 512#usize) (cur : Std.Usize) (lo : Std.Usize) (hi : Std.Usize) (base : Std.U32) (ebits : Std.U64) :
    slot.y_relax_range arr lcost cur lo hi base ebits ⦃ fun _ => True ⦄ := T40! slot.y_relax_range
@[local step]
theorem word_at_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.y_word_at input p ⦃ fun _ => True ⦄ := T40! slot.y_word_at
@[local step]
theorem back_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (c : Std.Usize) (cap : Std.Usize) (k : Std.Usize) (go : Std.Usize) (it : Std.Usize)  :
    slot.y_back_len_loop input a c cap k go it ⦃ fun _ => True ⦄ := by
  rw [slot.y_back_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 40 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.y_back_len_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem back_len_spec (input : Slice Std.U8) (a : Std.Usize) (c : Std.Usize) (cap : Std.Usize) :
    slot.y_back_len input a c cap ⦃ fun _ => True ⦄ := T41! slot.y_back_len
@[local step]
theorem back_ext_spec (input : Slice Std.U8) (pos : Std.Usize) (c : Std.Usize) (cap : Std.Usize) (wb : Std.U64) :
    slot.y_back_ext input pos c cap wb ⦃ fun _ => True ⦄ := T40! slot.y_back_ext
@[local step]
theorem at64_spec (a : Array Std.U64 8192#usize) (i : Std.Usize) :
    slot.y_at64 a i ⦃ fun _ => True ⦄ := T41! slot.y_at64
@[local step]
theorem relax_cand_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) (pos : Std.Usize) (cur : Std.Usize) (price : Std.U32) (c : Std.Usize) (d : Std.Usize) (lo : Std.Usize) (l : Std.Usize) (wb : Std.U64) (bx : Std.Usize) (bk : Array Std.U32 8192#usize) :
    slot.y_relax_cand input arr lcost dct pos cur price c d lo l wb bx bk ⦃ fun _ => True ⦄ := T40! slot.y_relax_cand
@[local step]
theorem byte_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) (n : Std.Usize) (l : Std.Usize)  :
    slot.y_byte_len_loop input a b cap n l ⦃ fun _ => True ⦄ := by
  rw [slot.y_byte_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => cap.val - s.val)
    (inv := fun s => True)
  · rintro x0 _
    simp only [slot.y_byte_len_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem byte_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) :
    slot.y_byte_len input a b cap ⦃ fun _ => True ⦄ := T41! slot.y_byte_len
@[local step]
theorem tzb_spec (x : Std.U64) :
    slot.y_tzb x ⦃ fun _ => True ⦄ := T40! slot.y_tzb
@[local step]
theorem fast_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) (n : Std.Usize) (l : Std.Usize) (go : Std.Usize) (it : Std.Usize)  :
    slot.y_fast_len_loop input a b cap n l go it ⦃ fun _ => True ⦄ := by
  rw [slot.y_fast_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 34 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.y_fast_len_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem fast_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) :
    slot.y_fast_len input a b cap ⦃ fun _ => True ⦄ := T41! slot.y_fast_len
@[local step]
theorem cand_len_spec (input : Slice Std.U8) (c : Std.Usize) (pos : Std.Usize) (cap : Std.Usize) (x : Std.U64) :
    slot.y_cand_len input c pos cap x ⦃ fun _ => True ⦄ := T40! slot.y_cand_len
@[local step]
theorem walk_loop_spec (input : Slice Std.U8) (prev : Array Std.U16 32768#usize) (arr : Array Std.U64 8192#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) (pos : Std.Usize) (cur : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) (price : Std.U32) (bx : Std.Usize) (wp : Std.U64) (bk : Array Std.U32 8192#usize) (wb : Std.U64) (best : Std.Usize) (d : Std.Usize) (probes : Std.Usize)  :
    slot.y_walk_loop input prev arr lcost dct pos cur cap depth price bx wp bk wb best d probes ⦃ fun _ => True ⦄ := by
  rw [slot.y_walk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => depth.val - s.2.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4⟩ _
    simp only [slot.y_walk_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem walk_spec (input : Slice Std.U8) (prev : Array Std.U16 32768#usize) (arr : Array Std.U64 8192#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) (pos : Std.Usize) (cur : Std.Usize) (cap : Std.Usize) (s4 : Std.Usize) (depth : Std.Usize) (price : Std.U32) (bx : Std.Usize) (wp : Std.U64) (bk : Array Std.U32 8192#usize) :
    slot.y_walk input prev arr lcost dct pos cur cap s4 depth price bx wp bk ⦃ fun _ => True ⦄ := T40! slot.y_walk
@[local step]
theorem sstep_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) (i : Std.Usize) (cur : Std.Usize) (price : Std.U32) (depth : Std.Usize) (bx : Std.Usize) (bk : Array Std.U32 8192#usize) :
    slot.y_sstep input head prev h3 arr litc lcost dct i cur price depth bx bk ⦃ fun _ => True ⦄ := T40! slot.y_sstep
@[local step]
theorem lit_run_loop_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (start : Std.Usize) (cur0 : Std.Usize) (cnt : Std.Usize) (price : Std.U32) (it : Std.Usize)  :
    slot.y_lit_run_loop input arr litc start cur0 cnt price it ⦃ fun _ => True ⦄ := by
  rw [slot.y_lit_run_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => cnt.val - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.y_lit_run_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem lit_run_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (start : Std.Usize) (cur0 : Std.Usize) (stop : Std.Usize) (price0 : Std.U32) :
    slot.y_lit_run input arr litc start cur0 stop price0 ⦃ fun _ => True ⦄ := T41! slot.y_lit_run
@[local step]
theorem insert_run_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) (start : Std.Usize) (cur0 : Std.Usize) (cnt : Std.Usize) (it : Std.Usize)  :
    slot.y_insert_run_loop input head prev h3 start cur0 cnt it ⦃ fun _ => True ⦄ := T46! slot.y_insert_run_loop slot.y_insert_run_loop.body
@[local step]
theorem insert_run_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) (start : Std.Usize) (cur0 : Std.Usize) (stop : Std.Usize) :
    slot.y_insert_run input head prev h3 start cur0 stop ⦃ fun _ => True ⦄ := T41! slot.y_insert_run
@[local step]
theorem interior_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (start : Std.Usize) (cur0 : Std.Usize) (cnt : Std.Usize) (price : Std.U32) (it : Std.Usize)  :
    slot.y_interior_loop input head prev h3 arr litc start cur0 cnt price it ⦃ fun _ => True ⦄ := by
  rw [slot.y_interior_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => cnt.val - s.2.2.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5⟩ _
    simp only [slot.y_interior_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem interior_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (start : Std.Usize) (cur0 : Std.Usize) (stop : Std.Usize) (price0 : Std.U32) :
    slot.y_interior input head prev h3 arr litc start cur0 stop price0 ⦃ fun _ => True ⦄ := T40! slot.y_interior
@[local step]
theorem put64_spec (a : Array Std.U64 8192#usize) (i : Std.Usize) (x : Std.U64) :
    slot.y_put64 a i x ⦃ fun _ => True ⦄ := T41! slot.y_put64
@[local step]
theorem dp_block_loop_spec (input : Slice Std.U8) (start : Std.Usize) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) (arr : Array Std.U64 8192#usize) (bk : Array Std.U32 8192#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) (rem : Std.Usize) (bend : Std.Usize) (lim : Std.Usize) (sat : Std.Usize) (price : Std.U32) (cur : Std.Usize) (reach : Std.Usize) (miss : Std.Usize) (acc_next : Std.Usize) (sparse : Std.Usize) (row : Std.Usize) (dgt : Std.Usize) (dbase : Std.Usize) (kend : Std.Usize) (it : Std.Usize)  :
    slot.y_dp_block_loop input start head prev h3 arr bk litc lcost dct rem bend lim sat price cur reach miss acc_next sparse row dgt dbase kend it ⦃ fun _ => True ⦄ := by
  rw [slot.y_dp_block_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 8192 - s.2.2.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13⟩ _
    simp only [slot.y_dp_block_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem dp_block_spec (input : Slice Std.U8) (start : Std.Usize) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 16384#usize) (arr : Array Std.U64 8192#usize) (bk : Array Std.U32 8192#usize) (cl : Array Std.U32 16#usize) (cd : Array Std.U32 16#usize) (cb : Array Std.U32 16#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U64 512#usize) (dct : Array Std.U32 512#usize) (st : Array Std.Usize 4#usize) :
    slot.y_dp_block input start head prev h3 arr bk cl cd cb litc lcost dct st ⦃ fun _ => True ⦄ := T40! slot.y_dp_block
@[local step]
theorem scale_prior_loop0_spec (llf : Array Std.U32 512#usize) (i : Std.Usize)  :
    slot.y_scale_prior_loop0 llf i ⦃ fun _ => True ⦄ := T45! slot.y_scale_prior_loop0 slot.y_scale_prior_loop0.body
@[local step]
theorem scale_prior_loop1_spec (df : Array Std.U32 32#usize) (j : Std.Usize)  :
    slot.y_scale_prior_loop1 df j ⦃ fun _ => True ⦄ := T44! slot.y_scale_prior_loop1 slot.y_scale_prior_loop1.body
@[local step]
theorem scale_prior_spec (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) :
    slot.y_scale_prior llf df ⦃ fun _ => True ⦄ := T41! slot.y_scale_prior
@[local step]
theorem sample_hist_loop_spec (input : Slice Std.U8) (h0 : Array Std.U32 256#usize) (h1 : Array Std.U32 256#usize) (h2 : Array Std.U32 256#usize) (h3 : Array Std.U32 256#usize) (q : Std.Usize) (k : Std.Usize)  :
    slot.y_sample_hist_loop input h0 h1 h2 h3 q k ⦃ fun _ => True ⦄ := by
  rw [slot.y_sample_hist_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => q.val - s.2.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3, x4⟩ _
    simp only [slot.y_sample_hist_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem sample_hist_spec (input : Slice Std.U8) (h0 : Array Std.U32 256#usize) (h1 : Array Std.U32 256#usize) (h2 : Array Std.U32 256#usize) (h3 : Array Std.U32 256#usize) :
    slot.y_sample_hist input h0 h1 h2 h3 ⦃ fun _ => True ⦄ := T41! slot.y_sample_hist
@[local step]
theorem init_stats_loop0_spec (llf : Array Std.U32 512#usize) (h0 : Array Std.U32 256#usize) (h1 : Array Std.U32 256#usize) (h2 : Array Std.U32 256#usize) (h3 : Array Std.U32 256#usize) (sc : Std.U32) (b : Std.Usize)  :
    slot.y_init_stats_loop0 llf h0 h1 h2 h3 sc b ⦃ fun _ => True ⦄ := T42! slot.y_init_stats_loop0 slot.y_init_stats_loop0.body
@[local step]
theorem init_stats_loop1_spec (llf : Array Std.U32 512#usize) (pm : Std.U32) (s : Std.Usize)  :
    slot.y_init_stats_loop1 llf pm s ⦃ fun _ => True ⦄ := T43! slot.y_init_stats_loop1 slot.y_init_stats_loop1.body
@[local step]
theorem init_stats_loop2_spec (df : Array Std.U32 32#usize) (pm : Std.U32) (t : Std.Usize)  :
    slot.y_init_stats_loop2 df pm t ⦃ fun _ => True ⦄ := T39! slot.y_init_stats_loop2 slot.y_init_stats_loop2.body
@[local step]
theorem init_stats_spec (input : Slice Std.U8) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) :
    slot.y_init_stats input llf df ⦃ fun _ => True ⦄ := T40! slot.y_init_stats
theorem match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.y_match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := T20! slot.y_match_len_loop slot.y_match_len_loop.body
@[local step]
theorem match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.y_match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  (
  exact match_len_loop_spec input a b cap 0#usize ha hb (by scalar_tac)
    (LZ77.Matches.zero input a.val b.val))
theorem verified_spec (input : Slice Std.U8) (pos d ch : Std.Usize) :
    slot.y_verified input pos d ch ⦃ fun b => b = true →
      3 ≤ ch.val ∧ ch.val ≤ 258 ∧ 1 ≤ d.val ∧ d.val ≤ 32768 ∧ d.val ≤ pos.val ∧
      pos.val + ch.val ≤ input.length ∧ Matches input (pos.val - d.val) pos.val ch.val ⦄ := T21! slot.y_verified
@[local step]
theorem get_spec (v : Slice Std.U32) (i : Std.Usize) :
    slot.y_get v i ⦃ fun _ => True ⦄ := T41! slot.y_get
theorem emit_range_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (plan_len plan_dist : Slice Std.U32) (base e n k0 ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ n.val) (hntok : ntok0.val ≤ k0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take k0.val)) :
    slot.y_emit_range_loop input out0 plan_len plan_dist base e n k0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ k0.val ≤ r.2.1.val ∧ (e.val ≤ r.2.1.val ∨ r.2.1.val = n.val) ∧
      r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := by
  rw [slot.y_emit_range_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.1.val)
    (inv := fun s =>
      s.2.1.val ≤ n.val ∧ k0.val ≤ s.2.1.val ∧ s.2.2.val ≤ s.2.1.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.val) = some ((bytes input).take s.2.1.val))
  · rintro ⟨out, k, ntok⟩ ⟨hkn, hk0, hnt, hlen, hde⟩
    simp only at hkn hk0 hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.y_emit_range_loop.body]
    split
    case isTrue hke =>
      split
      case isTrue hklt =>
        have hntok_lt : ntok.val < out.length := by scalar_tac
        step*
        apply Std.WP.spec_bind (verified_spec input k d ch)
        intro b hb
        split
        case isTrue hbt =>
          obtain ⟨hch3, hch258, hd1, hdmax, hdpos, hend, hmatch⟩ := hb hbt
          step*
          have htok : i10.val = LZ77.mkMatch d.val ch.val := by
            simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i10_post, i7_post, i6_post]
            scalar_tac
          refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
            by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
          rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
            show k1.val = k.val + ch.val by scalar_tac]
          exact emit_match input out ntok k.val d.val ch.val i10 hde hntok_lt hd1 hdpos hdmax
            hch3 hch258 hend hmatch htok
        case isFalse hbf =>
          have hposlen : k.val < input.length := by scalar_tac
          step*
          have hval : i5.val = (bytes input)[k.val]! := by
            rw [bytes_getElem! input k.val hposlen, i5_post, Std.U8.cast_U32_val_eq, i4_post]
          refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
            by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
          rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
            show k1.val = k.val + 1 by scalar_tac]
          exact emit_lit input out ntok k.val i5 hde hposlen hntok_lt hval
      case isFalse hge =>
        exact ⟨hkn, hk0, Or.inr (by scalar_tac), hnt, hlen, hde⟩
    case isFalse hge =>
      exact ⟨hkn, hk0, Or.inl (by scalar_tac), hnt, hlen, hde⟩
  · exact ⟨hk, le_refl _, hntok, rfl, hdec⟩
@[local step]
theorem emit_range_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (plan_len plan_dist : Slice Std.U32) (base k0 e ntok0 : Std.Usize)
    (hout : input.length ≤ out.length) (hk : k0.val ≤ input.length) (hntok : ntok0.val ≤ k0.val)
    (hdec : LZ77.decode (toks out ntok0.val) = some ((bytes input).take k0.val)) :
    slot.y_emit_range input out plan_len plan_dist base k0 e ntok0 ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ k0.val ≤ r.1.2.val ∧
      (e.val ≤ r.1.2.val ∨ r.1.2.val = input.length) ∧
      r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.y_emit_range]
  apply Std.WP.spec_bind (emit_range_loop_spec input out plan_len plan_dist base e _ k0 ntok0
    (by simp) hout (by scalar_tac) hntok hdec)
  rintro ⟨out1, k, ntok⟩ h
  simp only at h
  step*
theorem filled_loop0_spec (x : Std.U32) (v0 : alloc.vec.Vec Std.U32) (n8 i0 : Std.Usize)
    (hn8 : 8 * n8.val ≤ Std.Usize.max) (h0 : v0.length = 8 * i0.val) (hi : i0.val ≤ n8.val) :
    slot.y_filled_loop0 x v0 n8 i0 ⦃ fun r => r.length = 8 * n8.val ⦄ := by
  rw [slot.y_filled_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n8.val - s.2.val)
    (inv := fun s => s.1.length = 8 * s.2.val ∧ s.2.val ≤ n8.val)
  · rintro ⟨v, i⟩ ⟨hv, hle⟩
    simp only at hv hle
    simp only [slot.y_filled_loop0.body]
    split
    case isTrue hlt =>
      step*
      all_goals (simp_all; scalar_tac)
    case isFalse hge =>
      simp only [Std.WP.spec_ok]
      scalar_tac
  · exact ⟨h0, hi⟩
theorem filled_loop1_spec (n : Std.Usize) (x : Std.U32) (v0 : alloc.vec.Vec Std.U32)
    (j0 : Std.Usize) (h0 : v0.length = j0.val) (hj : j0.val ≤ n.val) :
    slot.y_filled_loop1 n x v0 j0 ⦃ fun r => r.length = n.val ⦄ := by
  rw [slot.y_filled_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.val)
    (inv := fun s => s.1.length = s.2.val ∧ s.2.val ≤ n.val)
  · rintro ⟨v, j⟩ ⟨hv, hle⟩
    simp only at hv hle
    simp only [slot.y_filled_loop1.body]
    split
    case isTrue hlt =>
      step*
      simp_all
      scalar_tac
    case isFalse hge =>
      simp only [Std.WP.spec_ok]
      scalar_tac
  · exact ⟨h0, hj⟩
@[local step]
theorem filled_spec (n : Std.Usize) (x : Std.U32) :
    slot.y_filled n x ⦃ fun r => r.length = n.val ⦄ := by
  rw [slot.y_filled]
  step*
  apply Std.WP.spec_bind (filled_loop0_spec x _ n8 0#usize (by scalar_tac)
    (by simp [alloc.vec.Vec.with_capacity]) (by scalar_tac))
  intro v1 hv1
  step*
  exact filled_loop1_spec n x v1 j (by scalar_tac) (by scalar_tac)
theorem dp_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize) (head0 : Array Std.U32 65536#usize) (prev0 : Array Std.U16 32768#usize) (h30 : Array Std.U32 16384#usize) (arr0 : Array Std.U64 8192#usize) (bk0 : Array Std.U32 8192#usize) (cl0 : Array Std.U32 16#usize) (cd0 : Array Std.U32 16#usize) (cb0 : Array Std.U32 16#usize) (litc0 : Array Std.U32 256#usize) (lcost0 : Array Std.U64 512#usize) (dct0 : Array Std.U32 512#usize) (scost0 : Array Std.U32 32#usize) (llf0 : Array Std.U32 512#usize) (df0 : Array Std.U32 32#usize) (pllf0 : Array Std.U32 512#usize) (pdf0 : Array Std.U32 32#usize) (tllf0 : Array Std.U32 512#usize) (tdf0 : Array Std.U32 32#usize) (st0 : Array Std.Usize 4#usize) (plan_len0 : alloc.vec.Vec Std.U32) (plan_dist0 : alloc.vec.Vec Std.U32) (pos00 : Std.Usize) (k0 : Std.Usize) (ntok0 : Std.Usize) (blk0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos00.val ≤ k0.val) (hk : k0.val ≤ n.val) (hntok : ntok0.val ≤ k0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take k0.val)) :
    slot.y_dp_parse_loop input out0 n head0 prev0 h30 arr0 bk0 cl0 cd0 cb0 litc0 lcost0 dct0 scost0 llf0 df0 pllf0 pdf0 tllf0 tdf0 st0 plan_len0 plan_dist0 pos00 k0 ntok0 blk0 ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
      LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.y_dp_parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ≤ s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ∧ s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ≤ n.val ∧ s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ≤ s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val) = some ((bytes input).take s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val))
  · rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25⟩ ⟨hpk, hkn, hnt, hlen, hde⟩
    simp only at hpk hkn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.y_dp_parse_loop.body, lift, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      repeat (split <;> step*)
      all_goals (first
        | (refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, by assumption, by scalar_tac⟩)
        | scalar_tac)
    case isFalse hge =>
      have hpn : x23.val = input.length := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      rw [hde, hpn]
      simp
  · exact ⟨hp, hk, hntok, rfl, hdec⟩
@[local step]
theorem dp_parse_spec (input : Slice Std.U8) (out : Slice Std.U32) (cls : Std.Usize)
    (hlen : input.length ≤ out.length) :
    slot.y_dp_parse input out cls ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.y_dp_parse]
  simp only [lift, ite_ok]
  step*
  apply dp_parse_loop_spec
  all_goals first | rfl | assumption | scalar_tac | simp [toks, LZ77.decode]
@[local step]
theorem lg8_spec (x : Std.U32) :
    slot.y_lg8 x ⦃ fun _ => True ⦄ := T40! slot.y_lg8
set_option hygiene false in
local notation "T47!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 256 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [q1__, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial)
@[local step]
theorem entropy256_loop_spec (h : Array Std.U32 256#usize) (tot : Std.U64) (acc : Std.U64) (i : Std.Usize)  :
    slot.y_entropy256_loop h tot acc i ⦃ fun _ => True ⦄ := T47! slot.y_entropy256_loop slot.y_entropy256_loop.body
@[local step]
theorem entropy256_spec (h : Array Std.U32 256#usize) :
    slot.y_entropy256 h ⦃ fun _ => True ⦄ := T41! slot.y_entropy256
@[local step]
theorem entropy16_loop_spec (h : Array Std.U32 32#usize) (base : Std.Usize) (tot : Std.U64) (acc : Std.U64) (i : Std.Usize)  :
    slot.y_entropy16_loop h base tot acc i ⦃ fun _ => True ⦄ := by
  rw [slot.y_entropy16_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 16 - s.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2⟩ _
    simp only [slot.y_entropy16_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem entropy16_spec (h : Array Std.U32 32#usize) (base : Std.Usize) :
    slot.y_entropy16 h base ⦃ fun _ => True ⦄ := T41! slot.y_entropy16
@[local step]
theorem lane_diff_spec (hn : Array Std.U32 32#usize) :
    slot.y_lane_diff hn ⦃ fun _ => True ⦄ := T41! slot.y_lane_diff
@[local step]
theorem odd_sample_loop_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) (hn : Array Std.U32 32#usize) (n : Std.Usize) (st : Std.Usize) (k : Std.Usize) (c : Std.Usize)  :
    slot.y_odd_sample_loop input h hn n st k c ⦃ fun _ => True ⦄ := by
  rw [slot.y_odd_sample_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 8192 - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [slot.y_odd_sample_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem odd_sample_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) (hn : Array Std.U32 32#usize) :
    slot.y_odd_sample input h hn ⦃ fun _ => True ⦄ := T40! slot.y_odd_sample
@[local step]
theorem probe_win_loop_spec (input : Slice Std.U8) (tab : Array Std.U32 4096#usize) (a : Std.Usize) (lim : Std.Usize) (i : Std.Usize) (cov : Std.Usize) (it : Std.Usize)  :
    slot.y_probe_win_loop input tab a lim i cov it ⦃ fun _ => True ⦄ := by
  rw [slot.y_probe_win_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 65536 - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [slot.y_probe_win_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem probe_win_spec (input : Slice Std.U8) (tab : Array Std.U32 4096#usize) (a : Std.Usize) :
    slot.y_probe_win input tab a ⦃ fun _ => True ⦄ := T40! slot.y_probe_win
@[local step]
theorem redund_loop_spec (input : Slice Std.U8) (tab : Array Std.U32 4096#usize) (wins : Std.Usize) (step : Std.Usize) (cov : Std.Usize) (tot : Std.Usize) (w : Std.Usize)  :
    slot.y_redund_loop input tab wins step cov tot w ⦃ fun _ => True ⦄ := by
  rw [slot.y_redund_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => wins.val - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [slot.y_redund_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem redund_spec (input : Slice Std.U8) (pre : Std.Usize) :
    slot.y_redund input pre ⦃ fun _ => True ⦄ := T40! slot.y_redund
@[local step]
theorem hshare_loop_spec (h : Array Std.U32 256#usize) (lo : Std.Usize) (hi : Std.Usize) (tot : Std.Usize) (s : Std.Usize) (i : Std.Usize)  :
    slot.y_hshare_loop h lo hi tot s i ⦃ fun _ => True ⦄ := T47! slot.y_hshare_loop slot.y_hshare_loop.body
@[local step]
theorem hshare_spec (h : Array Std.U32 256#usize) (lo : Std.Usize) (hi : Std.Usize) :
    slot.y_hshare h lo hi ⦃ fun _ => True ⦄ := T40! slot.y_hshare
@[local step]
theorem dp_class_spec (n : Std.Usize) (fv : Array Std.Usize 8#usize) :
    slot.y_dp_class n fv ⦃ fun _ => True ⦄ := T41! slot.y_dp_class
@[local step]
theorem band_spec (x : Std.Usize) (lo : Std.Usize) (hi : Std.Usize) :
    slot.y_band x lo hi ⦃ fun _ => True ⦄ := T41! slot.y_band
@[local step]
theorem inbox_loop_spec (fv : Array Std.Usize 8#usize) (b : Array Std.Usize 16#usize) (r : Std.Usize) (i : Std.Usize)  :
    slot.y_inbox_loop fv b r i ⦃ fun _ => True ⦄ := by
  rw [slot.y_inbox_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 8 - s.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1⟩ _
    simp only [slot.y_inbox_loop.body, lift]
    step*
    repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem fast_route_spec (n : Std.Usize) (h0 : Std.Usize) (lane : Std.Usize) (fv : Array Std.Usize 8#usize) :
    slot.y_fast_route n h0 lane fv ⦃ fun _ => True ⦄ := T40! slot.y_fast_route
theorem decode_nil (input : Slice Std.U8) (out : Slice Std.U32) :
    LZ77.decode (toks out (0#usize).val) = some ((bytes input).take (0#usize).val) := by
  simp [toks, LZ77.decode]
theorem valid_of_decode {input : Slice Std.U8} {o : Slice Std.U32} {t p : Std.Usize}
    (hde : LZ77.decode (toks o t.val) = some ((bytes input).take p.val)) (hp : p.val = input.length) :
    LZ77.Valid (bytes input) (toks o t.val) := by
  unfold LZ77.Valid
  rw [hde, hp]
  simp
theorem ite_prod_spec {α β : Type} (c : Prop) [Decidable c] (A B : Result (α × β))
    (hA : c → A ⦃ fun _ => True ⦄) (hB : ¬c → B ⦃ fun _ => True ⦄) :
    (if c then A else B) ⦃ fun _ => True ⦄ := T1!
theorem ite_true_spec {α : Type} (c : Prop) [Decidable c] (A B : Result α)
    (hA : c → A ⦃ fun _ => True ⦄) (hB : ¬c → B ⦃ fun _ => True ⦄) :
    (if c then A else B) ⦃ fun _ => True ⦄ := T1!
@[local step]
theorem x_ld4_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.y_x_ld4 input p ⦃ fun _ => True ⦄ := T2! slot.y_x_ld4
@[local step]
theorem x_ld8_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.y_x_ld8 input p ⦃ fun _ => True ⦄ := T2! slot.y_x_ld8
@[local step]
theorem x_first_diff_spec (x : Std.U64) :
    slot.y_x_first_diff x ⦃ fun _ => True ⦄ := T2! slot.y_x_first_diff
@[local step]
theorem x_fast_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) (l : Std.Usize) (go : Std.Usize) (it : Std.Usize)  :
    slot.y_x_fast_len_loop input a b cap l go it ⦃ fun _ => True ⦄ := T3! slot.y_x_fast_len_loop slot.y_x_fast_len_loop.body
@[local step]
theorem x_fast_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) :
    slot.y_x_fast_len input a b cap ⦃ fun _ => True ⦄ := T4! slot.y_x_fast_len
@[local step]
theorem x_hashp_spec (input : Slice Std.U8) (p : Std.Usize) (hs : Std.U32) :
    slot.y_x_hashp input p hs ⦃ fun _ => True ⦄ := T2! slot.y_x_hashp
@[local step]
theorem x_hash3_spec (w : Std.U32) :
    slot.y_x_hash3 w ⦃ fun _ => True ⦄ := T2! slot.y_x_hash3
@[local step]
theorem x_dextra_spec (d : Std.Usize) :
    slot.y_x_dextra d ⦃ fun _ => True ⦄ := T2! slot.y_x_dextra
@[local step]
theorem x_lextra_spec (l : Std.Usize) :
    slot.y_x_lextra l ⦃ fun _ => True ⦄ := T2! slot.y_x_lextra
@[local step]
theorem x_score_spec (l : Std.Usize) (d : Std.Usize) (cq : Std.Usize) :
    slot.y_x_score l d cq ⦃ fun _ => True ⦄ := T2! slot.y_x_score
@[local step]
theorem x_lg8_spec (x : Std.U32) :
    slot.y_x_lg8 x ⦃ fun _ => True ⦄ := T2! slot.y_x_lg8
@[local step]
theorem x_sample_loop_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) (n : Std.Usize) (st : Std.Usize) (k : Std.Usize) (c : Std.Usize) (hn : n.val = input.length) :
    slot.y_x_sample_loop input h n st k c ⦃ fun _ => True ⦄ := T5! slot.y_x_sample_loop slot.y_x_sample_loop.body
@[local step]
theorem x_sample_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) :
    slot.y_x_sample input h ⦃ fun _ => True ⦄ := T4! slot.y_x_sample
@[local step]
theorem x_entropy256_loop_spec (h : Array Std.U32 256#usize) (tot : Std.U64) (acc : Std.U64) (i : Std.Usize)  :
    slot.y_x_entropy256_loop h tot acc i ⦃ fun _ => True ⦄ := T6! slot.y_x_entropy256_loop slot.y_x_entropy256_loop.body
@[local step]
theorem x_entropy256_spec (h : Array Std.U32 256#usize) :
    slot.y_x_entropy256 h ⦃ fun _ => True ⦄ := T4! slot.y_x_entropy256
@[local step]
theorem x_share_loop_spec (h : Array Std.U32 256#usize) (lo : Std.Usize) (hi : Std.Usize) (t : Std.Usize) (s : Std.Usize) (i : Std.Usize)  :
    slot.y_x_share_loop h lo hi t s i ⦃ fun _ => True ⦄ := T6! slot.y_x_share_loop slot.y_x_share_loop.body
@[local step]
theorem x_share_spec (h : Array Std.U32 256#usize) (lo : Std.Usize) (hi : Std.Usize) :
    slot.y_x_share h lo hi ⦃ fun _ => True ⦄ := T2! slot.y_x_share
@[local step]
theorem x_low_mode_spec (e : Std.Usize) :
    slot.y_x_low_mode e ⦃ fun _ => True ⦄ := T4! slot.y_x_low_mode
@[local step]
theorem x_lit_cost_spec (e : Std.Usize) (low : Std.Usize) :
    slot.y_x_lit_cost e low ⦃ fun _ => True ⦄ := T2! slot.y_x_lit_cost
@[local step]
theorem x_m3_mode_spec (h : Array Std.U32 256#usize) (e : Std.Usize) :
    slot.y_x_m3_mode h e ⦃ fun _ => True ⦄ := T4! slot.y_x_m3_mode
@[local step]
theorem x_h3_mode_spec (h : Array Std.U32 256#usize) (e : Std.Usize) :
    slot.y_x_h3_mode h e ⦃ fun _ => True ⦄ := T2! slot.y_x_h3_mode
@[local step]
theorem x_numeric_spec (h : Array Std.U32 256#usize) (n : Std.Usize) (low : Std.Usize) :
    slot.y_x_numeric h n low ⦃ fun _ => True ⦄ := T2! slot.y_x_numeric
@[local step]
theorem x_walk_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (cap : Std.Usize) (probes : Std.Usize) (litq : Std.Usize) (lim : Std.Usize) (stop : Std.Usize) (cur : Std.Usize) (k : Std.Usize) (bl : Std.Usize) (bs : Std.Usize) (bd : Std.Usize) (off : Std.Usize) (want : Std.U32)  :
    slot.y_x_walk_loop input prev pos cap probes litq lim stop cur k bl bs bd off want ⦃ fun _ => True ⦄ := T7! slot.y_x_walk_loop slot.y_x_walk_loop.body
@[local step]
theorem x_walk_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (start : Std.Usize) (cap : Std.Usize) (probes : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) :
    slot.y_x_walk input prev pos start cap probes bl0 bs0 litq ⦃ fun _ => True ⦄ := T2! slot.y_x_walk
@[local step]
theorem x_lwalk_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (cap : Std.Usize) (probes : Std.Usize) (litq : Std.Usize) (lim : Std.Usize) (stop : Std.Usize) (cur : Std.Usize) (k : Std.Usize) (bl : Std.Usize) (bs : Std.Usize) (bd : Std.Usize) (off : Std.Usize) (want : Std.U32)  :
    slot.y_x_lwalk_loop input prev pos cap probes litq lim stop cur k bl bs bd off want ⦃ fun _ => True ⦄ := T7! slot.y_x_lwalk_loop slot.y_x_lwalk_loop.body
@[local step]
theorem x_lwalk_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (start : Std.Usize) (cap : Std.Usize) (probes : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) :
    slot.y_x_lwalk input prev pos start cap probes bl0 bs0 litq ⦃ fun _ => True ⦄ := T2! slot.y_x_lwalk
@[local step]
theorem x_cand3_spec (input : Slice Std.U8) (pos : Std.Usize) (s3 : Std.Usize) (cap : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) :
    slot.y_x_cand3 input pos s3 cap bs0 litq ⦃ fun _ => True ⦄ := T2! slot.y_x_cand3
@[local step]
theorem x_upd3_spec (input : Slice Std.U8) (head3 : Array Std.U32 16384#usize) (pos : Std.Usize) (on : Std.Usize) :
    slot.y_x_upd3 input head3 pos on ⦃ fun _ => True ⦄ := T2! slot.y_x_upd3
@[local step]
theorem x_search_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (head3 : Array Std.U32 16384#usize) (pos : Std.Usize) (probes : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) (hs : Std.U32) (h3on : Std.Usize) :
    slot.y_x_search input head prev head3 pos probes bl0 bs0 litq hs h3on ⦃ fun _ => True ⦄ := T2! slot.y_x_search
@[local step]
theorem x_insert_range_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («to» : Std.Usize) (hs : Std.U32) (lim : Std.Usize) (p : Std.Usize)  :
    slot.y_x_insert_range_loop input head prev «to» hs lim p ⦃ fun _ => True ⦄ := T8! slot.y_x_insert_range_loop slot.y_x_insert_range_loop.body
@[local step]
theorem x_insert_range_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («from» : Std.Usize) («to» : Std.Usize) (hs : Std.U32) :
    slot.y_x_insert_range input head prev «from» «to» hs ⦃ fun _ => True ⦄ := T2! slot.y_x_insert_range
@[local step]
theorem x_insert_range3_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (head3 : Array Std.U32 16384#usize) («to» : Std.Usize) (hs : Std.U32) (lim : Std.Usize) (p : Std.Usize)  :
    slot.y_x_insert_range3_loop input head prev head3 «to» hs lim p ⦃ fun _ => True ⦄ := T9! slot.y_x_insert_range3_loop slot.y_x_insert_range3_loop.body
@[local step]
theorem x_insert_range3_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (head3 : Array Std.U32 16384#usize) («from» : Std.Usize) («to» : Std.Usize) (hs : Std.U32) :
    slot.y_x_insert_range3 input head prev head3 «from» «to» hs ⦃ fun _ => True ⦄ := T2! slot.y_x_insert_range3
@[local step]
theorem x_insert_match_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (head3 : Array Std.U32 16384#usize) («from» : Std.Usize) («to» : Std.Usize) (hs : Std.U32) (h3on : Std.Usize) :
    slot.y_x_insert_match input head prev head3 «from» «to» hs h3on ⦃ fun _ => True ⦄ := T2! slot.y_x_insert_match
def w8 (input : Slice Std.U8) (p : Nat) : Nat :=
  (input.val[p]!).val + (input.val[p + 1]!).val * 256 + (input.val[p + 2]!).val * 65536 +
  (input.val[p + 3]!).val * 16777216 + (input.val[p + 4]!).val * 4294967296 +
  (input.val[p + 5]!).val * 1099511627776 + (input.val[p + 6]!).val * 281474976710656 +
  (input.val[p + 7]!).val * 72057594037927936
def w4 (input : Slice Std.U8) (p : Nat) : Nat :=
  (input.val[p]!).val + (input.val[p + 1]!).val * 256 + (input.val[p + 2]!).val * 65536 +
  (input.val[p + 3]!).val * 16777216
theorem w8_bytes (input : Slice Std.U8) (p q : Nat) (h : w8 input p = w8 input q) :
    ∀ k, k < 8 → input.val[q + k]! = input.val[p + k]! := T10!
theorem w4_bytes (input : Slice Std.U8) (p q : Nat) (h : w4 input p = w4 input q) :
    ∀ k, k < 4 → input.val[q + k]! = input.val[p + k]! := T11!
theorem Matches.add8 {input : Slice Std.U8} {a b l : Nat} (h : Matches input a b l)
    (hw : w8 input (a + l) = w8 input (b + l)) : Matches input a b (l + 8) := T12!
theorem Matches.tail8 {input : Slice Std.U8} {a b l c : Nat} (h : Matches input a b l)
    (hc : 8 ≤ c) (hl : c ≤ l + 8)
    (hw : w8 input (a + (c - 8)) = w8 input (b + (c - 8))) : Matches input a b c := T13!
theorem Matches.two4 {input : Slice Std.U8} {a b c : Nat}
    (hc : 4 ≤ c) (hc8 : c < 8) (hw0 : w4 input a = w4 input b)
    (hw1 : w4 input (a + (c - 4)) = w4 input (b + (c - 4))) : Matches input a b c := T14!
@[local step]
theorem x_tw8_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 8 ≤ input.length) :
    slot.y_x_tw8 input p ⦃ fun r => r.val = w8 input p.val ⦄ := T15! slot.y_x_tw8
@[local step]
theorem x_tw4_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 4 ≤ input.length) :
    slot.y_x_tw4 input p ⦃ fun r => r.val = w4 input p.val ⦄ := T16! slot.y_x_tw4
theorem x_words_eq_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.y_x_words_eq_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := T17! slot.y_x_words_eq_loop slot.y_x_words_eq_loop.body
@[local step]
theorem x_tail_eq_spec (input : Slice Std.U8) (a b cap l : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) (hl : l.val ≤ cap.val) :
    slot.y_x_tail_eq input a b cap l ⦃ fun r => r.val = 1 →
      8 ≤ cap.val ∧ cap.val ≤ l.val + 8 ∧
      w8 input (a.val + (cap.val - 8)) = w8 input (b.val + (cap.val - 8)) ⦄ := T18! slot.y_x_tail_eq
@[local step]
theorem x_short_eq_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.y_x_short_eq input a b cap ⦃ fun r => r.val = 1 →
      4 ≤ cap.val ∧ cap.val < 8 ∧ w4 input a.val = w4 input b.val ∧
      w4 input (a.val + (cap.val - 4)) = w4 input (b.val + (cap.val - 4)) ⦄ := T19! slot.y_x_short_eq
@[local step]
theorem x_words_eq_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.y_x_words_eq input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.y_x_words_eq]
  apply Std.WP.spec_bind (x_words_eq_loop_spec input a b cap 0#usize ha hb (by scalar_tac)
    (LZ77.Matches.zero input a.val b.val))
  rintro l ⟨hle, hm⟩
  apply Std.WP.spec_bind (x_tail_eq_spec input a b cap l ha hb hle)
  rintro big hbig
  apply Std.WP.spec_bind (x_short_eq_spec input a b cap ha hb)
  rintro small hsmall
  split
  · have h1 : big.val = 1 := by scalar_tac
    obtain ⟨h8, hcl, hw⟩ := hbig h1
    simp only [Std.WP.spec_ok]
    exact ⟨le_refl _, Matches.tail8 hm h8 hcl hw⟩
  · split
    · have h1 : small.val = 1 := by scalar_tac
      obtain ⟨h4, h8, hw0, hw1⟩ := hsmall h1
      simp only [Std.WP.spec_ok]
      exact ⟨le_refl _, Matches.two4 h4 h8 hw0 hw1⟩
    · simp only [Std.WP.spec_ok]
      exact ⟨hle, hm⟩
theorem x_match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.y_x_match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := T23! slot.y_x_match_len_loop slot.y_x_match_len_loop.body
@[local step]
theorem x_match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.y_x_match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.y_x_match_len]
  apply Std.WP.spec_bind (x_words_eq_spec input a b cap ha hb)
  rintro l0 ⟨hle, hm⟩
  exact x_match_len_loop_spec input a b cap l0 ha hb hle hm
theorem x_verified_spec (input : Slice Std.U8) (pos d ch : Std.Usize) :
    slot.y_x_verified input pos d ch ⦃ fun b => b = true →
      3 ≤ ch.val ∧ ch.val ≤ 258 ∧ 1 ≤ d.val ∧ d.val ≤ 32768 ∧ d.val ≤ pos.val ∧
      pos.val + ch.val ≤ input.length ∧ Matches input (pos.val - d.val) pos.val ch.val ⦄ := T21! slot.y_x_verified
theorem x_emit_lits_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (n cnt1 k0 c0 ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ n.val) (hntok : ntok0.val ≤ k0.val) (hc0 : c0.val = 0)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take k0.val)) :
    slot.y_x_emit_lits_loop input out0 n cnt1 k0 c0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ (k0.val < r.2.1.val ∨ cnt1.val = 0 ∨ k0.val = n.val) ∧
      r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := T22! slot.y_x_emit_lits_loop slot.y_x_emit_lits_loop.body
@[local step]
theorem x_emit_lits_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos0 cnt ntok0 : Std.Usize)
    (hout : input.length ≤ out.length) (hpos : pos0.val ≤ input.length)
    (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.y_x_emit_lits input out pos0 cnt ntok0 ⦃ fun r =>
      (pos0.val < r.1.2.val ∨ pos0.val = input.length) ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.y_x_emit_lits]
  apply Std.WP.spec_bind (Pₘ := fun (c : Std.Usize) => 1 ≤ c.val)
  · split <;> simp only [Std.WP.spec_ok] <;> scalar_tac
  intro cnt1 hc1
  apply Std.WP.spec_bind (x_emit_lits_loop_spec input out _ cnt1 pos0 0#usize ntok0
    (by simp) hout (by scalar_tac) hntok (by simp) hdec)
  rintro ⟨out1, k, ntok⟩ ⟨h1, h2, h3, h4, h5⟩
  simp only at h1 h2 h3 h4 h5
  step*
  all_goals exact ⟨by scalar_tac, by scalar_tac, h3, h4, h5⟩
@[local step]
theorem x_emit_step_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos d l lits ntok : Std.Usize)
    (hout : input.length ≤ out.length) (hpos : pos.val < input.length)
    (hntok : ntok.val ≤ pos.val)
    (hdec : LZ77.decode (toks out ntok.val) = some ((bytes input).take pos.val)) :
    slot.y_x_emit_step input out pos d l lits ntok ⦃ fun r =>
      pos.val < r.1.2.val ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.y_x_emit_step]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (x_verified_spec input pos d l)
  intro b hb
  split
  case isTrue hbt =>
    obtain ⟨hl3, hl258, hd1, hdmax, hdpos, hend, hmatch⟩ := hb hbt
    have hntok_lt : ntok.val < out.length := by scalar_tac
    step*
    have htok : i6.val = LZ77.mkMatch d.val l.val := by
      simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i6_post, i3_post, i2_post]
      scalar_tac
    refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
      by rw [out1_post]; simp [Std.Slice.set_val_eq], ?_⟩
    rw [out1_post, show i7.val = ntok.val + 1 by scalar_tac,
      show i8.val = pos.val + l.val by scalar_tac]
    exact emit_match input out ntok pos.val d.val l.val i6 hdec hntok_lt hd1 hdpos hdmax
      hl3 hl258 hend hmatch htok
  case isFalse hbf =>
    apply Std.WP.spec_mono (x_emit_lits_spec input out pos lits ntok hout (by scalar_tac) hntok hdec)
    rintro ⟨⟨t, k⟩, o⟩ ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by scalar_tac, h2, h3, h4, h5⟩
@[local step]
theorem x_lazy_probe_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (head3 : Array Std.U32 16384#usize) (q : Std.Usize) (go : Std.Usize) (p2 : Std.Usize) (l1 : Std.Usize) (sv1 : Std.Usize) (litq : Std.Usize) (hs : Std.U32) (h3on : Std.Usize) :
    slot.y_x_lazy_probe input head prev head3 q go p2 l1 sv1 litq hs h3on ⦃ fun _ => True ⦄ := T2! slot.y_x_lazy_probe
@[local step]
theorem x_ext_ok_spec (input : Slice Std.U8) (pos : Std.Usize) (l2 : Std.Usize) (d2 : Std.Usize) :
    slot.y_x_ext_ok input pos l2 d2 ⦃ fun _ => True ⦄ := T4! slot.y_x_ext_ok
@[local step]
theorem x_fl_tw8_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 8 ≤ input.length) :
    slot.y_x_fl_tw8 input p ⦃ fun r => r.val = w8 input p.val ⦄ := T15! slot.y_x_fl_tw8
@[local step]
theorem x_fl_tw4_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 4 ≤ input.length) :
    slot.y_x_fl_tw4 input p ⦃ fun r => r.val = w4 input p.val ⦄ := T16! slot.y_x_fl_tw4
theorem x_fl_words_eq_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.y_x_fl_words_eq_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := T17! slot.y_x_fl_words_eq_loop slot.y_x_fl_words_eq_loop.body
@[local step]
theorem x_fl_tail_eq_spec (input : Slice Std.U8) (a b cap l : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) (hl : l.val ≤ cap.val) :
    slot.y_x_fl_tail_eq input a b cap l ⦃ fun r => r.val = 1 →
      8 ≤ cap.val ∧ cap.val ≤ l.val + 8 ∧
      w8 input (a.val + (cap.val - 8)) = w8 input (b.val + (cap.val - 8)) ⦄ := T18! slot.y_x_fl_tail_eq
@[local step]
theorem x_fl_short_eq_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.y_x_fl_short_eq input a b cap ⦃ fun r => r.val = 1 →
      4 ≤ cap.val ∧ cap.val < 8 ∧ w4 input a.val = w4 input b.val ∧
      w4 input (a.val + (cap.val - 4)) = w4 input (b.val + (cap.val - 4)) ⦄ := T19! slot.y_x_fl_short_eq
@[local step]
theorem x_fl_words_eq_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.y_x_fl_words_eq input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.y_x_fl_words_eq]
  apply Std.WP.spec_bind (x_fl_words_eq_loop_spec input a b cap 0#usize ha hb (by scalar_tac)
    (LZ77.Matches.zero input a.val b.val))
  rintro l ⟨hle, hm⟩
  apply Std.WP.spec_bind (x_fl_tail_eq_spec input a b cap l ha hb hle)
  rintro big hbig
  apply Std.WP.spec_bind (x_fl_short_eq_spec input a b cap ha hb)
  rintro small hsmall
  split
  · have h1 : big.val = 1 := by scalar_tac
    obtain ⟨h8, hcl, hw⟩ := hbig h1
    simp only [Std.WP.spec_ok]
    exact ⟨le_refl _, Matches.tail8 hm h8 hcl hw⟩
  · split
    · have h1 : small.val = 1 := by scalar_tac
      obtain ⟨h4, h8, hw0, hw1⟩ := hsmall h1
      simp only [Std.WP.spec_ok]
      exact ⟨le_refl _, Matches.two4 h4 h8 hw0 hw1⟩
    · simp only [Std.WP.spec_ok]
      exact ⟨hle, hm⟩
theorem x_fl_match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.y_x_fl_match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := T23! slot.y_x_fl_match_len_loop slot.y_x_fl_match_len_loop.body
@[local step]
theorem x_fl_match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.y_x_fl_match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.y_x_fl_match_len]
  apply Std.WP.spec_bind (x_fl_words_eq_spec input a b cap ha hb)
  rintro l0 ⟨hle, hm⟩
  exact x_fl_match_len_loop_spec input a b cap l0 ha hb hle hm
theorem x_fl_verified_spec (input : Slice Std.U8) (pos d ch : Std.Usize) :
    slot.y_x_fl_verified input pos d ch ⦃ fun b => b = true →
      3 ≤ ch.val ∧ ch.val ≤ 258 ∧ 1 ≤ d.val ∧ d.val ≤ 32768 ∧ d.val ≤ pos.val ∧
      pos.val + ch.val ≤ input.length ∧ Matches input (pos.val - d.val) pos.val ch.val ⦄ := T21! slot.y_x_fl_verified
theorem x_fl_emit_lits_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (n cnt1 k0 c0 ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ n.val) (hntok : ntok0.val ≤ k0.val) (hc0 : c0.val = 0)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take k0.val)) :
    slot.y_x_fl_emit_lits_loop input out0 n cnt1 k0 c0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ (k0.val < r.2.1.val ∨ cnt1.val = 0 ∨ k0.val = n.val) ∧
      r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := T22! slot.y_x_fl_emit_lits_loop slot.y_x_fl_emit_lits_loop.body
@[local step]
theorem x_fl_emit_lits_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos0 cnt ntok0 : Std.Usize)
    (hout : input.length ≤ out.length) (hpos : pos0.val ≤ input.length)
    (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.y_x_fl_emit_lits input out pos0 cnt ntok0 ⦃ fun r =>
      (pos0.val < r.1.2.val ∨ pos0.val = input.length) ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.y_x_fl_emit_lits]
  apply Std.WP.spec_bind (Pₘ := fun (c : Std.Usize) => 1 ≤ c.val)
  · split <;> simp only [Std.WP.spec_ok] <;> scalar_tac
  intro cnt1 hc1
  apply Std.WP.spec_bind (x_fl_emit_lits_loop_spec input out _ cnt1 pos0 0#usize ntok0
    (by simp) hout (by scalar_tac) hntok (by simp) hdec)
  rintro ⟨out1, k, ntok⟩ ⟨h1, h2, h3, h4, h5⟩
  simp only at h1 h2 h3 h4 h5
  step*
  all_goals exact ⟨by scalar_tac, by scalar_tac, h3, h4, h5⟩
@[local step]
theorem x_fl_emit_step_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos d l lits ntok : Std.Usize)
    (hout : input.length ≤ out.length) (hpos : pos.val < input.length)
    (hntok : ntok.val ≤ pos.val)
    (hdec : LZ77.decode (toks out ntok.val) = some ((bytes input).take pos.val)) :
    slot.y_x_fl_emit_step input out pos d l lits ntok ⦃ fun r =>
      pos.val < r.1.2.val ∧ r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧
      r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := by
  rw [slot.y_x_fl_emit_step]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (x_fl_verified_spec input pos d l)
  intro b hb
  split
  case isTrue hbt =>
    obtain ⟨hl3, hl258, hd1, hdmax, hdpos, hend, hmatch⟩ := hb hbt
    have hntok_lt : ntok.val < out.length := by scalar_tac
    step*
    have htok : i6.val = LZ77.mkMatch d.val l.val := by
      simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i6_post, i3_post, i2_post]
      scalar_tac
    refine ⟨by scalar_tac, by scalar_tac, by scalar_tac,
      by rw [out1_post]; simp [Std.Slice.set_val_eq], ?_⟩
    rw [out1_post, show i7.val = ntok.val + 1 by scalar_tac,
      show i8.val = pos.val + l.val by scalar_tac]
    exact emit_match input out ntok pos.val d.val l.val i6 hdec hntok_lt hd1 hdpos hdmax
      hl3 hl258 hend hmatch htok
  case isFalse hbf =>
    apply Std.WP.spec_mono (x_fl_emit_lits_spec input out pos lits ntok hout (by scalar_tac) hntok hdec)
    rintro ⟨⟨t, k⟩, o⟩ ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by scalar_tac, h2, h3, h4, h5⟩
@[local step]
theorem x_fl_byte_spec (input : Slice Std.U8) (i : Std.Usize) :
    slot.y_x_fl_byte input i ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_byte
@[local step]
theorem x_fl_ld4_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.y_x_fl_ld4 input p ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_ld4
@[local step]
theorem x_fl_ld8_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.y_x_fl_ld8 input p ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_ld8
@[local step]
theorem x_fl_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) (l : Std.Usize) (go : Std.Usize) (it : Std.Usize)  :
    slot.y_x_fl_len_loop input a b cap l go it ⦃ fun _ => True ⦄ := T3! slot.y_x_fl_len_loop slot.y_x_fl_len_loop.body
@[local step]
theorem x_fl_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) :
    slot.y_x_fl_len input a b cap ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_len
@[local step]
theorem x_fl_hashp_spec (input : Slice Std.U8) (p : Std.Usize) (hsh : Std.U64) :
    slot.y_x_fl_hashp input p hsh ⦃ fun r => r.val < 65536 ⦄ := T2! slot.y_x_fl_hashp
@[local step]
theorem x_fl_log16_spec (f : Std.U32) :
    slot.y_x_fl_log16 f ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_log16
@[local step]
theorem x_fl_sample_loop_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) (n : Std.Usize) (st : Std.Usize) (k : Std.Usize) (c : Std.Usize) (hn : n.val = input.length) :
    slot.y_x_fl_sample_loop input h n st k c ⦃ fun _ => True ⦄ := T5! slot.y_x_fl_sample_loop slot.y_x_fl_sample_loop.body
@[local step]
theorem x_fl_sample_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) :
    slot.y_x_fl_sample input h ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_sample
@[local step]
theorem x_fl_costs_loop0_spec (h : Array Std.U32 256#usize) (t : Std.U32) (i : Std.Usize)  :
    slot.y_x_fl_costs_loop0 h t i ⦃ fun _ => True ⦄ := T24! slot.y_x_fl_costs_loop0 slot.y_x_fl_costs_loop0.body
@[local step]
theorem x_fl_costs_loop1_spec (h : Array Std.U32 256#usize) (cost : Array Std.U32 256#usize) (lt : Std.U32) (j : Std.Usize)  :
    slot.y_x_fl_costs_loop1 h cost lt j ⦃ fun _ => True ⦄ := T24! slot.y_x_fl_costs_loop1 slot.y_x_fl_costs_loop1.body
@[local step]
theorem x_fl_costs_spec (h : Array Std.U32 256#usize) (cost : Array Std.U32 256#usize) :
    slot.y_x_fl_costs h cost ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_costs
@[local step]
theorem x_fl_ent_loop0_spec (h : Array Std.U32 1024#usize) (base : Std.Usize) (t : Std.U32) (i : Std.Usize)  :
    slot.y_x_fl_ent_loop0 h base t i ⦃ fun _ => True ⦄ := T24! slot.y_x_fl_ent_loop0 slot.y_x_fl_ent_loop0.body
@[local step]
theorem x_fl_ent_loop1_spec (h : Array Std.U32 1024#usize) (base : Std.Usize) (lt : Std.U32) (bits : Std.Usize) (j : Std.Usize)  :
    slot.y_x_fl_ent_loop1 h base lt bits j ⦃ fun _ => True ⦄ := T24! slot.y_x_fl_ent_loop1 slot.y_x_fl_ent_loop1.body
@[local step]
theorem x_fl_ent_spec (h : Array Std.U32 1024#usize) (base : Std.Usize) :
    slot.y_x_fl_ent h base ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_ent
@[local step]
theorem x_fl_stats_loop0_spec (h : Array Std.U32 256#usize) (t : Std.U32) (i : Std.Usize)  :
    slot.y_x_fl_stats_loop0 h t i ⦃ fun _ => True ⦄ := T24! slot.y_x_fl_stats_loop0 slot.y_x_fl_stats_loop0.body
@[local step]
theorem x_fl_stats_loop1_spec (h : Array Std.U32 256#usize) (t : Std.U32) (lt : Std.U32) (bits : Std.Usize) (top : Std.U32) (np : Std.Usize) (big : Std.Usize) (bigsum : Std.Usize) (j : Std.Usize)  :
    slot.y_x_fl_stats_loop1 h t lt bits top np big bigsum j ⦃ fun _ => True ⦄ := T25! slot.y_x_fl_stats_loop1 slot.y_x_fl_stats_loop1.body
@[local step]
theorem x_fl_stats_spec (h : Array Std.U32 256#usize) :
    slot.y_x_fl_stats h ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_stats
@[local step]
theorem x_fl_probe_chunk_loop_spec (input : Slice Std.U8) (tab : Array Std.U32 4096#usize) (ph : Array Std.U32 1024#usize) (s : Std.Usize) (p : Std.Usize) (k : Std.Usize) (c4 : Std.Usize)  :
    slot.y_x_fl_probe_chunk_loop input tab ph s p k c4 ⦃ fun _ => True ⦄ := T26! slot.y_x_fl_probe_chunk_loop slot.Y_X_FL_PCH.val slot.y_x_fl_probe_chunk_loop.body
@[local step]
theorem x_fl_weights_loop_spec (input : Slice Std.U8) (tab : Array Std.U32 4096#usize) (ph : Array Std.U32 1024#usize) (span : Std.Usize) (c4 : Std.Usize) (i : Std.Usize)  :
    slot.y_x_fl_weights_loop input tab ph span c4 i ⦃ fun _ => True ⦄ := by
  rw [slot.y_x_fl_weights_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.Y_X_FL_PNC.val - s.2.2.2.val)
    (inv := fun s => True)
  · rintro ⟨x0, x1, x2, x3⟩ _
    simp only [slot.y_x_fl_weights_loop.body, lift, Array.to_slice_mut]
    step*
    repeat (first
      | (intro hc; (try step*))
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5, r6⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem x_fl_weights_spec (input : Slice Std.U8) :
    slot.y_x_fl_weights input ⦃ fun _ => True ⦄ := T27! slot.y_x_fl_weights
@[local step]
theorem x_fl_mode_spec (input : Slice Std.U8) (st : Std.U64) :
    slot.y_x_fl_mode input st ⦃ fun _ => True ⦄ := T27! slot.y_x_fl_mode
@[local step]
theorem x_fl_config_spec («class» : Std.Usize) (cf : Array Std.Usize 8#usize) :
    slot.y_x_fl_config «class» cf ⦃ fun _ => True ⦄ := T27! slot.y_x_fl_config
section
attribute [local step] ite_true_spec
@[local step]
theorem x_fl_lit_parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.y_x_fl_lit_parse input out ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := T28! slot.y_x_fl_lit_parse
end
attribute [local step] x_fl_lit_parse_spec
section
attribute [local step] ite_true_spec
@[local step]
theorem x_fl_rle_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize) (pos0 : Std.Usize) (ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.y_x_fl_rle_parse_loop input out0 n pos0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := T29! slot.y_x_fl_rle_parse_loop slot.y_x_fl_rle_parse_loop.body
end
attribute [local step] x_fl_rle_parse_loop_spec
section
attribute [local step] ite_true_spec
@[local step]
theorem x_fl_rle_parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.y_x_fl_rle_parse input out ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := T28! slot.y_x_fl_rle_parse
end
attribute [local step] x_fl_rle_parse_spec
@[local step]
theorem x_fl_cheap_run_loop_spec (input : Slice Std.U8) (cost : Array Std.U32 256#usize) (n : Std.Usize) (k : Std.Usize) (hn : n.val = input.length) :
    slot.y_x_fl_cheap_run_loop input cost n k ⦃ fun _ => True ⦄ := T30! slot.y_x_fl_cheap_run_loop slot.y_x_fl_cheap_run_loop.body
@[local step]
theorem x_fl_cheap_run_spec (input : Slice Std.U8) (cost : Array Std.U32 256#usize) (pos : Std.Usize) :
    slot.y_x_fl_cheap_run input cost pos ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_cheap_run
@[local step]
theorem x_fl_span_cost_loop_spec (input : Slice Std.U8) (cost : Array Std.U32 256#usize) (pos : Std.Usize) (l : Std.Usize) (s : Std.Usize) (i : Std.Usize)  :
    slot.y_x_fl_span_cost_loop input cost pos l s i ⦃ fun _ => True ⦄ := T31! slot.y_x_fl_span_cost_loop slot.y_x_fl_span_cost_loop.body
@[local step]
theorem x_fl_dextra_spec (d : Std.Usize) :
    slot.y_x_fl_dextra d ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_dextra
@[local step]
theorem x_fl_lextra_spec (l : Std.Usize) :
    slot.y_x_fl_lextra l ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_lextra
@[local step]
theorem x_fl_dna_ok_spec (input : Slice Std.U8) (cost : Array Std.U32 256#usize) (pos : Std.Usize) (l : Std.Usize) (d : Std.Usize) :
    slot.y_x_fl_dna_ok input cost pos l d ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_dna_ok
@[local step]
theorem x_fl_dwalk_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) (bl : Std.Usize) (bd : Std.Usize) (cur : Std.Usize) (k : Std.Usize)  :
    slot.y_x_fl_dwalk_loop input prev pos cap depth bl bd cur k ⦃ fun _ => True ⦄ := T32! slot.y_x_fl_dwalk_loop slot.y_x_fl_dwalk_loop.body
@[local step]
theorem x_fl_dwalk_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (start : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) :
    slot.y_x_fl_dwalk input prev pos start cap depth ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_dwalk
@[local step]
theorem x_fl_dsearch_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (p : Std.Usize) (depth : Std.Usize) :
    slot.y_x_fl_dsearch input head prev p depth ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_dsearch
@[local step]
theorem x_fl_insert_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («to» : Std.Usize) (hsh : Std.U64) (lim : Std.Usize) (p : Std.Usize)  :
    slot.y_x_fl_insert_loop input head prev «to» hsh lim p ⦃ fun _ => True ⦄ := T8! slot.y_x_fl_insert_loop slot.y_x_fl_insert_loop.body
@[local step]
theorem x_fl_insert_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («from» : Std.Usize) («to» : Std.Usize) (hsh : Std.U64) :
    slot.y_x_fl_insert input head prev «from» «to» hsh ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_insert
section
attribute [local step] ite_true_spec
@[local step]
theorem x_fl_dna_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (cost : Array Std.U32 256#usize) (n : Std.Usize) (head0 : Array Std.U32 65536#usize) (prev0 : Array Std.U32 32768#usize) (pos0 : Std.Usize) (ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.y_x_fl_dna_parse_loop input out0 cost n head0 prev0 pos0 ntok0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := T33! slot.y_x_fl_dna_parse_loop slot.y_x_fl_dna_parse_loop.body
end
attribute [local step] x_fl_dna_parse_loop_spec
section
attribute [local step] ite_true_spec
@[local step]
theorem x_fl_dna_parse_spec (input : Slice Std.U8) (out : Slice Std.U32) (cost : Array Std.U32 256#usize)
    (hlen : input.length ≤ out.length) :
    slot.y_x_fl_dna_parse input out cost ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := T28! slot.y_x_fl_dna_parse
end
attribute [local step] x_fl_dna_parse_spec
@[local step]
theorem x_fl_score_spec (l : Std.Usize) (d : Std.Usize) (litq : Std.Usize) :
    slot.y_x_fl_score l d litq ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_score
@[local step]
theorem x_fl_lg8_spec (x : Std.U32) :
    slot.y_x_fl_lg8 x ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_lg8
@[local step]
theorem x_fl_entropy256_loop_spec (h : Array Std.U32 256#usize) (tot : Std.U64) (acc : Std.U64) (i : Std.Usize)  :
    slot.y_x_fl_entropy256_loop h tot acc i ⦃ fun _ => True ⦄ := T6! slot.y_x_fl_entropy256_loop slot.y_x_fl_entropy256_loop.body
@[local step]
theorem x_fl_entropy256_spec (h : Array Std.U32 256#usize) :
    slot.y_x_fl_entropy256 h ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_entropy256
@[local step]
theorem x_fl_lit_cost_spec (h0 : Std.Usize) :
    slot.y_x_fl_lit_cost h0 ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_lit_cost
@[local step]
theorem x_fl_walk_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) (litq : Std.Usize) (nice : Std.Usize) (bl : Std.Usize) (bd : Std.Usize) (bs : Std.Usize) (cur : Std.Usize) (k : Std.Usize) (off : Std.Usize) (want : Std.U32)  :
    slot.y_x_fl_walk_loop input prev pos cap depth litq nice bl bd bs cur k off want ⦃ fun _ => True ⦄ := T34! slot.y_x_fl_walk_loop slot.y_x_fl_walk_loop.body
@[local step]
theorem x_fl_walk_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (start : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) (nice : Std.Usize) :
    slot.y_x_fl_walk input prev pos start cap depth bl0 bs0 litq nice ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_walk
@[local step]
theorem x_fl_search_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) (pos : Std.Usize) (depth : Std.Usize) (ins : Std.Usize) (bl0 : Std.Usize) (bs0 : Std.Usize) (litq : Std.Usize) (hsh : Std.U64) (nice : Std.Usize) :
    slot.y_x_fl_search input head prev pos depth ins bl0 bs0 litq hsh nice ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_search
@[local step]
theorem x_fl_insert_match_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U32 32768#usize) («from» : Std.Usize) («to» : Std.Usize) (hsh : Std.U64) (ih : Std.Usize) (it : Std.Usize) :
    slot.y_x_fl_insert_match input head prev «from» «to» hsh ih it ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_insert_match
@[local step]
theorem x_fl_lits_spec (miss : Std.Usize) (acc : Std.Usize) :
    slot.y_x_fl_lits miss acc ⦃ fun _ => True ⦄ := T2! slot.y_x_fl_lits
@[local step]
theorem x_fl_litq_spec (h0 : Std.Usize) :
    slot.y_x_fl_litq h0 ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_litq
@[local step]
theorem x_fl_hsh_spec (h0 : Std.Usize) :
    slot.y_x_fl_hsh h0 ⦃ fun _ => True ⦄ := T4! slot.y_x_fl_hsh
section
attribute [local step] ite_true_spec
@[local step]
theorem x_fl_lazy_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize) (depth : Std.Usize) (depth2 : Std.Usize) (lazy : Std.Usize) (nice : Std.Usize) (ih : Std.Usize) (it : Std.Usize) (acc : Std.Usize) (litq : Std.Usize) (hsh : Std.U64) (head0 : Array Std.U32 65536#usize) (prev0 : Array Std.U32 32768#usize) (pos0 : Std.Usize) (ntok0 : Std.Usize) (carry0 : Std.Usize) (miss0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.y_x_fl_lazy_parse_loop input out0 n depth depth2 lazy nice ih it acc litq hsh head0 prev0 pos0 ntok0 carry0 miss0 ⦃ fun r =>
      r.2.1.val ≤ n.val ∧ r.2.2.val ≤ r.2.1.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.2.val) = some ((bytes input).take r.2.1.val) ⦄ := T35! slot.y_x_fl_lazy_parse_loop slot.y_x_fl_lazy_parse_loop.body
end
attribute [local step] x_fl_lazy_parse_loop_spec
section
attribute [local step] ite_true_spec
@[local step]
theorem x_fl_lazy_parse_spec (input : Slice Std.U8) (out : Slice Std.U32) (lh : Array Std.U32 256#usize) (cf : Array Std.Usize 8#usize)
    (hlen : input.length ≤ out.length) :
    slot.y_x_fl_lazy_parse input out lh cf ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := T28! slot.y_x_fl_lazy_parse
end
attribute [local step] x_fl_lazy_parse_spec
section
attribute [local step] ite_true_spec
@[local step]
theorem x_fl_part_spec (input : Slice Std.U8) (out : Slice Std.U32) (mc : Std.Usize) (fh : Array Std.U32 256#usize)
    (hlen : input.length ≤ out.length) :
    slot.y_x_fl_part input out mc fh ⦃ fun r =>
      r.1.2.val ≤ input.length ∧ r.1.1.val ≤ r.1.2.val ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.1.val) = some ((bytes input).take r.1.2.val) ⦄ := T28! slot.y_x_fl_part
end
attribute [local step] x_fl_part_spec
section
attribute [local step] ite_true_spec
@[local step]
theorem x_main_parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize) (head0 : Array Std.U32 65536#usize) (prev0 : Array Std.U32 32768#usize) (head30 : Array Std.U32 16384#usize) (litq : Std.Usize) (hs : Std.U32) (acc : Std.U64) (depth : Std.Usize) (lz : Std.Usize) (p2 : Std.Usize) (h3on : Std.Usize) (h3i : Std.Usize) (pos0 : Std.Usize) (ntok0 : Std.Usize) (carry0 : Std.Usize) (miss0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp : pos0.val ≤ n.val) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.y_x_main_parse_loop input out0 n head0 prev0 head30 litq hs acc depth lz p2 h3on h3i pos0 ntok0 carry0 miss0 ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.y_x_main_parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.2.1.val ≤ n.val ∧ s.2.2.2.2.2.1.val ≤ s.2.2.2.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.2.1.val) = some ((bytes input).take s.2.2.2.2.1.val))
  · rintro ⟨out, head, prev, head3, pos, ntok, carry, miss⟩ ⟨hpn, hnt, hlen, hde⟩
    simp only at hpn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.y_x_main_parse_loop.body, lift, Array.to_slice_mut, alloc.vec.Vec.deref_mut, bind_tc_ok]
    split
    case isTrue hlt =>
      step*
      all_goals (repeat (first
        | (refine ⟨by scalar_tac, by scalar_tac, by assumption, by assumption, by scalar_tac⟩)
        | (intro hc; (try step*))
        | (casesm* _ × _; (try simp only []); (try step*))
        | (split <;> (try step*))
        | (step <;> (try step*))))
      all_goals (try scalar_tac)
    case isFalse hge =>
      have hpn' : pos.val = input.length := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      unfold LZ77.Valid
      rw [hde, hpn']
      simp
  · exact ⟨hp, hntok, rfl, hdec⟩
end
attribute [local step] x_main_parse_loop_spec
section
attribute [local step] ite_true_spec
@[local step]
theorem x_main_parse_spec (input : Slice Std.U8) (out : Slice Std.U32) (pos0 : Std.Usize) (ntok0 : Std.Usize)
    (hlen : input.length ≤ out.length)
    (hp : pos0.val ≤ input.length) (hntok : ntok0.val ≤ pos0.val)
    (hdec : LZ77.decode (toks out ntok0.val) = some ((bytes input).take pos0.val)) :
    slot.y_x_main_parse input out pos0 ntok0 ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := T38! slot.y_x_main_parse
end
attribute [local step] x_main_parse_spec
section
attribute [local step] ite_true_spec
@[local step]
theorem x_parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.y_x_parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := T38! slot.y_x_parse
end
attribute [local step] x_parse_spec
theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.y_parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.y_parse]
  simp only [lift, ite_ok]
  step*
@[local step]
theorem sym_cost_spec (f : Std.U32) (lt : Std.U32) :
    slot.y_sym_cost f lt ⦃ fun _ => True ⦄ := T41! slot.y_sym_cost
end EY

namespace ER
open Aeneas Aeneas.Std Result ControlFlow
open LZ77 (toks bytes bytes_getElem! emit_lit)
theorem r_window_loop_spec (input : Slice Std.U8) (st : Std.Usize) (c : Array Std.U32 8#usize)
    (n i : Std.Usize) (hn : n.val = input.length) :
    slot.r_window_loop input st c n i ⦃ fun _ => True ⦄ := by
  rw [slot.r_window_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.R_WIN.val - s.2.val)
    (inv := fun _ => True)
  · rintro ⟨c', i'⟩ -
    simp only [slot.r_window_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial

theorem r_window_spec (input : Slice Std.U8) (st : Std.Usize) (c : Array Std.U32 8#usize) :
    slot.r_window input st c ⦃ fun _ => True ⦄ := by
  rw [slot.r_window]
  exact r_window_loop_spec input st c _ _ (by simp)

theorem r_sample_loop_spec (input : Slice Std.U8) (c : Array Std.U32 8#usize) (step k : Std.Usize) :
    slot.r_sample_loop input c step k ⦃ fun _ => True ⦄ := by
  rw [slot.r_sample_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.R_NWIN.val - s.2.val)
    (inv := fun _ => True)
  · rintro ⟨c', k'⟩ -
    simp only [slot.r_sample_loop.body]
    split
    · have hw := r_window_spec
      step*
    · simp
  · trivial

theorem r_sample_spec (input : Slice Std.U8) (c : Array Std.U32 8#usize) :
    slot.r_sample input c ⦃ fun _ => True ⦄ := by
  rw [slot.r_sample]
  have hl := r_sample_loop_spec
  step*

theorem r_size_index_loop_spec (n i hit : Std.Usize) :
    slot.r_size_index_loop n i hit ⦃ fun _ => True ⦄ := by
  rw [slot.r_size_index_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.R_NSZ.val - s.1.val)
    (inv := fun _ => True)
  · rintro ⟨i', hit'⟩ -
    simp only [slot.r_size_index_loop.body]
    split
    · step*
      repeat' (split <;> step*)
      all_goals scalar_tac
    · simp
  · trivial

theorem r_size_index_spec (n : Std.Usize) : slot.r_size_index n ⦃ fun _ => True ⦄ := by
  rw [slot.r_size_index]
  exact r_size_index_loop_spec n _ _

theorem r_tie_spec (input : Slice Std.U8) (si : Std.Usize) :
    slot.r_tie input si ⦃ fun _ => True ⦄ := by
  rw [slot.r_tie]
  have hs := r_sample_spec
  step*
  repeat' (split <;> step*)

theorem r_format_spec (input : Slice Std.U8) : slot.r_format input ⦃ fun _ => True ⦄ := by
  rw [slot.r_format]
  have h1 := r_size_index_spec
  have h2 := r_tie_spec
  step*
  repeat' (split <;> step*)

theorem r_literals_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n i0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hi : i0.val ≤ n.val)
    (hdec : LZ77.decode (toks out0 i0.val) = some ((bytes input).take i0.val)) :
    slot.r_literals_loop input out0 n i0 ⦃ fun r =>
      r.length = out0.length ∧ LZ77.decode (toks r n.val) = some (bytes input) ⦄ := by
  rw [slot.r_literals_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.val)
    (inv := fun s =>
      s.2.val ≤ n.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.val) = some ((bytes input).take s.2.val))
  · rintro ⟨out, i⟩ ⟨hle, hlen, hde⟩
    simp only at hle hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.r_literals_loop.body]
    split
    case isTrue hlt =>
      step*
      have hval : i2.val = (bytes input)[i.val]! := by
        rw [bytes_getElem! input i.val (by scalar_tac), i2_post, Std.U8.cast_U32_val_eq, i1_post]
      refine ⟨by scalar_tac, by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_,
        by scalar_tac⟩
      rw [s_post, show i3.val = i.val + 1 by scalar_tac]
      exact emit_lit input out i i.val i2 hde (by scalar_tac) (by scalar_tac) hval
    case isFalse hge =>
      refine ⟨hlen, ?_⟩
      rw [show n.val = i.val by scalar_tac, hde, show i.val = (bytes input).length by
        rw [LZ77.bytes_length]; scalar_tac]
      simp
  · exact ⟨hi, rfl, hdec⟩

theorem r_literals_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.r_literals input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.r_literals]
  apply Std.WP.spec_bind (r_literals_loop_spec input out (Std.Slice.len input) 0#usize
    (by simp) hlen (by scalar_tac) (by simp [toks, LZ77.decode]))
  intro out1 ⟨hlen1, hdec⟩
  step*
  exact ⟨by simp, hlen1, hdec⟩

end ER

attribute [local step] EA.parse_spec EB.a_sniff_spec EB.a_parse_cls_spec EB.emit_spec ER.r_literals_spec
  EY.dp_parse_spec EY.x_parse_spec

theorem run_method_spec (input : Slice Std.U8) (out : Slice Std.U32) (k : Array Std.Usize 9#usize)
    (hlen : input.length ≤ out.length) :
    slot.run_method input out k ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.run_method]
  step*
  · apply Std.WP.spec_bind (Pₘ := fun _ => True)
    · split
      · exact EB.a_sniff_spec input
      · simp
    · intro cls _
      step*
  · apply Std.WP.spec_bind (Pₘ := fun _ => True)
    · split
      · step*
        all_goals (first
          | simp
          | (have hw := EB.dp_wadd_self input.len (by rw [← i2_post]; scalar_tac)
             exact EB.dp_parse_spec input _ _ _ _ _ _ _ _ (by scalar_tac) (by simpa using hw)))
      · simp
    · intro plan1 _
      step*
      refine ⟨by assumption, by assumption, ?_⟩
      unfold LZ77.Valid; assumption

attribute [local step] run_method_spec ER.r_format_spec

theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.parse]
  step*

end Submission
