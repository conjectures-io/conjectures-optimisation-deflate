import Lz77
import Slot
namespace Submission
open Aeneas Aeneas.Std Result ControlFlow
open LZ77 (toks bytes)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace EA
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
theorem get0_spec (v : Slice Std.U32) (i : Std.Usize) : slot.a_get0 v i ⦃ fun _ => True ⦄ := by
  rw [slot.a_get0]; split <;> step*
@[local step]
theorem set_in_spec (v : Slice Std.U32) (i : Std.Usize) (x : Std.U32) :
    slot.a_set_in v i x ⦃ fun r => r.length = v.length ⦄ := by
  rw [slot.a_set_in]; split <;> step*
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
theorem BLOCK_TOKENS_bounds : 0 < slot.A_BLOCK_TOKENS.val ∧ slot.A_BLOCK_TOKENS.val ≤ 65536 := by
  simp [slot.A_BLOCK_TOKENS]
theorem mlen_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.a_mlen_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.a_mlen_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    simp only [slot.a_mlen_loop.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    step*
    refine ⟨by scalar_tac, ?_, by scalar_tac⟩
    rw [show l1.val = l.val + 1 by scalar_tac]
    apply LZ77.Matches.succ hinv
    rw [getElem!_pos _ _ (by scalar_tac), getElem!_pos _ _ (by scalar_tac)]
    simp_all
  · exact ⟨hl0, h0⟩
@[local step]
theorem mlen_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.a_mlen input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ :=
  mlen_loop_spec input a b cap 0#usize ha hb (by scalar_tac) (LZ77.Matches.zero input a.val b.val)
@[local step]
theorem check_spec (input : Slice Std.U8) (p len dist : Std.Usize) :
    slot.a_check input p len dist ⦃ fun valid => valid = true →
      3 ≤ len.val ∧ len.val ≤ 258 ∧ 1 ≤ dist.val ∧ dist.val ≤ 32768 ∧ dist.val ≤ p.val ∧
      p.val + len.val ≤ input.length ∧ Matches input (p.val - dist.val) p.val len.val ⦄ := by
  rw [slot.a_check]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  intro hvalid
  have hl : l = len := by simpa using hvalid
  subst hl
  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac,
    by scalar_tac, ?_⟩
  rw [← src_post1]
  exact l_post2
theorem emit_loop_spec (input : Slice Std.U8) (plan out0 : Slice Std.U32)
    (n ntok0 p0 : Std.Usize) (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hp0 : p0.val ≤ n.val) (hntok0 : ntok0.val ≤ p0.val)
    (hdec0 : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take p0.val)) :
    slot.a_emit_loop input plan out0 n ntok0 p0 ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
      LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.a_emit_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, p) => n.val - p.val)
    (inv := fun (out, ntok, p) => p.val ≤ n.val ∧ ntok.val ≤ p.val ∧ out.length = out0.length ∧
      LZ77.decode (toks out ntok.val) = some ((bytes input).take p.val))
  · rintro ⟨out, ntok, p⟩ ⟨hp, hnt, hlen, hde⟩
    simp only [slot.a_emit_loop.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    split
    case isTrue hlt =>
      have hntok_lt : ntok.val < out.length := by scalar_tac
      step*
      · -- `check` accepted `(len, dist)`: write the match token, advance `len`
        obtain ⟨h3, h258, hd1, hd32k, hdp, hend, hm⟩ := valid_post (by assumption)
        have htok : tok.val = LZ77.mkMatch dist.val len.val := by
          simp only [LZ77.mkMatch, LZ77.MATCH_BASE]
          scalar_tac
        refine ⟨by scalar_tac, by scalar_tac, by rw [s_post]; simpa using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show p1.val = p.val + len.val by scalar_tac]
        exact emit_match input out ntok p.val dist.val len.val tok hde hntok_lt hd1 hdp hd32k
          h3 h258 hend hm htok
      · -- anything else: write the literal `input[p]`, advance 1
        have hlit : lit.val = (bytes input)[p.val]! := by
          rw [bytes_getElem! input p.val (by scalar_tac)]
          scalar_tac
        refine ⟨by scalar_tac, by scalar_tac, by rw [s_post]; simpa using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show p1.val = p.val + 1 by scalar_tac]
        exact emit_lit input out ntok p.val lit hde (by scalar_tac) hntok_lt hlit
    case isFalse hge =>
      have hpn : p.val = input.length := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      rw [hde, hpn]
      simp
  · exact ⟨hp0, hntok0, rfl, hdec0⟩
@[local step]
theorem emit_spec (input : Slice Std.U8) (plan out : Slice Std.U32)
    (hout : input.length ≤ out.length) :
    slot.a_emit input plan out ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.a_emit]
  exact emit_loop_spec input plan out (Std.Slice.len input) 0#usize 0#usize (by simp) hout
    (by simp) (by simp) (by simp [toks, LZ77.decode])
@[local step]
theorem zeros_loop_spec (n : Std.Usize) (v0 : alloc.vec.Vec Std.U32) (i0 : Std.Usize)
    (hv : v0.length = i0.val) (hi : i0.val ≤ n.val) :
    slot.a_zeros_loop n v0 i0 ⦃ fun v => v.length = n.val ⦄ := by
  rw [slot.a_zeros_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i) => n.val - i.val)
    (inv := fun (v, i) => v.length = i.val ∧ i.val ≤ n.val)
  · rintro ⟨v, i⟩ ⟨hvi, hin⟩
    simp only [slot.a_zeros_loop.body]
    step*
    have hlen : v1.length = v.length + 1 := by simp [v1_post]
    scalar_tac
  · exact ⟨hv, hi⟩
@[local step]
theorem zeros_spec (n : Std.Usize) : slot.a_zeros n ⦃ fun v => v.length = n.val ⦄ := by
  rw [slot.a_zeros]
  step*
  simp [alloc.vec.Vec.with_capacity]
@[local step]
theorem sample_counts_loop0_loop0_spec (s : Slice Std.U8) (f) (n e i : Std.Usize) (c : Nat)
    (hn : n.val ≤ s.length) (hc : c + (e.val - i.val) ≤ 2 ^ 31) (hf : LeAll f.val c) :
    slot.a_sample_counts_loop0_loop0 s f n e i ⦃ fun r => LeAll r.val (c + (e.val - i.val)) ⦄ := by
  rw [slot.a_sample_counts_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i') => e.val - i'.val)
    (inv := fun (f', i') => i.val ≤ i'.val ∧ i'.val - i.val ≤ e.val - i.val ∧
      LeAll f'.val (c + (i'.val - i.val)))
  · rintro ⟨f', i'⟩ ⟨hi1, hi2, hf'⟩
    simp only [slot.a_sample_counts_loop0_loop0.body]
    step*
    all_goals try (exact LeAll_mono hf' (by omega))
    have h5 := LeAll_get hf' i4.val (by scalar_tac)
    rw [← i5_post] at h5
    have h6 : i6.val = i5.val + 1 := by
      simp only [i6_post, core.num.Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
      rw [Nat.mod_eq_of_lt] <;> scalar_tac
    refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
    have heq : i7.val - i.val = (i'.val - i.val) + 1 := by scalar_tac
    rw [heq, ← Nat.add_assoc, a_post, Array.set_val_eq]
    exact LeAll_set_succ hf' _ _ (by scalar_tac)
  · exact ⟨le_refl _, by omega, by simpa using hf⟩
theorem spine_wrap1024 (a : Std.Usize) :
    (core.num.Usize.wrapping_add a 1024#usize).val - a.val ≤ 1024 := by
  rw [core.num.Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  have ha : a.val < Usize.size := by scalar_tac
  have hs : 1024 < Usize.size := by scalar_tac
  have h1 : (1024#usize).val = 1024 := by simp
  rw [h1]
  by_cases h : a.val + 1024 < Usize.size
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
@[local step]
theorem sample_counts_loop0_spec (s : Slice Std.U8) (f) (n nw step w : Std.Usize) (c : Nat)
    (hn : n.val ≤ s.length) (hnw : (nw.val = 1 ∧ n.val ≤ 32768) ∨ nw.val = 32)
    (hc : c ≤ 2 ^ 30) (hf : LeAll f.val c) :
    slot.a_sample_counts_loop0 s f n nw step w ⦃ fun r => LeAll r.val (c + (nw.val - w.val) * (32768 / nw.val)) ⦄ := by
  rw [slot.a_sample_counts_loop0]
  rcases hnw with ⟨h1, hn1⟩ | h32
  · -- the whole input is one window (`e = n ≤ 32768`)
    have hK : 32768 / nw.val = 32768 := by rw [h1]
    rw [hK]
    apply Std.loop.spec_decr_nat
      (measure := fun (_, w') => nw.val - w'.val)
      (inv := fun (f', w') => w.val ≤ w'.val ∧ w'.val - w.val ≤ nw.val - w.val ∧
        LeAll f'.val (c + (w'.val - w.val) * 32768))
    · rintro ⟨f', w'⟩ ⟨hw1, hw2, hf'⟩
      simp only [slot.a_sample_counts_loop0.body]
      step*
      repeat' (split <;> step*)
      all_goals try (exact LeAll_mono hf' (by scalar_tac))
      all_goals try scalar_tac
      refine ⟨by scalar_tac, by scalar_tac, LeAll_mono f1_post (by scalar_tac), by scalar_tac⟩
    · exact ⟨le_refl _, by omega, by simpa using hf⟩
  · -- 32 windows of 1024 bytes (`e = a + 1024` wrapping: at most 1024 bytes each)
    have hK : 32768 / nw.val = 1024 := by rw [h32]
    rw [hK]
    apply Std.loop.spec_decr_nat
      (measure := fun (_, w') => nw.val - w'.val)
      (inv := fun (f', w') => w.val ≤ w'.val ∧ w'.val - w.val ≤ nw.val - w.val ∧
        LeAll f'.val (c + (w'.val - w.val) * 1024))
    · rintro ⟨f', w'⟩ ⟨hw1, hw2, hf'⟩
      simp only [slot.a_sample_counts_loop0.body]
      step*
      repeat' (split <;> step*)
      all_goals try (exact LeAll_mono hf' (by scalar_tac))
      all_goals try (have := spine_wrap1024 a; scalar_tac)
      have := spine_wrap1024 a
      refine ⟨by scalar_tac, by scalar_tac, LeAll_mono f1_post (by scalar_tac), by scalar_tac⟩
    · exact ⟨le_refl _, by omega, by simpa using hf⟩
set_option hygiene false in
local notation "U1!" q0__:max => (by
  rw [q0__]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac)
@[local step]
theorem sample_counts_spec (s) (f : Array Std.Usize 16#usize) (hf : LeAll f.val 0) :
    slot.a_sample_counts s f ⦃ fun r => LeAll r.val 32768 ⦄ := U1! slot.a_sample_counts
@[local step]
theorem classify_loop0_spec (f tot k) :
    slot.a_classify_loop0 f tot k ⦃ fun _ => True ⦄ := by
  rw [slot.a_classify_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (tot_, k_) => 16 - k_.val)
    (inv := fun _ => True)
  · rintro ⟨tot_, k_⟩ _
    simp only [slot.a_classify_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem classify_loop1_spec (f : Array Std.Usize 16#usize) (tot : Std.Usize) (k) (m : Array Std.Usize 16#usize)
    (htot : 0 < tot.val) (hf : LeAll f.val 32768) (hm : LeAll m.val 32768000) :
    slot.a_classify_loop1 f tot k m ⦃ fun r => LeAll r.val 32768000 ⦄ := by
  rw [slot.a_classify_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (k', _) => 16 - k'.val)
    (inv := fun (_, m') => LeAll m'.val 32768000)
  · rintro ⟨k', m'⟩ (hm' : LeAll m'.val 32768000)
    simp only [slot.a_classify_loop1.body]
    step*
    have h0 : i.val ≤ 32768 := by rw [i_post]; exact LeAll_get hf k'.val (by scalar_tac)
    have h1 : i1.val = i.val * 1000 := by
      simp only [i1_post, core.num.Usize.wrapping_mul_val_eq, UScalar.size_UScalarTyUsize]
      rw [Nat.mod_eq_of_lt] <;> scalar_tac
    have h2 : i2.val ≤ i1.val := by rw [i2_post]; exact Nat.div_le_self _ _
    refine ⟨?_, by scalar_tac⟩
    rw [a_post, Array.set_val_eq]
    exact LeAll_set hm' _ _ (by scalar_tac)
  · exact hm
theorem spine_LeAll_repeat0 (n : Std.Usize) (B : Nat) : LeAll (Array.repeat n 0#usize).val B := by
  rw [Array.repeat_val]; exact LeAll_replicate _ _ _ (by simp)
theorem spine_LeAll_read {ty : UScalarTy} {l : List (UScalar ty)} {B : Nat} (hl : LeAll l B)
    {x : UScalar ty} {j : Nat} {hj : j < l.length} (hx : x = l[j]) : x.val ≤ B := by
  subst hx; exact hl j hj
@[local step]
theorem classify_spec (s) : slot.a_classify s ⦃ fun _ => True ⦄ := by
  rw [slot.a_classify]
  have h0 := spine_LeAll_repeat0 16#usize 0
  have h1 := spine_LeAll_repeat0 16#usize 32768000
  step*
  all_goals
    try have hb1 := spine_LeAll_read m1_post nl_post
    try have hb3 := spine_LeAll_read m1_post dig_post
    try have hb4 := spine_LeAll_read m1_post lt_post
    try have hb5 := spine_LeAll_read m1_post q_post
    try have hb6 := spine_LeAll_read m1_post com_post
    try have hb7 := spine_LeAll_read m1_post hi_post
    try have hb8 := spine_LeAll_read m1_post zero_post
    try have hbi := spine_LeAll_read m1_post i_post
    try have hbi1 := spine_LeAll_read m1_post i1_post
    try have hbi2 := spine_LeAll_read m1_post i2_post
    try have hbi3 := spine_LeAll_read m1_post i3_post
    scalar_tac
theorem A_LOG_FRAC_le : LeAll slot.A_A_LOG_FRAC.val 64 := by
  unfold slot.A_A_LOG_FRAC LeAll; simp only [Array.make]; decide
theorem A_SEG_bounds : 256 ≤ slot.A_A_SEG.val ∧ slot.A_A_SEG.val ≤ 65536 ∧
    slot.A_A_SEG.val + 512 ≤ slot.A_A_SEG.val * slot.A_A_SAMPLE.val ∧
    slot.A_A_SEG.val * slot.A_A_SAMPLE.val ≤ 1048576 := by
  simp
theorem A_HB_bounds : 1 ≤ slot.A_A_HB.val ∧ slot.A_A_HB.val ≤ 32 := by
  simp
theorem A_BLOCK_bounds : 0 < slot.A_BLOCK_TOKENS.val ∧ slot.A_BLOCK_TOKENS.val ≤ 16384 ∧
    slot.A_A_MARGIN.val ≤ 65536 ∧ slot.A_A_SLACK.val ≠ 0 := by
  simp
theorem engA_ite_ok {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then (ok a : Result α) else ok b) = ok (if c then a else b) := by
  split <;> rfl
theorem engA_sat_add_val (x y : Std.Usize) :
    (core.num.Usize.saturating_add x y).val = min Std.Usize.max (x.val + y.val) := by
  have hsz : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    rw [Std.Usize.max_def, Std.Usize.numBits]
    have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    omega
  show (BitVec.ofNat _ (min (UScalar.max UScalarTy.Usize) (x.val + y.val))).toNat = _
  rw [BitVec.toNat_ofNat, UScalar.max_USize_eq, Nat.mod_eq_of_lt (by omega)]
@[local scalar_tac core.num.Usize.saturating_add x y]
theorem engA_sat_add_val' (x y : Std.Usize) :
    (core.num.Usize.saturating_add x y).val = min Std.Usize.max (x.val + y.val) := engA_sat_add_val x y
theorem engA_ite_pair {α β : Type} (c : Prop) [Decidable c] (a a' : α) (b b' : β) :
    (if c then (a, b) else (a', b')) = (if c then a else a', if c then b else b') := by
  split <;> rfl
theorem engA_LeAll_repeat {ty : UScalarTy} (n : Std.Usize) (x : UScalar ty) (B : Nat) (h : x.val ≤ B) :
    LeAll (Array.repeat n x).val B := by
  rw [Array.repeat_val]; exact LeAll_replicate _ _ _ h
theorem engA_LeAll_set_of_eq {n : Std.Usize} {a r : Array Std.U32 n} {i : Std.Usize} {v : Std.U32} {B : Nat}
    (hr : r = a.set i v) (ha : LeAll a.val B) (hv : v.val ≤ B) : LeAll r.val B := by
  rw [hr, Array.set_val_eq]; exact LeAll_set ha _ _ hv
@[local step]
theorem a_slot_of_spec (x) :
    slot.a_a_slot_of x ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_slot_of]
  step*
@[local step]
theorem a_len_slot_spec (len) :
    slot.a_a_len_slot len ⦃ fun r => r.val ≤ 28 ⦄ := by
  rw [slot.a_a_len_slot]
  split
  · step*
  · split
    · step*
    · step*
      all_goals
        have hx : x.val = len.val - 3 := by
          rw [x_post, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)]; scalar_tac
        have h1 := lz32_le_of_pow_le x 3 (by scalar_tac)
        have h2 := lz32_ge_of_lt_pow x 8 (by scalar_tac)
        subst i1_post
        scalar_tac
@[local step]
theorem a_walk_loop0_spec (lf) :
    slot.a_a_walk_loop0 lf 0#usize ⦃ fun r => LeAll r.val 0 ⦄ := by
  rw [slot.a_a_walk_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k) => 512 - k.val)
    (inv := fun (lf', k) => k.val ≤ 512 ∧ ∀ j (hj : j < k.val) (hl : j < lf'.val.length), (lf'.val[j]).val = 0)
  · rintro ⟨lf', k⟩ ⟨hk, hz⟩
    simp only [slot.a_a_walk_loop0.body]
    step*
    · -- one more entry zeroed
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj hl
      subst a_post
      simp only [Array.set_val_eq, List.getElem_set]
      split
      · rfl
      · exact hz j (by scalar_tac) (by simpa using hl)
    · -- exit: k = 512 covers the whole array
      intro j hl
      have : k.val = 512 := by scalar_tac
      have hl' : j < 512 := by simpa using hl
      rw [hz j (by omega) hl]
  · exact ⟨by simp, fun j hj => by simp at hj⟩
@[local step]
theorem a_walk_loop1_spec (df) :
    slot.a_a_walk_loop1 df 0#usize ⦃ fun r => LeAll r.val 0 ⦄ := by
  rw [slot.a_a_walk_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k) => 32 - k.val)
    (inv := fun (df', k) => k.val ≤ 32 ∧ ∀ j (hj : j < k.val) (hl : j < df'.val.length), (df'.val[j]).val = 0)
  · rintro ⟨df', k⟩ ⟨hk, hz⟩
    simp only [slot.a_a_walk_loop1.body]
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj hl
      subst a_post
      simp only [Array.set_val_eq, List.getElem_set]
      split
      · rfl
      · exact hz j (by scalar_tac) (by simpa using hl)
    · intro j hl
      have : k.val = 32 := by scalar_tac
      have hl' : j < 32 := by simpa using hl
      rw [hz j (by omega) hl]
  · exact ⟨by simp, fun j hj => by simp at hj⟩
@[local step]
theorem a_walk_loop2_spec (s : Slice Std.U8) (ch) (lim need : Std.Usize) (lf df) (i t : Std.Usize)
    (hlim : lim.val ≤ 2 ^ 31) (hls : lim.val ≤ s.length) (hneed : need.val ≤ 2 ^ 31)
    (hlf : LeAll lf.val t.val) (hdf : LeAll df.val t.val) :
    slot.a_a_walk_loop2 s ch lim need lf df i t ⦃ fun r => i.val ≤ r.2.2.1.val ∧ r.2.2.2.val ≤ max t.val need.val ∧
      r.2.2.1.val ≤ max i.val (lim.val + 511) ∧ r.2.2.1.val + 511 * t.val ≤ i.val + 511 * r.2.2.2.val ⦄ := by
  rw [slot.a_a_walk_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, t') => need.val - t'.val)
    (inv := fun (lf', df', i', t') => LeAll lf'.val t'.val ∧ LeAll df'.val t'.val ∧
      i.val ≤ i'.val ∧ t'.val ≤ max t.val need.val ∧
      i'.val ≤ max i.val (lim.val + 511) ∧ i'.val + 511 * t.val ≤ i.val + 511 * t'.val)
  · rintro ⟨lf', df', i', t'⟩ ⟨hlf', hdf', hi', ht', hi2', hi3'⟩
    simp only [slot.a_a_walk_loop2.body]
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Array Std.U32 512#usize × Std.Array Std.U32 32#usize × Std.Usize) =>
      LeAll x.1.val (t'.val + 1) ∧ LeAll x.2.1.val (t'.val + 1) ∧ i'.val < x.2.2.val ∧ x.2.2.val ≤ i'.val + 511)
    · split
      · -- a match: one length counter and one distance counter go up
        step*
        all_goals try (have := LeAll_get hlf' i6.val (by scalar_tac))
        all_goals try (have := LeAll_get hdf' i14.val (by scalar_tac))
        all_goals try scalar_tac
        refine ⟨?_, ?_, by scalar_tac, by scalar_tac⟩
        · rw [a_post, Array.set_val_eq]; exact LeAll_set_succ hlf' _ _ (by scalar_tac)
        · rw [a1_post, Array.set_val_eq]; exact LeAll_set_succ hdf' _ _ (by scalar_tac)
      · -- a literal: one literal counter goes up
        step*
        all_goals try (have := LeAll_get hlf' i5.val (by scalar_tac))
        all_goals try scalar_tac
        refine ⟨?_, LeAll_mono hdf' (by omega), by scalar_tac, by scalar_tac⟩
        rw [a_post, Array.set_val_eq]; exact LeAll_set_succ hlf' _ _ (by scalar_tac)
    · rintro ⟨lf1, df1, i3⟩ ⟨h1, h2, h3, h4⟩
      step*
      refine ⟨?_, ?_, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
      · rw [show t1.val = t'.val + 1 by scalar_tac]; exact h1
      · rw [show t1.val = t'.val + 1 by scalar_tac]; exact h2
  · exact ⟨hlf, hdf, le_refl _, by omega, by omega, by omega⟩
@[local step]
theorem a_walk_spec (s : Slice Std.U8) (ch) (p0 lim need : Std.Usize) (lf df)
    (hlim : lim.val ≤ 2 ^ 31) (hls : lim.val ≤ s.length) (hneed : need.val ≤ 2 ^ 31) :
    slot.a_a_walk s ch p0 lim need lf df ⦃ fun r => p0.val ≤ r.1.1.val ∧ r.1.2.val ≤ need.val ∧
      r.1.1.val ≤ max p0.val (lim.val + 511) ∧ r.1.1.val ≤ p0.val + 511 * r.1.2.val ⦄ := U1! slot.a_a_walk
@[local step]
theorem a_dp_pass_loop0_spec (pe : Std.Usize) (cost) (cl z : Std.Usize) (hpe : pe.val ≤ 2 ^ 31) (hcl : cl.val = cost.length) :
    slot.a_a_dp_pass_loop0 pe cost cl z ⦃ fun r => r.length = cost.length ⦄ := by
  rw [slot.a_a_dp_pass_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, z_) => cl.val - z_.val)
    (inv := fun (cost_, _) => cost_.length = cost.length)
  · rintro ⟨cost_, z_⟩ hinv
    simp only [slot.a_a_dp_pass_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · rfl
set_option hygiene false in
local notation "U2!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun (mbest_, at0_, l_) => stop.val + 1 - at0_.val)
    (inv := fun _ => True)
  · rintro ⟨mbest_, at0_, l_⟩ _
    simp only [q1__]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem a_dp_pass_loop1_loop0_loop0_spec (lc) (cost : alloc.vec.Vec Std.U32) (stop base mbest at0 l) (hstop : stop.val < cost.length) :
    slot.a_a_dp_pass_loop1_loop0_loop0 lc cost stop base mbest at0 l ⦃ fun _ => True ⦄ := U2! slot.a_a_dp_pass_loop1_loop0_loop0 slot.a_a_dp_pass_loop1_loop0_loop0.body
@[local step]
theorem a_dp_pass_loop1_loop0_loop1_spec (lc) (cost : alloc.vec.Vec Std.U32) (stop base mbest at0 l) (hstop : stop.val < cost.length) :
    slot.a_a_dp_pass_loop1_loop0_loop1 lc cost stop base mbest at0 l ⦃ fun _ => True ⦄ := U2! slot.a_a_dp_pass_loop1_loop0_loop1 slot.a_a_dp_pass_loop1_loop0_loop1.body
@[local step]
theorem a_dp_pass_loop1_loop0_spec (mb lc dc) (cost : alloc.vec.Vec Std.U32) (cl i : Std.Usize) (bias best bd) (prev pd : Std.Usize) (j top : Std.Usize)
    (hcl : cl.val = cost.length) (hi : i.val ≤ 2 ^ 31) (htop : top.val ≤ mb.length)
    (hprev : prev.val ≤ i.val + 258) (hpd : pd.val ≤ 32768) (hbd : bd.val ≤ 32767) :
    slot.a_a_dp_pass_loop1_loop0 mb lc dc cost cl i bias best bd prev pd j top ⦃ fun r =>
      prev.val ≤ r.2.2.1.val ∧ r.2.2.1.val ≤ i.val + 258 ∧ r.2.2.2.val ≤ 32768 ∧ r.2.1.val ≤ 32767 ⦄ := by
  rw [slot.a_a_dp_pass_loop1_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, j_) => top.val - j_.val)
    (inv := fun (_, bd_, prev_, pd_, _) => prev.val ≤ prev_.val ∧ prev_.val ≤ i.val + 258 ∧
      pd_.val ≤ 32768 ∧ bd_.val ≤ 32767)
  · rintro ⟨best_, bd_, prev_, pd_, j_⟩ ⟨hp0, hp1, hpd_, hbd_⟩
    simp only [slot.a_a_dp_pass_loop1_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨le_refl _, hprev, hpd, hbd⟩
@[local step]
theorem a_dp_pass_loop1_loop1_spec (lc) (cost : alloc.vec.Vec Std.U32) (stop base mbest at0 l) (hstop : stop.val < cost.length) :
    slot.a_a_dp_pass_loop1_loop1 lc cost stop base mbest at0 l ⦃ fun _ => True ⦄ := U2! slot.a_a_dp_pass_loop1_loop1 slot.a_a_dp_pass_loop1_loop1.body
set_option maxHeartbeats 4000000 in
@[local step]
theorem a_dp_pass_loop1_spec (s : Slice Std.U8) (mp mb : alloc.vec.Vec Std.U32) (p0 lit lc dc) (cost ch : alloc.vec.Vec Std.U32)
    (cl i e xl xd : Std.Usize)
    (hcl : cl.val = cost.length) (hi : i.val < cl.val) (hmp : i.val < mp.length) (hs : i.val ≤ s.length)
    (hch : i.val ≤ ch.length) (hi31 : i.val ≤ 2 ^ 31) (hxl : xl.val ≤ 258) (hxd : xd.val ≤ 32768) :
    slot.a_a_dp_pass_loop1 s mp mb p0 lit lc dc cost ch cl i e xl xd ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_dp_pass_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, i_, _, _, _) => i_.val)
    (inv := fun ((cost_ : alloc.vec.Vec Std.U32), (ch_ : alloc.vec.Vec Std.U32), (i_ : Std.Usize), _,
        (xl_ : Std.Usize), (xd_ : Std.Usize)) =>
      cost_.length = cl.val ∧ ch_.length = ch.length ∧ i_.val ≤ i.val ∧ xl_.val ≤ 258 ∧ xd_.val ≤ 32768)
  · rintro ⟨cost_, ch_, i_, e_, xl_, xd_⟩ ⟨hc_, hch_, hi_, hxl_, hxd_⟩
    simp only [slot.a_a_dp_pass_loop1.body]
    step*
    apply WP.spec_bind (Pₘ := fun (top : Std.Usize) => top.val ≤ mb.length)
    · split <;> step* <;> scalar_tac
    rintro top htop
    step*
    apply WP.spec_bind (Pₘ := fun (el : Std.Usize) => el.val ≤ 258)
    · split <;> step* <;> scalar_tac
    rintro el hel
    step*
    all_goals
      try (
        apply WP.spec_bind (Pₘ := fun (x : Std.U32 × Std.U32) => x.2.val ≤ 32767)
        · split <;> step* <;> scalar_tac
        rintro ⟨best2, bd1⟩ hbd1
        step*)
    all_goals
      apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.U32) => x.1.length = cost_.length)
      · split <;> step* <;> scalar_tac
      rintro ⟨cost1, i23⟩ hc1
      step*
      scalar_tac
  · exact ⟨hcl.symm, rfl, le_refl _, hxl, hxd⟩
@[local step]
theorem a_dp_pass_spec (s : Slice Std.U8) (mp mb) (p0 pe : Std.Usize) (lit lc dc) (cost ch)
    (hpe : pe.val ≤ 2 ^ 31) :
    slot.a_a_dp_pass s mp mb p0 pe lit lc dc cost ch ⦃ fun _ => True ⦄ := U1! slot.a_a_dp_pass
@[local step]
theorem a_sample_pass_loop0_loop0_spec (lf zf b) :
    slot.a_a_sample_pass_loop0_loop0 lf zf b ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_sample_pass_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (zf_, b_) => 512 - b_.val)
    (inv := fun _ => True)
  · rintro ⟨zf_, b_⟩ _
    simp only [slot.a_a_sample_pass_loop0_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_sample_pass_loop0_loop1_spec (df zd b) :
    slot.a_a_sample_pass_loop0_loop1 df zd b ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_sample_pass_loop0_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (zd_, b_) => 32 - b_.val)
    (inv := fun _ => True)
  · rintro ⟨zd_, b_⟩ _
    simp only [slot.a_a_sample_pass_loop0_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_sample_pass_loop0_spec (s : Slice Std.U8) (mp mb) (pe : Std.Usize) (lit lc dc cost ch lf df zf zd) (sb st a : Std.Usize)
    (hpe : pe.val ≤ 2 ^ 30) (hps : pe.val ≤ s.length) (hsb : sb.val ≤ a.val) (hst : st.val ≤ a.val)
    (ha : a.val ≤ pe.val + slot.A_A_SEG.val * slot.A_A_SAMPLE.val) :
    slot.a_a_sample_pass_loop0 s mp mb pe lit lc dc cost ch lf df zf zd sb st a ⦃ fun _ => True ⦄ := by
  have hseg := A_SEG_bounds
  rw [slot.a_a_sample_pass_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, a_) => pe.val - a_.val)
    (inv := fun (_, _, _, _, _, _, sb_, st_, a_) => sb_.val ≤ a_.val ∧ st_.val ≤ a_.val ∧
      a_.val ≤ pe.val + slot.A_A_SEG.val * slot.A_A_SAMPLE.val)
  · rintro ⟨cost_, ch_, lf_, df_, zf_, zd_, sb_, st_, a_⟩ ⟨hsb_, hst_, ha_⟩
    simp only [slot.a_a_sample_pass_loop0.body]
    step*
    cases ‹Std.Usize × Std.Usize›
    step*
    all_goals scalar_tac
  · exact ⟨hsb, hst, ha⟩
@[local step]
theorem a_sample_pass_loop1_spec (lf zf b) :
    slot.a_a_sample_pass_loop1 lf zf b ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_sample_pass_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (lf_, b_) => 512 - b_.val)
    (inv := fun _ => True)
  · rintro ⟨lf_, b_⟩ _
    simp only [slot.a_a_sample_pass_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_sample_pass_loop2_spec (df zd b) :
    slot.a_a_sample_pass_loop2 df zd b ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_sample_pass_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (df_, b_) => 32 - b_.val)
    (inv := fun _ => True)
  · rintro ⟨df_, b_⟩ _
    simp only [slot.a_a_sample_pass_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_sample_pass_spec (s : Slice Std.U8) (mp mb) (p0 pe : Std.Usize) (lit lc dc cost ch lf df)
    (hpe : pe.val ≤ 2 ^ 30) (hps : pe.val ≤ s.length) (hp0 : p0.val ≤ pe.val) :
    slot.a_a_sample_pass s mp mb p0 pe lit lc dc cost ch lf df ⦃ fun _ => True ⦄ := by
  have hseg := A_SEG_bounds
  rw [slot.a_a_sample_pass]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac
@[local step]
theorem a_add_counts_loop0_spec (dst a b k) :
    slot.a_a_add_counts_loop0 dst a b k ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_add_counts_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (dst_, k_) => 512 - k_.val)
    (inv := fun _ => True)
  · rintro ⟨dst_, k_⟩ _
    simp only [slot.a_a_add_counts_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_add_counts_loop1_spec (dd x y k) :
    slot.a_a_add_counts_loop1 dd x y k ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_add_counts_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (dd_, k_) => 32 - k_.val)
    (inv := fun _ => True)
  · rintro ⟨dd_, k_⟩ _
    simp only [slot.a_a_add_counts_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_add_counts_spec (dst a b dd x y) :
    slot.a_a_add_counts dst a b dd x y ⦃ fun _ => True ⦄ := U1! slot.a_a_add_counts
@[local step]
theorem a_lg64_spec (x) :
    slot.a_a_lg64 x ⦃ fun r => r.val ≤ 2048 ⦄ := by
  rw [slot.a_a_lg64]
  have hlz := lz32_bound x
  have htab := A_LOG_FRAC_le
  step*
  repeat' (split <;> step*)
  all_goals try (have := LeAll_get htab i3.val (by scalar_tac))
  all_goals scalar_tac
@[local step]
theorem a_sym_cost_spec (f : Std.U32) (g : Std.U32) (hg : g.val ≤ 65536) :
    slot.a_a_sym_cost f g ⦃ fun r => r.val ≤ 1152 ⦄ := U1! slot.a_a_sym_cost
@[local step]
theorem a_dist_extra_spec (slt : Std.Usize) :
    slot.a_a_dist_extra slt ⦃ fun r => r.val ≤ slt.val / 2 ⦄ := U1! slot.a_a_dist_extra
@[local step]
theorem a_len_extra_spec (slt) :
    slot.a_a_len_extra slt ⦃ fun r => r.val ≤ 5 ⦄ := U1! slot.a_a_len_extra
@[local step]
theorem a_set_costs_loop0_spec (lf tl i) :
    slot.a_a_set_costs_loop0 lf tl i ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (tl_, i_) => 286 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨tl_, i_⟩ _
    simp only [slot.a_a_set_costs_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
set_option hygiene false in
local notation "U3!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun (i_, td_) => 30 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨i_, td_⟩ _
    simp only [q1__]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem a_set_costs_loop1_spec (df i td) :
    slot.a_a_set_costs_loop1 df i td ⦃ fun _ => True ⦄ := U3! slot.a_a_set_costs_loop1 slot.a_a_set_costs_loop1.body
@[local step]
theorem a_set_costs_loop2_spec (lf lit i) (gl : Std.U32) (hgl : gl.val ≤ 65536) :
    slot.a_a_set_costs_loop2 lf lit i gl ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (lit_, i_) => 256 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨lit_, i_⟩ _
    simp only [slot.a_a_set_costs_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_loop3_spec (lf lc i) (gl : Std.U32) (hgl : gl.val ≤ 65536) :
    slot.a_a_set_costs_loop3 lf lc i gl ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun (lc_, i_) => 258 + 1 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨lc_, i_⟩ _
    simp only [slot.a_a_set_costs_loop3.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_loop4_spec (df dc) (i : Std.Usize) (gd : Std.U32) (hgd : gd.val ≤ 65536) :
    slot.a_a_set_costs_loop4 df dc i gd ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_loop4]
  apply Std.loop.spec_decr_nat
    (measure := fun (dc_, i_) => 30 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨dc_, i_⟩ _
    simp only [slot.a_a_set_costs_loop4.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_spec (lf df lit lc dc) :
    slot.a_a_set_costs lf df lit lc dc ⦃ fun _ => True ⦄ := U1! slot.a_a_set_costs
@[local step]
theorem a_first_model_loop0_spec (s : Slice Std.U8) (lf) (m i : Std.Usize) (hm : m.val ≤ s.length) (hm2 : m.val ≤ 65536)
    (hlf : LeAll lf.val i.val) :
    slot.a_a_first_model_loop0 s lf m i ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_first_model_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i_) => m.val - i_.val)
    (inv := fun (lf_, i_) => LeAll lf_.val i_.val)
  · rintro ⟨lf_, i_⟩ hlf_
    simp only [slot.a_a_first_model_loop0.body]
    step*
    all_goals try (have := LeAll_get hlf_ i2.val (by scalar_tac))
    all_goals try scalar_tac
    refine ⟨?_, by scalar_tac⟩
    rw [show i5.val = i_.val + 1 by scalar_tac, a_post, Array.set_val_eq]
    exact LeAll_set_succ hlf_ _ _ (by scalar_tac)
  · exact hlf
@[local step]
theorem a_first_model_loop1_spec (lf i) :
    slot.a_a_first_model_loop1 lf i ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_first_model_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (lf_, i_) => 29 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨lf_, i_⟩ _
    simp only [slot.a_a_first_model_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_first_model_loop2_spec (df i) :
    slot.a_a_first_model_loop2 df i ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_first_model_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (df_, i_) => 30 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨df_, i_⟩ _
    simp only [slot.a_a_first_model_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_first_model_spec (s lit lc dc) :
    slot.a_a_first_model s lit lc dc ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_first_model]
  step*
  repeat' (split <;> step*)
  all_goals exact engA_LeAll_repeat _ _ _ (by simp)
@[local step]
theorem a_kraft_fix_loop_spec (sym m) (len : Array Std.U32 512#usize) (kraft q) (hlen : LeAll len.val 15) :
    slot.a_a_kraft_fix_loop sym m len kraft q ⦃ fun r => LeAll r.val 15 ⦄ := by
  rw [slot.a_a_kraft_fix_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun ((len_ : Array Std.U32 512#usize), _, (q_ : Std.Usize)) =>
      (512 - q_.val) * 16 + (15 - (len_.val[(sym.val[q_.val]!).val % 512]!).val))
    (inv := fun (len_, _, _) => LeAll len_.val 15)
  · rintro ⟨len_, kraft_, q_⟩ hlen_
    dsimp only at hlen_
    simp only [slot.a_a_kraft_fix_loop.body]
    step*
    · -- one code gets one bit longer: the second component of the measure drops
      have hq : (sym.val[q_.val]!).val % 512 = s2.val := by
        rw [getElem!_pos sym.val q_.val (by scalar_tac), ← i_post]; scalar_tac
      have ha : a.val[s2.val]! = i5 := by
        rw [a_post, Array.set_val_eq, getElem!_pos _ _ (by simp; scalar_tac), List.getElem_set_self]
      have hl : len_.val[s2.val]! = i2 := by
        rw [getElem!_pos _ _ (by scalar_tac), ← i2_post]
      refine ⟨?_, ?_⟩
      · rw [a_post, Array.set_val_eq]; exact LeAll_set hlen_ _ _ (by scalar_tac)
      · rw [hq, ha, hl]; scalar_tac
    · -- the next symbol: the first component drops
      exact ⟨hlen_, by scalar_tac⟩
  · exact hlen
@[local step]
theorem a_kraft_fix_spec (sym m) (len : Array Std.U32 512#usize) (kraft0) (hlen : LeAll len.val 15) :
    slot.a_a_kraft_fix sym m len kraft0 ⦃ fun r => LeAll r.val 15 ⦄ := by
  unfold slot.a_a_kraft_fix
  step*
@[local step]
theorem a_lighter_spec (w a) (b : Std.Usize) (m k) (hb : b.val ≤ 4096) :
    slot.a_a_lighter w a b m k ⦃ fun r => r.2.1.val ≤ a.val + 1 ∧ r.2.2.val ≤ b.val + 1 ⦄ := U1! slot.a_a_lighter
@[local step]
theorem a_sorted_insert_loop_spec (sym freq fv) (j : Std.Usize) (hj : j.val < 512) :
    slot.a_a_sorted_insert_loop sym freq fv j ⦃ fun r => r.2.val < 512 ⦄ := by
  rw [slot.a_a_sorted_insert_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, j_) => j_.val)
    (inv := fun (_, j_) => j_.val < 512)
  · rintro ⟨sym_, j_⟩ hinv
    simp only [slot.a_a_sorted_insert_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hj
@[local step]
theorem a_sorted_insert_spec (sym freq m v) :
    slot.a_a_sorted_insert sym freq m v ⦃ fun _ => True ⦄ := U1! slot.a_a_sorted_insert
@[local step]
theorem a_huff_lengths_loop0_spec (freq n) (len : Array Std.U32 512#usize) (sym) (m i : Std.Usize)
    (hm : m.val ≤ i.val) (hi : i.val ≤ 512) (hlen : LeAll len.val 15) :
    slot.a_a_huff_lengths_loop0 freq n len sym m i ⦃ fun r => r.2.2.val ≤ 512 ∧ LeAll r.1.val 15 ⦄ := by
  rw [slot.a_a_huff_lengths_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, i_) => 512 - i_.val)
    (inv := fun (len_, _, m_, i_) => m_.val ≤ i_.val ∧ i_.val ≤ 512 ∧ LeAll len_.val 15)
  · rintro ⟨len_, sym_, m_, i_⟩ ⟨hm_, hi_, hlen_⟩
    simp only [slot.a_a_huff_lengths_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [a_post, Array.set_val_eq]; exact LeAll_set hlen_ _ _ (by scalar_tac)
  · exact ⟨hm, hi, hlen⟩
@[local step]
theorem a_huff_lengths_loop1_spec (freq sym m i w) :
    slot.a_a_huff_lengths_loop1 freq sym m i w ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_huff_lengths_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (i_, w_) => m.val - i_.val)
    (inv := fun _ => True)
  · rintro ⟨i_, w_⟩ _
    simp only [slot.a_a_huff_lengths_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_huff_lengths_loop2_spec (m : Std.Usize) (w par) (a b k : Std.Usize) (hm : m.val ≤ 512)
    (ha : a.val ≤ 2 * k.val) (hb : b.val ≤ 2 * k.val) (hk : k.val ≤ 1024) :
    slot.a_a_huff_lengths_loop2 m w par a b k ⦃ fun r => r.2.val ≤ 1024 ⦄ := by
  rw [slot.a_a_huff_lengths_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, k_) => 1024 - k_.val)
    (inv := fun (_, _, a_, b_, k_) => a_.val ≤ 2 * k_.val ∧ b_.val ≤ 2 * k_.val ∧ k_.val ≤ 1024)
  · rintro ⟨w_, par_, a_, b_, k_⟩ ⟨ha_, hb_, hk_⟩
    simp only [slot.a_a_huff_lengths_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨ha, hb, hk⟩
@[local step]
theorem a_huff_lengths_loop3_spec (par d j) :
    slot.a_a_huff_lengths_loop3 par d j ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_huff_lengths_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun (d_, j_) => j_.val)
    (inv := fun _ => True)
  · rintro ⟨d_, j_⟩ _
    simp only [slot.a_a_huff_lengths_loop3.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_huff_lengths_loop4_spec (len : Array Std.U32 512#usize) (sym m i d kraft) (hlen : LeAll len.val 15) :
    slot.a_a_huff_lengths_loop4 len sym m i d kraft ⦃ fun r => LeAll r.1.val 15 ⦄ := by
  rw [slot.a_a_huff_lengths_loop4]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i_, _) => m.val - i_.val)
    (inv := fun (len_, _, _) => LeAll len_.val 15)
  · rintro ⟨len_, i_, kraft_⟩ hlen_
    dsimp only at hlen_
    simp only [slot.a_a_huff_lengths_loop4.body]
    step*
    repeat' (split <;> step*)
    all_goals try scalar_tac
    all_goals
      refine ⟨?_, by scalar_tac⟩
      rw [a_post, Array.set_val_eq]; exact LeAll_set hlen_ _ _ (by scalar_tac)
  · exact hlen
@[local step]
theorem a_huff_lengths_spec (freq n) (len : Array Std.U32 512#usize) (hlen : LeAll len.val 15) :
    slot.a_a_huff_lengths freq n len ⦃ fun r => LeAll r.val 15 ⦄ := by
  rw [slot.a_a_huff_lengths]
  step*
  repeat' (split <;> step*)
  all_goals try scalar_tac
  all_goals apply engA_LeAll_set_of_eq (by assumption) (by assumption) (by scalar_tac)
@[local step]
theorem a_set_costs_huff_loop0_spec (lf0 lf z) :
    slot.a_a_set_costs_huff_loop0 lf0 lf z ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_huff_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (lf_, z_) => 286 - z_.val)
    (inv := fun _ => True)
  · rintro ⟨lf_, z_⟩ _
    simp only [slot.a_a_set_costs_huff_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_huff_loop1_spec (df dd i) :
    slot.a_a_set_costs_huff_loop1 df dd i ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_huff_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (dd_, i_) => 30 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨dd_, i_⟩ _
    simp only [slot.a_a_set_costs_huff_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_huff_loop2_spec (lf i tl) :
    slot.a_a_set_costs_huff_loop2 lf i tl ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_huff_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (i_, tl_) => 286 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨i_, tl_⟩ _
    simp only [slot.a_a_set_costs_huff_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_huff_loop3_spec (df i td) :
    slot.a_a_set_costs_huff_loop3 df i td ⦃ fun _ => True ⦄ := U3! slot.a_a_set_costs_huff_loop3 slot.a_a_set_costs_huff_loop3.body
@[local step]
theorem a_set_costs_huff_loop4_spec (lit) (hl : Array Std.U32 512#usize) (i) (ul : Std.U32) (hhl : LeAll hl.val 15) :
    slot.a_a_set_costs_huff_loop4 lit hl i ul ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_huff_loop4]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i_) => 256 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨lit_, i_⟩ _
    simp only [slot.a_a_set_costs_huff_loop4.body]
    step*
    repeat' (split <;> step*)
    all_goals try (have := LeAll_get hhl i_.val (by scalar_tac))
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_huff_loop5_spec (lc) (hl : Array Std.U32 512#usize) (i) (ul : Std.U32) (hhl : LeAll hl.val 15) (hul : ul.val ≤ 1152) :
    slot.a_a_set_costs_huff_loop5 lc hl i ul ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_huff_loop5]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i_) => 259 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨lc_, i_⟩ _
    simp only [slot.a_a_set_costs_huff_loop5.body]
    step*
    repeat' (split <;> step*)
    all_goals try (have := LeAll_get hhl i2.val (by scalar_tac))
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_huff_loop6_spec (dc) (i : Std.Usize) (hd : Array Std.U32 512#usize) (ud : Std.U32) (hhd : LeAll hd.val 15) (hud : ud.val ≤ 1152) :
    slot.a_a_set_costs_huff_loop6 dc i hd ud ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_huff_loop6]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i_) => 30 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨dc_, i_⟩ _
    simp only [slot.a_a_set_costs_huff_loop6.body]
    step*
    repeat' (split <;> step*)
    all_goals try (have := LeAll_get hhd i_.val (by scalar_tac))
    all_goals scalar_tac
  · trivial
@[local step]
theorem a_set_costs_huff_spec (lf0 df lit lc dc) :
    slot.a_a_set_costs_huff lf0 df lit lc dc ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_set_costs_huff]
  step*
  all_goals exact engA_LeAll_repeat _ _ _ (by simp)
set_option hygiene false in
local notation "U4!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun k_ => lim.val - k_.val)
    (inv := fun _ => True)
  · rintro k_ _
    simp only [q1__]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem a_shared_loop_spec (s : Slice Std.U8) (a b lim : Std.Usize) (k)
    (ha : a.val + lim.val ≤ s.length) (hb : b.val + lim.val ≤ s.length) :
    slot.a_a_shared_loop s a b lim k ⦃ fun _ => True ⦄ := U4! slot.a_a_shared_loop slot.a_a_shared_loop.body
@[local step]
theorem a_shared_spec (s : Slice Std.U8) (a b lim : Std.Usize)
    (ha : a.val + lim.val ≤ s.length) (hb : b.val + lim.val ≤ s.length) :
    slot.a_a_shared s a b lim ⦃ fun _ => True ⦄ := U1! slot.a_a_shared
@[local step]
theorem a_word_at_spec (s) (i : Std.Usize) (hi : i.val ≤ 2 ^ 31) :
    slot.a_a_word_at s i ⦃ fun _ => True ⦄ := U1! slot.a_a_word_at
@[local step]
theorem a_word_pair_spec (s) (a b : Std.Usize) (ha : a.val ≤ 2 ^ 31) (hb : b.val ≤ 2 ^ 31) :
    slot.a_a_word_pair s a b ⦃ fun _ => True ⦄ := U1! slot.a_a_word_pair
@[local step]
theorem a_probe_loop_spec (s) (p q k : Std.Usize) (w) (hp : p.val ≤ 2 ^ 30) (hq : q.val ≤ 2 ^ 30) (hk : k.val ≤ 258) :
    slot.a_a_probe_loop s p q k w ⦃ fun r => r.1.val ≤ 258 ⦄ := by
  rw [slot.a_a_probe_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (k_, _) => 258 - k_.val)
    (inv := fun (k_, _) => k_.val ≤ 258)
  · rintro ⟨k_, ⟨w0, w1⟩⟩ hinv
    simp only [slot.a_a_probe_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hk
@[local step]
theorem a_probe_spec (s) (p q k : Std.Usize) (hp : p.val ≤ 2 ^ 30) (hq : q.val ≤ 2 ^ 30) (hk : k.val ≤ 258) :
    slot.a_a_probe s p q k ⦃ fun r => r.1.val ≤ 258 ⦄ := U1! slot.a_a_probe
@[local step]
theorem a_tree_insert_loop_spec (s : Slice Std.U8) (kid) (pos depth oldest : Std.Usize) (mb) (cur best lo_at hi_at lo_len hi_len steps : Std.Usize)
    (hpos : pos.val + 266 ≤ s.length) (hn26 : s.length < 67108864) (hlo : lo_len.val ≤ 258) (hhi : hi_len.val ≤ 258) (hbest : 2 ≤ best.val) :
    slot.a_a_tree_insert_loop s kid pos depth mb oldest cur best lo_at hi_at lo_len hi_len steps ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_tree_insert_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, steps_) => depth.val - steps_.val)
    (inv := fun (_, _, _, best_, _, _, lo_len_, hi_len_, _) => lo_len_.val ≤ 258 ∧ hi_len_.val ≤ 258 ∧ 2 ≤ best_.val)
  · rintro ⟨kid_, mb_, cur_, best_, lo_at_, hi_at_, lo_len_, hi_len_, steps_⟩ ⟨hlo_, hhi_, hbest_⟩
    simp only [slot.a_a_tree_insert_loop.body, engA_ite_ok]
    step*
    · split <;> omega
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.Usize) => 2 ≤ x.2.val)
    · split
      · step*
        repeat' (split <;> step*)
        all_goals scalar_tac
      · step*
    rintro ⟨mb1, best1⟩ hb1
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Array Std.U32 65536#usize × Std.Usize × Std.Usize × Std.Usize ×
        Std.Usize × Std.Usize) => x.2.2.2.2.1.val ≤ 258 ∧ x.2.2.2.2.2.val ≤ 258)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ⟨kid1, cur1, lo_at1, hi_at1, lo_len2, hi_len1⟩ ⟨hl2, hh1⟩
    step*
    all_goals scalar_tac
  · exact ⟨hlo, hhi, hbest⟩
@[local step]
theorem a_tree_insert_spec (s : Slice Std.U8) (head kid h3 rct) (pos : Std.Usize) (pre depth mb) (hpos : pos.val + 266 ≤ s.length)
    (hn26 : s.length < 67108864) :
    slot.a_a_tree_insert s head kid h3 rct pos pre depth mb ⦃ fun _ => True ⦄ := by
  obtain ⟨q, t, h, c3, cr, cur⟩ := pre
  rw [slot.a_a_tree_insert]
  apply WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
  · split
    all_goals step*
  rintro oldest -
  step*
  apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.Usize) => 2 ≤ x.2.val)
  · repeat' (split <;> step*)
    all_goals scalar_tac
  rintro ⟨mb1, best⟩ hb
  step*
  apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.Usize) => 2 ≤ x.2.val)
  · repeat' (split <;> step*)
    all_goals scalar_tac
  rintro ⟨mb2, best1⟩ hb1
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac
set_option maxHeartbeats 4000000 in
@[local step]
theorem a_find_all_loop_spec (i : Std.U32) (s : Slice Std.U8) (mp : alloc.vec.Vec Std.U32) (mb depth) (skip n : Std.Usize) (head kid h3 rct) (i1 cl cd : Std.Usize) (nq nt nh n3 nr nc)
    (hn : n.val = s.length) (hn26 : s.length < 67108864) (hi : i.val < 32) (hskip : 3 ≤ skip.val)
    (hmp : mp.length ≤ i1.val + 1) (hcd : 1 ≤ cd.val) :
    slot.a_a_find_all_loop i s mp mb depth skip n head kid h3 rct i1 cl cd nq nt nh n3 nr nc ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_find_all_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, i1_, _, _, _, _, _, _, _, _) => n.val - i1_.val)
    (inv := fun ((mp_ : alloc.vec.Vec Std.U32), _, _, _, _, _, (i1_ : Std.Usize), _, (cd_ : Std.Usize), _, _, _, _, _, _) =>
      mp_.length ≤ i1_.val + 1 ∧ 1 ≤ cd_.val)
  · rintro ⟨mp_, mb_, head_, kid_, h3_, rct_, i1_, cl_, cd_, nq_, nt_, nh_, n3_, nr_, nc_⟩ ⟨hmp_, hcd_⟩
    unfold slot.a_a_find_all_loop.body
    simp only [engA_ite_ok, engA_ite_pair]
    step*
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.Array Std.U32 65536#usize × Std.Array Std.U32 65536#usize ×
        Std.Array Std.U32 32768#usize × Std.Array Std.U32 65536#usize × Std.Usize × Std.Usize × Std.U64 × Std.Usize ×
        Std.Usize × Std.Usize × Std.Usize × Std.Usize) => 1 ≤ x.2.2.2.2.2.2.1.val)
    · split
      · step*
        · -- a searched or skipped position (at least 266 bytes left)
          apply WP.spec_bind (Pₘ := fun (y : alloc.vec.Vec Std.U32 × Std.Array Std.U32 65536#usize ×
              Std.Array Std.U32 65536#usize × Std.Array Std.U32 32768#usize × Std.Array Std.U32 65536#usize ×
              Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize) => 1 ≤ y.2.2.2.2.2.2.1.val)
          · split
            · -- skip: the covering match's remainder as the only record (guarded push)
              step*
              split
              all_goals step*
              all_goals scalar_tac
            · -- search: tree insertion, then the new covering match (its distance code >= 1)
              step*
              apply WP.spec_bind (Pₘ := fun (z : Std.Array Std.U32 65536#usize × Std.Array Std.U32 65536#usize ×
                  Std.Array Std.U32 32768#usize × Std.Array Std.U32 65536#usize × Std.Usize × Std.Usize) =>
                  1 ≤ z.2.2.2.2.2.val)
              · repeat' (split <;> step*)
                all_goals scalar_tac
              rintro ⟨head3, kid3, h33, rct3, cl2, cd2⟩ hcd2
              step*
          rintro ⟨v, a, a1, a2, a3, i17, i18, i19, i20, i21⟩ h18
          step*
        · -- one of the last positions: the latest 3-byte occurrence (guarded push)
          apply WP.spec_bind (Pₘ := fun (_ : alloc.vec.Vec Std.U32 × Std.Array Std.U32 32768#usize) => True)
          · repeat' (split <;> step*)
            all_goals scalar_tac
          rintro ⟨v, a⟩ -
          step*
      · step*
        apply WP.spec_bind (Pₘ := fun (_ : alloc.vec.Vec Std.U32 × Std.Array Std.U32 32768#usize) => True)
        · repeat' (split <;> step*)
          all_goals scalar_tac
        rintro ⟨v, a⟩ -
        step*
    rintro ⟨mb1, head1, kid1, h31, rct1, cl1, cd1, nq1, nt1, nh1, n31, nr1, nc1⟩ hcd1
    step*
    apply WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
    · split
      all_goals step*
    rintro cl2 -
    step*
    simp only [alloc.vec.Vec.length, *, List.length_append, List.length_singleton]
    scalar_tac
  · exact ⟨hmp, hcd⟩
@[local step]
theorem a_find_all_spec (s : Slice Std.U8) (mp : alloc.vec.Vec Std.U32) (mb depth) (skip : Std.Usize)
    (hn26 : s.length < 67108864) (hskip : 3 ≤ skip.val) (hmp : mp.length = 0) :
    slot.a_a_find_all s mp mb depth skip ⦃ fun _ => True ⦄ := by
  have hhb := A_HB_bounds
  rw [slot.a_a_find_all]
  step*
  all_goals try simp only [alloc.vec.Vec.length, *, List.length_append, List.length_singleton]
  all_goals scalar_tac
@[local step]
theorem a_engine_loop0_spec (n : Std.Usize) (cost) (i : Std.Usize) (hn : n.val < 67108864) (hc : cost.length = i.val) :
    slot.a_a_engine_loop0 n cost i ⦃ fun _ => True ⦄ := by
  rw [slot.a_a_engine_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i_) => n.val + 1 - i_.val)
    (inv := fun (cost_, i_) => cost_.length = i_.val)
  · rintro ⟨cost_, i_⟩ hc_
    simp only [slot.a_a_engine_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals try simp only [alloc.vec.Vec.length, *, List.length_append, List.length_singleton]
    all_goals scalar_tac
  · exact hc
@[local step]
theorem a_engine_loop1_loop0_spec (input : Slice Std.U8) (ch) (n : Std.Usize) (mp mb cost lit lc dc lf df bl bd sl sd) (rot p0 need passes sampled pe k p1 t : Std.Usize)
    (hn : n.val = input.length) (hn26 : n.val < 67108864) (hp0 : p0.val < n.val) (hpe : p0.val ≤ pe.val ∧ pe.val ≤ n.val)
    (hpe' : pe.val = n.val ∨ p0.val + slot.A_A_MARGIN.val ≤ pe.val)
    (hneed : need.val ≤ 65536) (ht : t.val ≤ need.val) (hp1 : p0.val ≤ p1.val ∧ p1.val ≤ p0.val + 511 * t.val) :
    slot.a_a_engine_loop1_loop0 input ch n mp mb cost lit lc dc lf df bl bd sl sd rot p0 need passes sampled pe k p1 t ⦃ fun r =>
      r.2.2.2.2.2.2.2.2.2.2.val ≤ need.val ∧ p0.val ≤ r.2.2.2.2.2.2.2.2.2.1.val ∧
      r.2.2.2.2.2.2.2.2.2.1.val ≤ p0.val + 511 * r.2.2.2.2.2.2.2.2.2.2.val ⦄ := by
  have hbt := A_BLOCK_bounds
  have hseg := A_SEG_bounds
  rw [slot.a_a_engine_loop1_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, _, _, k_, _, _) => passes.val - k_.val)
    (inv := fun (_, _, _, _, _, _, _, _, _, (pe_ : Std.Usize), _, (p1_ : Std.Usize), (t_ : Std.Usize)) =>
      p0.val ≤ pe_.val ∧ pe_.val ≤ n.val ∧ (pe_.val = n.val ∨ p0.val + slot.A_A_MARGIN.val ≤ pe_.val) ∧
      t_.val ≤ need.val ∧ p0.val ≤ p1_.val ∧ p1_.val ≤ p0.val + 511 * t_.val)
  · rintro ⟨ch_, cost_, lit_, lc_, dc_, lf_, df_, sl_, sd_, pe_, k_, p1_, t_⟩ ⟨hpe0, hpe1, hpe2, ht_, hp10, hp11⟩
    simp only [slot.a_a_engine_loop1_loop0.body]
    step*
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × alloc.vec.Vec Std.U32 × Std.Array Std.U32 512#usize ×
        Std.Array Std.U32 32#usize × Std.Usize × Std.Usize × Std.Usize) =>
        p0.val ≤ x.2.2.2.2.1.val ∧ x.2.2.2.2.1.val ≤ n.val ∧
        (x.2.2.2.2.1.val = n.val ∨ p0.val + slot.A_A_MARGIN.val ≤ x.2.2.2.2.1.val) ∧
        x.2.2.2.2.2.2.val ≤ need.val ∧ p0.val ≤ x.2.2.2.2.2.1.val ∧ x.2.2.2.2.2.1.val ≤ p0.val + 511 * x.2.2.2.2.2.2.val)
    · split
      · step*
        · -- a sampled pass: the window end scales with the sampled bytes per token
          cases ‹Std.Usize × Std.Usize›
          step*
          apply WP.spec_bind (Pₘ := fun (z : alloc.vec.Vec Std.U32 × alloc.vec.Vec Std.U32 × Std.Array Std.U32 512#usize ×
              Std.Array Std.U32 32#usize × Std.Usize) => p0.val ≤ z.2.2.2.2.val ∧ z.2.2.2.2.val ≤ n.val ∧
              (z.2.2.2.2.val = n.val ∨ p0.val + slot.A_A_MARGIN.val ≤ z.2.2.2.2.val))
          · repeat' (split <;> step*)
            all_goals scalar_tac
          rintro ⟨v, v1, a, a1, i6⟩ hi6
          step*
          all_goals scalar_tac
        · -- a full pass: dynamic program, then the walk of the round's tokens
          apply WP.spec_bind (Pₘ := fun (lim : Std.Usize) => lim.val ≤ pe_.val)
          · split
            all_goals step*
            all_goals scalar_tac
          rintro lim hlim
          step*
          cases ‹Std.Usize × Std.Usize›
          step*
          apply WP.spec_bind (Pₘ := fun (z : Std.Array Std.U32 512#usize × Std.Array Std.U32 32#usize × Std.Usize) =>
              p0.val ≤ z.2.2.val ∧ z.2.2.val ≤ n.val ∧ (z.2.2.val = n.val ∨ p0.val + slot.A_A_MARGIN.val ≤ z.2.2.val))
          · repeat' (split <;> step*)
            all_goals scalar_tac
          rintro ⟨a, a1, i4⟩ hi4
          step*
          all_goals scalar_tac
        · -- a full pass: dynamic program, then the walk of the round's tokens
          apply WP.spec_bind (Pₘ := fun (lim : Std.Usize) => lim.val ≤ pe_.val)
          · split
            all_goals step*
            all_goals scalar_tac
          rintro lim hlim
          step*
          cases ‹Std.Usize × Std.Usize›
          step*
          apply WP.spec_bind (Pₘ := fun (z : Std.Array Std.U32 512#usize × Std.Array Std.U32 32#usize × Std.Usize) =>
              p0.val ≤ z.2.2.val ∧ z.2.2.val ≤ n.val ∧ (z.2.2.val = n.val ∨ p0.val + slot.A_A_MARGIN.val ≤ z.2.2.val))
          · repeat' (split <;> step*)
            all_goals scalar_tac
          rintro ⟨a, a1, i4⟩ hi4
          step*
          all_goals scalar_tac
      · step*
        · -- a full pass: dynamic program, then the walk of the round's tokens
          apply WP.spec_bind (Pₘ := fun (lim : Std.Usize) => lim.val ≤ pe_.val)
          · split
            all_goals step*
            all_goals scalar_tac
          rintro lim hlim
          step*
          cases ‹Std.Usize × Std.Usize›
          step*
          apply WP.spec_bind (Pₘ := fun (z : Std.Array Std.U32 512#usize × Std.Array Std.U32 32#usize × Std.Usize) =>
              p0.val ≤ z.2.2.val ∧ z.2.2.val ≤ n.val ∧ (z.2.2.val = n.val ∨ p0.val + slot.A_A_MARGIN.val ≤ z.2.2.val))
          · repeat' (split <;> step*)
            all_goals scalar_tac
          rintro ⟨a, a1, i4⟩ hi4
          step*
          all_goals scalar_tac
    rintro ⟨ch1, cost1, lf1, df1, pe1, p11, t1⟩ ⟨hq0, hq1, hq2, hq3, hq4, hq5⟩
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hpe.1, hpe.2, hpe', ht, hp1.1, hp1.2⟩
@[local step]
theorem a_engine_loop1_spec (input : Slice Std.U8) (ch first_passes fspass passes_k) (n : Std.Usize) (mp mb cost lit lc dc lf df bl bd sl sd zl zd) (rot spn p0 used bpt : Std.Usize)
    (hn : n.val = input.length) (hn26 : n.val < 67108864) (hused : used.val < slot.A_BLOCK_TOKENS.val) (hbpt : 256 ≤ bpt.val ∧ bpt.val ≤ 65536) :
    slot.a_a_engine_loop1 input ch first_passes fspass passes_k n mp mb cost lit lc dc lf df bl bd sl sd zl zd rot spn p0 used bpt ⦃ fun _ => True ⦄ := by
  have hbt := A_BLOCK_bounds
  rw [slot.a_a_engine_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, _, _, _, p0_, _, _) => n.val - p0_.val)
    (inv := fun (_, _, _, _, _, _, _, _, _, _, _, _, used_, bpt_) => used_.val < slot.A_BLOCK_TOKENS.val ∧
      256 ≤ bpt_.val ∧ bpt_.val ≤ 130816)
  · rintro ⟨ch_, cost_, lit_, lc_, dc_, lf_, df_, bl_, bd_, sl_, sd_, p0_, used_, bpt_⟩ ⟨hused_, hbpt0, hbpt1⟩
    simp only [slot.a_a_engine_loop1.body, engA_ite_ok]
    step*
    · -- the token estimate `need * bpt` fits in 32 bits
      have : need.val * bpt_.val ≤ 16384 * 130816 := Nat.mul_le_mul (by scalar_tac) hbpt1
      scalar_tac
    apply WP.spec_bind (Pₘ := fun (pe : Std.Usize) => p0_.val ≤ pe.val ∧ pe.val ≤ n.val ∧
      (pe.val = n.val ∨ p0_.val + slot.A_A_MARGIN.val ≤ pe.val))
    · split
      all_goals step*
      all_goals scalar_tac
    rintro pe hpe
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Array Std.U32 512#usize × Std.Array Std.U32 32#usize × Std.Usize) =>
      x.2.2.val < slot.A_BLOCK_TOKENS.val)
    · split
      all_goals step*
      all_goals scalar_tac
    rintro ⟨bl1, bd1, used2⟩ hu2
    step*
    all_goals try (
      have hdiv : bpt1.val ≤ 130816 := by
        rw [bpt1_post]; apply Nat.div_le_of_le_mul; scalar_tac
      by_cases hb : bpt1 < 256#usize
      all_goals simp only [hb, ite_true, ite_false])
    all_goals scalar_tac
  · -- the invariant allows up to 511 bytes per token (the snapshot never clamps `bpt` from above)
    exact ⟨hused, hbpt.1, by omega⟩
@[local step]
theorem a_engine_spec (input : Slice Std.U8) (ch) (depth skip first_passes fspass passes_k spass : Std.Usize)
    (hn : input.length < 67108864) (h1 : depth.val ≤ 65536) (h2 : skip.val ≤ 65536) (h2' : 3 ≤ skip.val)
    (h3 : first_passes.val ≤ 65536) (h4 : fspass.val ≤ 65536) (h5 : passes_k.val ≤ 65536) (h6 : spass.val ≤ 65536) :
    slot.a_a_engine input ch depth skip first_passes fspass passes_k spass ⦃ fun _ => True ⦄ := by
  have hbt := A_BLOCK_bounds
  rw [slot.a_a_engine]
  step*
  all_goals rfl
@[local step]
theorem B_FULL_spec : slot.A_B_FULL ⦃ fun x => x.val = 536870912 ⦄ := by
  unfold slot.A_B_FULL; step*
@[local step]
theorem B_KEEPMAX_spec : slot.A_B_KEEPMAX ⦃ fun _ => True ⦄ := by
  unfold slot.A_B_KEEPMAX
  have h := numBits_ge
  step*
theorem engB_vec_index_mut {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize) :
    alloc.vec.Vec.index_mut_usize v i =
      (do let x ← alloc.vec.Vec.index_usize v i; ok (x, alloc.vec.Vec.set v i)) := by
  unfold alloc.vec.Vec.index_mut_usize
  cases alloc.vec.Vec.index_usize v i <;> rfl
theorem engB_u32_shr15 (x : Std.U32) : x.val >>> 15 < 131072 := by
  rw [Nat.shiftRight_eq_div_pow]
  have : x.val < 2 ^ 32 := by scalar_tac
  omega
theorem engB_arr_index_le {n : Std.Usize} (a : Std.Array Std.U32 n) (j : Std.Usize) (B : Nat)
    (h : LeAll a.val B) (hj : j.val < a.length) :
    a.index_usize j ⦃ fun x => x = a.val[j.val] ∧ x.val ≤ B ⦄ := by
  have := Std.Array.index_usize_spec a j hj
  apply WP.spec_mono this
  intro x hx
  exact ⟨hx, hx ▸ LeAll_get h j.val (by simpa using hj)⟩
theorem engB_arr_update_le {n : Std.Usize} (a : Std.Array Std.U32 n) (j : Std.Usize) (x : Std.U32)
    (B : Nat) (h : LeAll a.val B) (hx : x.val < B + 1) (hj : j.val < a.length) :
    a.update j x ⦃ fun r => r = a.set j x ∧ LeAll r.val B ⦄ := by
  have := Std.Array.update_spec a j x hj
  apply WP.spec_mono this
  intro r hr
  exact ⟨hr, by rw [hr, Std.Array.set_val_eq]; exact LeAll_set h _ _ (by omega)⟩
theorem engB_arr_index_mut_spec {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (hbound : i.val < v.length) :
    v.index_mut_usize i ⦃ x back => back = Std.Array.set v i ⦄ := by
  have := Std.Array.index_mut_usize_spec v i hbound
  apply WP.spec_mono this
  rintro ⟨x, back⟩ ⟨_, h⟩
  exact h
theorem engB_arr_index_le_d {n : Std.Usize} (a : Std.Array Std.U32 n) (j : Std.Usize) (B : Nat)
    (h : LeAll a.val B) (hj : j.val < a.length) :
    a.index_usize j ⦃ fun x => x = a.val[j.val] ∧ x.val ≤ B ⦄ := engB_arr_index_le a j B h hj
theorem engB_arr_update_le_d {n : Std.Usize} (a : Std.Array Std.U32 n) (j : Std.Usize) (x : Std.U32)
    (B : Nat) (h : LeAll a.val B) (hx : x.val < B + 1) (hj : j.val < a.length) :
    a.update j x ⦃ fun r => r = a.set j x ∧ LeAll r.val B ⦄ := engB_arr_update_le a j x B h hx hj
theorem engB_arr_index_le_g {n : Std.Usize} (a : Std.Array Std.U32 n) (j : Std.Usize) (B : Nat)
    (h : LeAll a.val B) (hj : j.val < a.length) :
    a.index_usize j ⦃ fun x => x = a.val[j.val] ∧ x.val ≤ B ⦄ := engB_arr_index_le a j B h hj
theorem engB_arr_update_le_g {n : Std.Usize} (a : Std.Array Std.U32 n) (j : Std.Usize) (x : Std.U32)
    (B : Nat) (h : LeAll a.val B) (hx : x.val < B + 1) (hj : j.val < a.length) :
    a.update j x ⦃ fun r => r = a.set j x ∧ LeAll r.val B ⦄ := engB_arr_update_le a j x B h hx hj
theorem engB_arr_index_mut_spec_b {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (hbound : i.val < v.length) :
    v.index_mut_usize i ⦃ x back => back = Std.Array.set v i ⦄ := engB_arr_index_mut_spec v i hbound
theorem engB_arr_index_mut_spec_c {α : Type} {n : Std.Usize} (v : Std.Array α n) (i : Std.Usize)
    (hbound : i.val < v.length) :
    v.index_mut_usize i ⦃ x back => back = Std.Array.set v i ⦄ := engB_arr_index_mut_spec v i hbound
theorem engB_arr_index_le_e {n : Std.Usize} (a : Std.Array Std.U32 n) (j : Std.Usize) (B : Nat)
    (h : LeAll a.val B) (hj : j.val < a.length) :
    a.index_usize j ⦃ fun x => x = a.val[j.val] ∧ x.val ≤ B ⦄ := engB_arr_index_le a j B h hj
theorem engB_LeAll_u32 (l : List Std.U32) : LeAll l 4294967295 := fun j hj => by scalar_tac
theorem engB_wsub_val (x y : Std.Usize) (h : y.val ≤ x.val) :
    (core.num.Usize.wrapping_sub x y).val = x.val - y.val := by
  rw [core.num.Usize.wrapping_sub_val_eq]
  have hx : x.val < UScalar.size .Usize := by
    have := x.hBounds; simp only [UScalar.size]; exact this
  rw [show x.val + (UScalar.size .Usize - y.val) = (x.val - y.val) + UScalar.size .Usize by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
theorem engB_u32_shr2 (x : Std.U32) : x.val >>> 2 < 1073741824 := by
  rw [Nat.shiftRight_eq_div_pow]
  have : x.val < 2 ^ 32 := by scalar_tac
  omega
def engB_Blk (l : List Std.U32) (base K : Nat) : Prop :=
  ∀ z, z < slot.A_B_FSZ.val → ∀ x, l[base + z]? = some x → x.val ≤ K
def engB_Zero (l : List Std.U32) (base n : Nat) : Prop :=
  ∀ z, z < n → ∀ x, l[base + z]? = some x → x.val = 0
theorem engB_Blk_mono {l : List Std.U32} {base K K' : Nat} (h : engB_Blk l base K) (hK : K ≤ K') :
    engB_Blk l base K' := fun z hz x hx => le_trans (h z hz x hx) hK
theorem engB_Blk_of {l : List Std.U32} {base K base' K' : Nat} (h : engB_Blk l base K)
    (hh : base = base' ∧ K ≤ K') : engB_Blk l base' K' := by
  obtain ⟨rfl, hK⟩ := hh; exact engB_Blk_mono h hK
theorem engB_Blk_get {l : List Std.U32} {base K : Nat} (h : engB_Blk l base K) {idx : Nat}
    {x : Std.U32} (h1 : base ≤ idx) (h2 : idx < base + slot.A_B_FSZ.val) (hl : idx < l.length)
    (hx : x = l[idx]) : x.val ≤ K := by
  have hx' : l[base + (idx - base)]? = some x := by
    rw [show base + (idx - base) = idx by omega, hx]; exact List.getElem?_eq_getElem hl
  exact h (idx - base) (by omega) _ hx'
theorem engB_Blk_set {l : List Std.U32} {base K K' : Nat} (h : engB_Blk l base K) (idx : Nat)
    (v : Std.U32) (hv : v.val ≤ K') (hK : K ≤ K') : engB_Blk (l.set idx v) base K' := by
  intro z hz x hx
  rw [List.getElem?_set] at hx
  split at hx
  · split at hx
    · cases hx; exact hv
    · cases hx
  · exact le_trans (h z hz x hx) hK
theorem engB_Zero_zero (l : List Std.U32) (base : Nat) : engB_Zero l base 0 :=
  fun z hz => absurd hz (Nat.not_lt_zero z)
theorem engB_Zero_set {l : List Std.U32} {base n : Nat} (h : engB_Zero l base n) (idx : Nat)
    (hidx : idx = base + n) : engB_Zero (l.set idx 0#u32) base (n + 1) := by
  intro z hz x hx
  rw [List.getElem?_set] at hx
  split at hx
  · split at hx
    · cases hx; rfl
    · cases hx
  · exact h z (by omega) x hx
theorem engB_Zero_push {l : List Std.U32} {base n : Nat} (h : engB_Zero l base n)
    (hlen : l.length = base + n) : engB_Zero (l ++ [0#u32]) base (n + 1) := by
  intro z hz x hx
  by_cases hzn : z < n
  · rw [List.getElem?_append_left (by omega)] at hx
    exact h z hzn x hx
  · have : base + z = l.length := by omega
    rw [this, List.getElem?_concat_length] at hx
    cases hx; rfl
theorem engB_Zero_Blk {l : List Std.U32} {base n : Nat} (h : engB_Zero l base n)
    (hn : slot.A_B_FSZ.val ≤ n) : engB_Blk l base 0 :=
  fun z hz x hx => le_of_eq (h z (by omega) x hx)
@[local step]
theorem b_put_spec (rs) (rn : Std.Usize) (v) (hrn : rn.val < 4294967295) (hrs : rn.val ≤ rs.length) :
    slot.a_b_put rs rn v ⦃ fun r => r.1.val = rn.val + 1 ∧ r.1.val ≤ r.2.length ⦄ := by
  rw [slot.a_b_put]
  split
  · step*
    obtain ⟨x1, x2⟩ := x
    simp only at x_post1 x_post2 ⊢
    subst x_post2
    step*
    all_goals simp_all [alloc.vec.Vec.set_val_eq]; scalar_tac
  · step*
    all_goals first
      | scalar_tac
      | (have : rs1.length = rs.length + 1 := by simp [rs1_post]
         scalar_tac)
@[local step]
theorem b_plan_seg_loop_spec (a m : Std.Usize) (cc : alloc.vec.Vec Std.U64) (plan) (j : Std.Usize)
    (ham : a.val + m.val ≤ Std.Usize.max) (hj : j.val ≤ m.val) (hm : m.val < cc.length) :
    slot.a_b_plan_seg_loop a m cc plan j ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_plan_seg_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, j') => j'.val)
    (inv := fun (_, j') => j'.val ≤ m.val)
  · rintro ⟨plan', j'⟩ hj'
    simp only [slot.a_b_plan_seg_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals (try have := engB_u32_shr15 v); scalar_tac
  · exact hj
@[local step]
theorem b_plan_seg_spec (a m : Std.Usize) (cc : alloc.vec.Vec Std.U64) (plan)
    (ham : a.val + m.val ≤ Std.Usize.max) (hm : m.val < cc.length) :
    slot.a_b_plan_seg a m cc plan ⦃ fun _ => True ⦄ := U1! slot.a_b_plan_seg
@[local step]
theorem b_dist_slot_spec (d) : slot.a_b_dist_slot d ⦃ fun r => r.val ≤ 29 ⦄ := by
  rw [slot.a_b_dist_slot]
  step*
  repeat' (split <;> step*)
  all_goals
    try (have hx : v.val = i.val := by
          rw [v_post, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)])
    try (have h1 := lz32_le_of_pow_le v 2 (by scalar_tac))
    try (have h2 := lz32_ge_of_lt_pow v 15 (by scalar_tac))
    scalar_tac
@[local step]
theorem b_len_code_spec (l) : slot.a_b_len_code l ⦃ fun r => r.1.val ≤ 28 ∧ r.2.val ≤ 5 ⦄ := by
  rw [slot.a_b_len_code]
  step*
  repeat' (split <;> step*)
  all_goals
    try (have hx : v.val = i.val := by
          rw [v_post, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)])
    try (have h1 := lz32_le_of_pow_le v 3 (by scalar_tac))
    try (have h2 := lz32_ge_of_lt_pow v 8 (by scalar_tac))
    scalar_tac
set_option hygiene false in
local notation "U5!" q0__:max q1__:max q2__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, z') => q1__ - z'.val)
    (inv := fun (bf', z') => base.val + z'.val ≤ bf'.length ∧ bf.length ≤ bf'.length ∧
      engB_Zero bf'.val base.val z'.val)
  · rintro ⟨bf', z'⟩ ⟨h1, h2, h3⟩
    simp only [q2__]
    split
    · step*
      split
      · step*
        obtain ⟨x1, x2⟩ := x
        simp only at x_post1 x_post2 ⊢
        subst x_post2
        step*
        refine ⟨by simp; scalar_tac, by simp; scalar_tac, ?_, by scalar_tac⟩
        simp only [alloc.vec.Vec.set_val_eq]
        rw [show z1.val = z'.val + 1 by scalar_tac]
        exact engB_Zero_set h3 i.val (by scalar_tac)
      · step*
        have hl : bf1.length = bf'.length + 1 := by simp [bf1_post]
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        rw [bf1_post, show z1.val = z'.val + 1 by scalar_tac]
        exact engB_Zero_push h3 (by scalar_tac)
    · simp only [WP.spec_ok]
      exact ⟨by scalar_tac, h2, engB_Zero_Blk h3 (by scalar_tac)⟩
  · exact ⟨by simpa using hz, le_refl _, engB_Zero_zero _ _⟩)
@[local step]
theorem b_tally_plan_loop0_loop0_spec (bf) (base : Std.Usize)
    (hz : base.val ≤ bf.length) (hb : base.val + slot.A_B_FSZ.val ≤ 4294967295) :
    slot.a_b_tally_plan_loop0_loop0 bf base 0#usize ⦃ fun r => base.val + slot.A_B_FSZ.val ≤ r.length ∧
      bf.length ≤ r.length ∧ engB_Blk r.val base.val 0 ⦄ := U5! slot.a_b_tally_plan_loop0_loop0 slot.A_B_FSZ.val slot.a_b_tally_plan_loop0_loop0.body
theorem engB_tally_plan_tok (s : Slice Std.U8) (bf : alloc.vec.Vec Std.U32) (n pos f l v : Std.Usize)
    (K : Nat) (hn : n.val = s.length) (hpos : pos.val < n.val)
    (hf : f.val + slot.A_B_FSZ.val ≤ bf.length) (hblk : engB_Blk bf.val f.val K)
    (hK : K + 2 < 4294967295) :
    (if l ≥ 3#usize then do
        let i5 ← n - pos
        if l ≤ i5 then do
            let d ← v / 512#usize
            let (i6, _) ← slot.a_b_len_code l
            let i7 ← 257#usize + i6
            let i8 ← i7 % slot.A_B_FSZ
            let i9 ← f + i8
            let (i10, index_mut_back) ← bf.index_mut_usize i9
            let i11 ← i10 + 1#u32
            let i12 ← slot.a_b_dist_slot d
            let i13 ← 288#usize + i12
            let i14 ← i13 % slot.A_B_FSZ
            let i15 ← f + i14
            let (i16, index_mut_back1) ← (index_mut_back i11).index_mut_usize i15
            let i17 ← i16 + 1#u32
            let pos2 ← pos + l
            ok (index_mut_back1 i17, pos2)
          else do
            let i6 ← s.index_usize pos
            let i7 ← lift (UScalar.cast UScalarTy.Usize i6)
            let i8 ← f + i7
            let (i9, index_mut_back) ← bf.index_mut_usize i8
            let i10 ← i9 + 1#u32
            let pos2 ← pos + 1#usize
            ok (index_mut_back i10, pos2)
      else do
        let i6 ← s.index_usize pos
        let i7 ← lift (UScalar.cast UScalarTy.Usize i6)
        let i8 ← f + i7
        let (i9, index_mut_back) ← bf.index_mut_usize i8
        let i10 ← i9 + 1#u32
        let pos2 ← pos + 1#usize
        ok (index_mut_back i10, pos2)) ⦃ fun (x : alloc.vec.Vec Std.U32 × Std.Usize) =>
      x.1.length = bf.length ∧ pos.val < x.2.val ∧ x.2.val ≤ n.val ∧
        engB_Blk x.1.val f.val (K + (x.2.val - pos.val)) ⦄ := by
  split
  · step
    split
    · step*
      all_goals (try subst i10_post2)
      all_goals (try subst i16_post2)
      all_goals try
        (have hidx : f.val ≤ i9.val ∧ i9.val < f.val + slot.A_B_FSZ.val ∧ i9.val < bf.val.length := by
          scalar_tac
         have h10 := engB_Blk_get hblk hidx.1 hidx.2.1 hidx.2.2 i10_post1)
      all_goals try (have hb2 := engB_Blk_set hblk i9.val i11 (K' := K + 1) (by omega) (by omega))
      all_goals try
        (have hidx2 : f.val ≤ i15.val ∧ i15.val < f.val + slot.A_B_FSZ.val ∧
            i15.val < (bf.val.set i9.val i11).length := by
          rw [List.length_set]; scalar_tac
         have h16 := engB_Blk_get hb2 (x := i16) hidx2.1 hidx2.2.1 hidx2.2.2
          (by simp only [i16_post1, alloc.vec.Vec.set_val_eq]))
      all_goals try
        (have hb3 := engB_Blk_set hb2 i15.val i17 (K' := K + (pos2.val - pos.val))
          (by scalar_tac) (by scalar_tac))
      all_goals first
        | (refine ⟨by simp, by scalar_tac, by scalar_tac, ?_⟩
           simp only [alloc.vec.Vec.set_val_eq]; exact hb3)
        | scalar_tac
    · step*
      all_goals (try subst i9_post2)
      all_goals try
        (have hidx : f.val ≤ i8.val ∧ i8.val < f.val + slot.A_B_FSZ.val ∧ i8.val < bf.val.length := by
          scalar_tac
         have h9 := engB_Blk_get hblk hidx.1 hidx.2.1 hidx.2.2 i9_post1)
      all_goals try
        (have hb2 := engB_Blk_set hblk i8.val i10 (K' := K + (pos2.val - pos.val))
          (by scalar_tac) (by scalar_tac))
      all_goals first
        | (refine ⟨by simp, by scalar_tac, by scalar_tac, ?_⟩
           simp only [alloc.vec.Vec.set_val_eq]; exact hb2)
        | scalar_tac
  · step*
    all_goals (try subst i9_post2)
    all_goals try
      (have hidx : f.val ≤ i8.val ∧ i8.val < f.val + slot.A_B_FSZ.val ∧ i8.val < bf.val.length := by
        scalar_tac
       have h9 := engB_Blk_get hblk hidx.1 hidx.2.1 hidx.2.2 i9_post1)
    all_goals try
      (have hb2 := engB_Blk_set hblk i8.val i10 (K' := K + (pos2.val - pos.val))
        (by scalar_tac) (by scalar_tac))
    all_goals first
      | (refine ⟨by simp, by scalar_tac, by scalar_tac, ?_⟩
         simp only [alloc.vec.Vec.set_val_eq]; exact hb2)
      | scalar_tac
def engB_TPL (n : Nat) (bf bs : alloc.vec.Vec Std.U32) (nb pos t : Nat) : Prop :=
  (pos ≤ n ∧ t ≤ pos ∧ t ≤ nb * slot.A_BLOCK_TOKENS.val ∧ nb * slot.A_BLOCK_TOKENS.val < t + slot.A_BLOCK_TOKENS.val ∧
    nb * slot.A_B_FSZ.val ≤ bf.length ∧ nb ≤ bs.length) ∧
    (0 < nb → engB_Blk bf.val ((nb - 1) * slot.A_B_FSZ.val) pos)
theorem engB_TPL.mk {n : Nat} {bf bs : alloc.vec.Vec Std.U32} {nb pos t : Nat}
    (h1 : pos ≤ n ∧ t ≤ pos ∧ t ≤ nb * slot.A_BLOCK_TOKENS.val ∧
      nb * slot.A_BLOCK_TOKENS.val < t + slot.A_BLOCK_TOKENS.val ∧ nb * slot.A_B_FSZ.val ≤ bf.length ∧
      nb ≤ bs.length)
    (h2 : 0 < nb → engB_Blk bf.val ((nb - 1) * slot.A_B_FSZ.val) pos) : engB_TPL n bf bs nb pos t :=
  ⟨h1, h2⟩
@[local step]
theorem b_tally_plan_loop0_spec (s : Slice Std.U8) (plan) (bf bs : alloc.vec.Vec Std.U32) (n nb pos t : Std.Usize)
    (hn : n.val = s.length) (hn26 : n.val < 67108864)
    (hinv : engB_TPL n.val bf bs nb.val pos.val t.val) :
    slot.a_b_tally_plan_loop0 s plan bf bs n nb pos t ⦃ fun r =>
      r.2.2.val * slot.A_BLOCK_TOKENS.val ≤ n.val + slot.A_BLOCK_TOKENS.val ∧
      r.2.2.val * slot.A_B_FSZ.val ≤ r.1.length ∧
      (0 < r.2.2.val → engB_Blk r.1.val ((r.2.2.val - 1) * slot.A_B_FSZ.val) n.val) ⦄ := by
  rw [slot.a_b_tally_plan_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, pos', _) => n.val - pos'.val)
    (inv := fun (bf', bs', nb', pos', t') => engB_TPL n.val bf' bs' nb'.val pos'.val t'.val)
  · rintro ⟨bf', bs', nb', pos', t'⟩ ⟨⟨hp1, hp2, hp3, hp4, hp5, hp6⟩, hp7⟩
    simp only [slot.a_b_tally_plan_loop0.body]
    split
    · split
      · step*
        · -- a new block (t % BLOCK_TOKENS = 0)
          apply WP.spec_bind (Pₘ := fun (bs1 : alloc.vec.Vec Std.U32) => nb'.val < bs1.length)
          · split
            · step*
              all_goals first
                | scalar_tac
                | (simp only [alloc.vec.Vec.set_val_eq, List.length_set]; scalar_tac)
            · step*
              all_goals first
                | scalar_tac
                | (have : bs1.length = bs'.length + 1 := by simp [bs1_post]
                   scalar_tac)
          · intro bs1 hbs1
            step*
            apply WP.spec_bind (engB_tally_plan_tok s bf1 n pos' f l v 0 hn (by scalar_tac)
              (by scalar_tac) (by rw [show f.val = base.val by scalar_tac]; exact bf1_post3) (by norm_num))
            rintro ⟨bf2, pos1⟩ ⟨hb1, hb2, hb3, hb4⟩
            step*
            refine ⟨?_, by scalar_tac⟩
            apply engB_TPL.mk
            · scalar_tac
            · exact fun _ => engB_Blk_of hb4 (by scalar_tac)
        · -- the open block
          apply WP.spec_bind (engB_tally_plan_tok s bf' n pos' f l v pos'.val hn (by scalar_tac)
            (by scalar_tac) (engB_Blk_of (hp7 (by scalar_tac)) (by scalar_tac)) (by scalar_tac))
          rintro ⟨bf2, pos1⟩ ⟨hb1, hb2, hb3, hb4⟩
          step*
          refine ⟨?_, by scalar_tac⟩
          apply engB_TPL.mk
          · scalar_tac
          · exact fun _ => engB_Blk_of hb4 (by scalar_tac)
      · simp only [WP.spec_ok]
        exact ⟨by scalar_tac, hp5, fun h => engB_Blk_of (hp7 h) (by scalar_tac)⟩
    · simp only [WP.spec_ok]
      exact ⟨by scalar_tac, hp5, fun h => engB_Blk_of (hp7 h) (by scalar_tac)⟩
  · exact hinv
@[local step]
theorem b_tally_plan_spec (s : Slice Std.U8) (plan bf bs) (hn26 : s.length < 67108864) :
    slot.a_b_tally_plan s plan bf bs ⦃ fun r => r.1.val ≤ 1048576 ⦄ := by
  rw [slot.a_b_tally_plan]
  step*
  · unfold engB_TPL; simp
  · have := engB_Blk_get (bf1_post3 (by scalar_tac)) (by scalar_tac) (by scalar_tac) (by scalar_tac)
      i3_post1
    scalar_tac
@[local step]
theorem b_tally_seg_loop0_loop0_spec (bf) (base : Std.Usize)
    (hz : base.val ≤ bf.length) (hb : base.val + slot.A_B_FSZ.val ≤ 4294967295) :
    slot.a_b_tally_seg_loop0_loop0 bf base 0#usize ⦃ fun r => base.val + slot.A_B_FSZ.val ≤ r.length ∧
      bf.length ≤ r.length ∧ engB_Blk r.val base.val 0 ⦄ := U5! slot.a_b_tally_seg_loop0_loop0 slot.A_B_FSZ.val slot.a_b_tally_seg_loop0_loop0.body
@[local step]
theorem b_tally_seg_loop0_loop1_spec (bf) (base : Std.Usize)
    (hz : base.val ≤ bf.length) (hb : base.val + slot.A_B_FSZ.val ≤ 4294967295) :
    slot.a_b_tally_seg_loop0_loop1 bf base 0#usize ⦃ fun r => base.val + slot.A_B_FSZ.val ≤ r.length ∧
      bf.length ≤ r.length ∧ engB_Blk r.val base.val 0 ⦄ := U5! slot.a_b_tally_seg_loop0_loop1 slot.A_B_FSZ.val slot.a_b_tally_seg_loop0_loop1.body
theorem engB_tally_seg_tok (s : Slice Std.U8) (a m : Std.Usize) (bf : alloc.vec.Vec Std.U32)
    (f j l : Std.Usize) (v : Std.U32) (K : Nat)
    (ham : a.val + m.val ≤ s.length) (hj : 0 < j.val) (hjm : j.val ≤ m.val)
    (hf : f.val + slot.A_B_FSZ.val ≤ bf.length) (hblk : engB_Blk bf.val f.val K)
    (hK : K + 2 < 4294967295) :
    (if l ≥ 3#usize then
      if l ≤ j then do
        let i5 ← lift (v &&& 32767#u32)
        let i6 ← lift (UScalar.cast UScalarTy.Usize i5)
        let d ← i6 + 1#usize
        let (i7, _) ← slot.a_b_len_code l
        let i8 ← 257#usize + i7
        let i9 ← i8 % slot.A_B_FSZ
        let i10 ← f + i9
        let (i11, index_mut_back) ← bf.index_mut_usize i10
        let i12 ← i11 + 1#u32
        let i13 ← slot.a_b_dist_slot d
        let i14 ← 288#usize + i13
        let i15 ← i14 % slot.A_B_FSZ
        let i16 ← f + i15
        let (i17, index_mut_back1) ← (index_mut_back i12).index_mut_usize i16
        let i18 ← i17 + 1#u32
        let j2 ← j - l
        ok (index_mut_back1 i18, j2)
      else do
        let i5 ← a + m
        let i6 ← i5 - j
        let i7 ← s.index_usize i6
        let i8 ← lift (UScalar.cast UScalarTy.Usize i7)
        let i9 ← i8 % slot.A_B_FSZ
        let i10 ← f + i9
        let (i11, index_mut_back) ← bf.index_mut_usize i10
        let i12 ← i11 + 1#u32
        let j2 ← j - 1#usize
        ok (index_mut_back i12, j2)
    else do
      let i5 ← a + m
      let i6 ← i5 - j
      let i7 ← s.index_usize i6
      let i8 ← lift (UScalar.cast UScalarTy.Usize i7)
      let i9 ← i8 % slot.A_B_FSZ
      let i10 ← f + i9
      let (i11, index_mut_back) ← bf.index_mut_usize i10
      let i12 ← i11 + 1#u32
      let j2 ← j - 1#usize
      ok (index_mut_back i12, j2)) ⦃ fun (x : alloc.vec.Vec Std.U32 × Std.Usize) =>
      x.1.length = bf.length ∧ x.2.val < j.val ∧ engB_Blk x.1.val f.val (K + (j.val - x.2.val)) ⦄ := by
  split
  · split
    · step*
      all_goals (try subst i11_post2)
      all_goals (try subst i17_post2)
      all_goals try
        (have hidx : f.val ≤ i10.val ∧ i10.val < f.val + slot.A_B_FSZ.val ∧ i10.val < bf.val.length := by
          scalar_tac
         have h11 := engB_Blk_get hblk hidx.1 hidx.2.1 hidx.2.2 i11_post1)
      all_goals try (have hb2 := engB_Blk_set hblk i10.val i12 (K' := K + 1) (by omega) (by omega))
      all_goals try
        (have hidx2 : f.val ≤ i16.val ∧ i16.val < f.val + slot.A_B_FSZ.val ∧
            i16.val < (bf.val.set i10.val i12).length := by
          rw [List.length_set]; scalar_tac
         have h17 := engB_Blk_get hb2 (x := i17) hidx2.1 hidx2.2.1 hidx2.2.2
          (by simp only [i17_post1, alloc.vec.Vec.set_val_eq]))
      all_goals try
        (have hb3 := engB_Blk_set hb2 i16.val i18 (K' := K + (j.val - j2.val))
          (by scalar_tac) (by scalar_tac))
      all_goals first
        | (refine ⟨by simp, by scalar_tac, ?_⟩
           simp only [alloc.vec.Vec.set_val_eq]; exact hb3)
        | scalar_tac
    · step*
      all_goals (try subst i11_post2)
      all_goals try
        (have hidx : f.val ≤ i10.val ∧ i10.val < f.val + slot.A_B_FSZ.val ∧ i10.val < bf.val.length := by
          scalar_tac
         have h11 := engB_Blk_get hblk hidx.1 hidx.2.1 hidx.2.2 i11_post1)
      all_goals try
        (have hb2 := engB_Blk_set hblk i10.val i12 (K' := K + (j.val - j2.val))
          (by scalar_tac) (by omega))
      all_goals first
        | (refine ⟨by simp, by scalar_tac, ?_⟩
           simp only [alloc.vec.Vec.set_val_eq]; exact hb2)
        | scalar_tac
  · step*
    all_goals (try subst i11_post2)
    all_goals try
      (have hidx : f.val ≤ i10.val ∧ i10.val < f.val + slot.A_B_FSZ.val ∧ i10.val < bf.val.length := by
        scalar_tac
       have h11 := engB_Blk_get hblk hidx.1 hidx.2.1 hidx.2.2 i11_post1)
    all_goals try
      (have hb2 := engB_Blk_set hblk i10.val i12 (K' := K + (j.val - j2.val))
        (by scalar_tac) (by omega))
    all_goals first
      | (refine ⟨by simp, by scalar_tac, ?_⟩
         simp only [alloc.vec.Vec.set_val_eq]; exact hb2)
      | scalar_tac
def engB_TSInv (m : Nat) (bf bs : alloc.vec.Vec Std.U32) (nb inb j : Nat) : Prop :=
  j ≤ m ∧ nb * slot.A_B_FSZ.val ≤ bf.length ∧ nb ≤ bs.length ∧ (nb = 0 → inb = slot.A_BLOCK_TOKENS.val) ∧
    inb ≤ slot.A_BLOCK_TOKENS.val ∧ (0 < nb → (nb - 1) * slot.A_BLOCK_TOKENS.val + inb ≤ m - j)
def engB_TSL (m L : Nat) (bf bs : alloc.vec.Vec Std.U32) (nb inb j : Nat) : Prop :=
  (L ≤ bf.length ∧ engB_TSInv m bf bs nb inb j) ∧
    (0 < nb → engB_Blk bf.val ((nb - 1) * slot.A_B_FSZ.val) (m - j))
theorem engB_TSL.mk {m L : Nat} {bf bs : alloc.vec.Vec Std.U32} {nb inb j : Nat}
    (h1 : L ≤ bf.length ∧ j ≤ m ∧ nb * slot.A_B_FSZ.val ≤ bf.length ∧ nb ≤ bs.length ∧
      (nb = 0 → inb = slot.A_BLOCK_TOKENS.val) ∧ inb ≤ slot.A_BLOCK_TOKENS.val ∧
      (0 < nb → (nb - 1) * slot.A_BLOCK_TOKENS.val + inb ≤ m - j))
    (h2 : 0 < nb → engB_Blk bf.val ((nb - 1) * slot.A_B_FSZ.val) (m - j)) :
    engB_TSL m L bf bs nb inb j :=
  ⟨⟨h1.1, h1.2⟩, h2⟩
@[local step]
theorem b_tally_seg_loop0_spec (s : Slice Std.U8) (a m : Std.Usize) (cc : alloc.vec.Vec Std.U64) (whole) (bf bs : alloc.vec.Vec Std.U32) (nb inb j : Std.Usize)
    (ham : a.val + m.val ≤ s.length) (hm : m.val < cc.length) (hm26 : m.val < 67108864)
    (hinv : engB_TSInv m.val bf bs nb.val inb.val j.val)
    (hblk : 0 < nb.val → engB_Blk bf.val ((nb.val - 1) * slot.A_B_FSZ.val) (m.val - j.val)) :
    slot.a_b_tally_seg_loop0 s a m cc whole bf bs nb inb j ⦃ fun r =>
      r.2.2.val * slot.A_BLOCK_TOKENS.val ≤ m.val + slot.A_BLOCK_TOKENS.val ∧ bf.length ≤ r.1.length ∧
      r.2.2.val * slot.A_B_FSZ.val ≤ r.1.length ∧
      (0 < r.2.2.val → engB_Blk r.1.val ((r.2.2.val - 1) * slot.A_B_FSZ.val) m.val) ⦄ := by
  rw [slot.a_b_tally_seg_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, j') => j'.val)
    (inv := fun (bf', bs', nb', inb', j') => engB_TSL m.val bf.length bf' bs' nb'.val inb'.val j'.val)
  · rintro ⟨bf', bs', nb', inb', j'⟩ ⟨⟨hbf', hj', hI1, hI2, hI3, hI4, hI5⟩, hI6⟩
    simp only [slot.a_b_tally_seg_loop0.body]
    split
    · split
      · split
        · -- a new block (whole = 1)
          step*
          apply WP.spec_bind (Pₘ := fun (bs1 : alloc.vec.Vec Std.U32) => nb'.val < bs1.length)
          · split
            · step*
              all_goals first
                | scalar_tac
                | (simp only [alloc.vec.Vec.set_val_eq, List.length_set]; scalar_tac)
            · step*
              all_goals first
                | scalar_tac
                | (have : bs1.length = bs'.length + 1 := by simp [bs1_post]
                   scalar_tac)
          · intro bs1 hbs1
            step*
            apply WP.spec_bind (engB_tally_seg_tok s a m bf1 f j' l v 0 ham (by scalar_tac) hj'
              (by scalar_tac) (by rw [show f.val = base.val by scalar_tac]; exact bf1_post3) (by norm_num))
            rintro ⟨bf2, j1⟩ ⟨hb1, hb2, hb3⟩
            step*
            repeat' (split <;> step*)
            all_goals
              refine ⟨?_, by scalar_tac⟩
              apply engB_TSL.mk
              · scalar_tac
              · exact fun _ => engB_Blk_of hb3 (by scalar_tac)
        · split
          · -- the first block (nb = 0)
            step*
            apply WP.spec_bind (Pₘ := fun (bs1 : alloc.vec.Vec Std.U32) => nb'.val < bs1.length)
            · split
              · step*
                all_goals first
                  | scalar_tac
                  | (simp only [alloc.vec.Vec.set_val_eq, List.length_set]; scalar_tac)
              · step*
                all_goals first
                  | scalar_tac
                  | (have : bs1.length = bs'.length + 1 := by simp [bs1_post]
                     scalar_tac)
            · intro bs1 hbs1
              step*
              apply WP.spec_bind (engB_tally_seg_tok s a m bf1 f j' l v 0 ham (by scalar_tac) hj'
                (by scalar_tac) (by rw [show f.val = base.val by scalar_tac]; exact bf1_post3) (by norm_num))
              rintro ⟨bf2, j1⟩ ⟨hb1, hb2, hb3⟩
              step*
              repeat' (split <;> step*)
              all_goals
                refine ⟨?_, by scalar_tac⟩
                apply engB_TSL.mk
                · scalar_tac
                · exact fun _ => engB_Blk_of hb3 (by scalar_tac)
          · -- the open block, full (inb = BT, whole = 0)
            step*
            apply WP.spec_bind (engB_tally_seg_tok s a m bf' f j' l v (m.val - j'.val) ham
              (by scalar_tac) hj' (by scalar_tac)
              (engB_Blk_of (hI6 (by scalar_tac)) (by scalar_tac)) (by scalar_tac))
            rintro ⟨bf2, j1⟩ ⟨hb1, hb2, hb3⟩
            step*
            repeat' (split <;> step*)
            all_goals
              refine ⟨?_, by scalar_tac⟩
              apply engB_TSL.mk
              · scalar_tac
              · exact fun _ => engB_Blk_of hb3 (by scalar_tac)
      · -- the open block (inb < BT)
        step*
        apply WP.spec_bind (engB_tally_seg_tok s a m bf' f j' l v (m.val - j'.val) ham
          (by scalar_tac) hj' (by scalar_tac)
          (engB_Blk_of (hI6 (by scalar_tac)) (by scalar_tac)) (by scalar_tac))
        rintro ⟨bf2, j1⟩ ⟨hb1, hb2, hb3⟩
        step*
        repeat' (split <;> step*)
        all_goals
          refine ⟨?_, by scalar_tac⟩
          apply engB_TSL.mk
          · scalar_tac
          · exact fun _ => engB_Blk_of hb3 (by scalar_tac)
    · simp only [WP.spec_ok]
      exact ⟨by scalar_tac, hbf', by scalar_tac, fun h => engB_Blk_of (hI6 h) (by scalar_tac)⟩
  · exact ⟨⟨le_refl _, hinv⟩, hblk⟩
@[local step]
theorem b_tally_seg_spec (s : Slice Std.U8) (a m : Std.Usize) (cc : alloc.vec.Vec Std.U64) (whole bf bs)
    (ham : a.val + m.val ≤ s.length) (hm : m.val < cc.length) (hm26 : m.val < 67108864) :
    slot.a_b_tally_seg s a m cc whole bf bs ⦃ fun r => r.1.val ≤ 1048576 ∧ bf.length ≤ r.2.1.length ⦄ := by
  rw [slot.a_b_tally_seg]
  step*
  · unfold engB_TSInv; simp
  · have := engB_Blk_get (bf1_post4 (by scalar_tac)) (by scalar_tac) (by scalar_tac) (by scalar_tac)
      i3_post1
    scalar_tac
  · subst i3_post2; scalar_tac
@[local step]
theorem b_log2_fix_spec (x) : slot.a_b_log2_fix x ⦃ fun r => r.val < 131072 ⦄ := U1! slot.a_b_log2_fix
@[local step]
theorem b_sym_cost_spec (f total) : slot.a_b_sym_cost f total ⦃ fun r => r.val < 131072 ⦄ := U1! slot.a_b_sym_cost
set_option hygiene false in
local notation "U6!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun (tl_, k_) => 286 - k_.val)
    (inv := fun _ => True)
  · rintro ⟨tl_, k_⟩ _
    simp only [q1__]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem b_build_table_loop0_spec (freq tl k) :
    slot.a_b_build_table_loop0 freq tl k ⦃ fun _ => True ⦄ := U6! slot.a_b_build_table_loop0 slot.a_b_build_table_loop0.body
set_option hygiene false in
local notation "U7!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun (k_, td_) => 30 - k_.val)
    (inv := fun _ => True)
  · rintro ⟨k_, td_⟩ _
    simp only [q1__]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem b_build_table_loop1_spec (freq k td) :
    slot.a_b_build_table_loop1 freq k td ⦃ fun _ => True ⦄ := U7! slot.a_b_build_table_loop1 slot.a_b_build_table_loop1.body
@[local step]
theorem b_build_table_loop2_spec (freq tb tl k) :
    slot.a_b_build_table_loop2 freq tb tl k ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_build_table_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (tb_, k_) => 256 - k_.val)
    (inv := fun _ => True)
  · rintro ⟨tb_, k_⟩ _
    simp only [slot.a_b_build_table_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem b_build_table_loop3_spec (freq tb tl l) :
    slot.a_b_build_table_loop3 freq tb tl l ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_build_table_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun (tb_, l_) => 258 + 1 - l_.val)
    (inv := fun _ => True)
  · rintro ⟨tb_, l_⟩ _
    simp only [slot.a_b_build_table_loop3.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem b_build_table_loop4_spec (freq tb k td) :
    slot.a_b_build_table_loop4 freq tb k td ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_build_table_loop4]
  apply Std.loop.spec_decr_nat
    (measure := fun (tb_, k_) => 30 - k_.val)
    (inv := fun _ => True)
  · rintro ⟨tb_, k_⟩ _
    simp only [slot.a_b_build_table_loop4.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem b_build_table_spec (freq tb) :
    slot.a_b_build_table freq tb ⦃ fun _ => True ⦄ := U1! slot.a_b_build_table
@[local step]
theorem b_block_table_loop_spec (bf) (b : Std.Usize) (fq z)
    (hb : b.val * slot.A_B_FSZ.val + slot.A_B_FSZ.val ≤ 4294967295) :
    slot.a_b_block_table_loop bf b fq z ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_block_table_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (fq_, z_) => slot.A_B_FSZ.val - z_.val)
    (inv := fun _ => True)
  · rintro ⟨fq_, z_⟩ _
    simp only [slot.a_b_block_table_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem b_block_table_spec (bf) (b : Std.Usize) (tb) (hb : b.val * slot.A_B_FSZ.val + slot.A_B_FSZ.val ≤ 4294967295) :
    slot.a_b_block_table bf b tb ⦃ fun _ => True ⦄ := U1! slot.a_b_block_table
set_option hygiene false in
local notation "U8!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, l') => ml.val + 1 - l'.val)
    (inv := fun _ => True)
  · rintro ⟨best', choice', l'⟩ _
    simp only [q1__]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem b_dp_seg_loop0_loop0_loop0_spec (cc : alloc.vec.Vec Std.U64) (tb) (j : Std.Usize) (best choice v)
    (ml : Std.Usize) (dc l) (hj : j.val < cc.length) (hml : ml.val ≤ 511) :
    slot.a_b_dp_seg_loop0_loop0_loop0 cc tb j best choice v ml dc l ⦃ fun _ => True ⦄ := U8! slot.a_b_dp_seg_loop0_loop0_loop0 slot.a_b_dp_seg_loop0_loop0_loop0.body
@[local step]
theorem b_dp_seg_loop0_loop0_loop1_spec (cc : alloc.vec.Vec Std.U64) (tb) (j : Std.Usize) (best choice v)
    (ml : Std.Usize) (dc l) (hj : j.val < cc.length) (hml : ml.val ≤ 511) :
    slot.a_b_dp_seg_loop0_loop0_loop1 cc tb j best choice v ml dc l ⦃ fun _ => True ⦄ := U8! slot.a_b_dp_seg_loop0_loop0_loop1 slot.a_b_dp_seg_loop0_loop0_loop1.body
@[local step]
theorem b_dp_seg_loop0_loop0_spec (rs : alloc.vec.Vec Std.U32) (cc : alloc.vec.Vec Std.U64) (cuts : Std.Usize) (tb)
    (j e : Std.Usize) (best choice) (q lo : Std.Usize)
    (hj : j.val < cc.length) (he : e.val ≤ rs.length) (hcuts : cuts.val ≤ 65536) (hlo : lo.val ≤ 512) :
    slot.a_b_dp_seg_loop0_loop0 rs cc cuts tb j e best choice q lo ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_dp_seg_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, q', _) => e.val - q'.val)
    (inv := fun (_, _, _, lo') => lo'.val ≤ 512)
  · rintro ⟨best', choice', q', lo'⟩ hlo'
    simp only [slot.a_b_dp_seg_loop0_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hlo
@[local step]
theorem b_dp_seg_loop0_spec (s : Slice Std.U8) (a m : Std.Usize) (rs bf bs) (cc : alloc.vec.Vec Std.U64) (cuts : Std.Usize) (tb) (b bfirst p j : Std.Usize)
    (ham : a.val + m.val ≤ s.length) (hm : m.val < cc.length) (hp : p.val ≤ rs.length) (hj : 1 ≤ j.val)
    (hb : b.val ≤ 1048576) (hcuts : cuts.val ≤ 65536) :
    slot.a_b_dp_seg_loop0 s a m rs bf bs cc cuts tb b bfirst p j ⦃ fun r => r.length = cc.length ⦄ := by
  rw [slot.a_b_dp_seg_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, j') => m.val + 1 - j'.val)
    (inv := fun (cc', _, b', _, p', j') => cc'.length = cc.length ∧ p'.val ≤ rs.length ∧
      1 ≤ j'.val ∧ b'.val ≤ 1048576)
  · rintro ⟨cc', tb', b', bfirst', p', j'⟩ ⟨h1, h2, h3, h4⟩
    simp only [slot.a_b_dp_seg_loop0.body, alloc.vec.Vec.index_mut_slice_index, engB_vec_index_mut]
    split
    · split
      · step*
        apply WP.spec_bind (Pₘ := fun (x : Std.Array Std.U32 1024#usize × Std.Usize × Std.Usize) =>
          x.2.1.val ≤ b'.val)
        · split
          · split
            · step*
              repeat' (split <;> step*)
              all_goals scalar_tac
            · simp
          · simp
        · rintro ⟨tb1, b1, bfirst1⟩ hb1
          step*
          apply WP.spec_bind (Pₘ := fun (q : Std.Usize) => q.val < p'.val)
          · split
            · step*
              all_goals scalar_tac
            · simp; scalar_tac
          · intro q hq
            step*
            all_goals scalar_tac
      · simp; scalar_tac
    · simp; scalar_tac
  · exact ⟨rfl, hp, hj, hb⟩
@[local step]
theorem b_dp_seg_spec (s : Slice Std.U8) (a m : Std.Usize) (rs : alloc.vec.Vec Std.U32) (rn : Std.Usize) (bf bs) (nb : Std.Usize)
    (cc : alloc.vec.Vec Std.U64) (cuts : Std.Usize)
    (ham : a.val + m.val ≤ s.length) (hm : m.val < cc.length) (hrn : rn.val ≤ rs.length)
    (hnb : nb.val ≤ 1048576) (hcuts : cuts.val ≤ 65536) :
    slot.a_b_dp_seg s a m rs rn bf bs nb cc cuts ⦃ fun r => r.length = cc.length ⦄ := by
  rw [slot.a_b_dp_seg]
  simp only [alloc.vec.Vec.index_mut_slice_index, engB_vec_index_mut]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac
@[local step]
theorem b_static_freq_loop_spec (f) (k : Std.Usize) (hk : k.val ≤ f.length) :
    slot.a_b_static_freq_loop f k ⦃ fun r => slot.A_B_FSZ.val ≤ r.length ⦄ := by
  rw [slot.a_b_static_freq_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => slot.A_B_FSZ.val - k'.val)
    (inv := fun (f', k') => k'.val ≤ f'.length)
  · rintro ⟨f', k'⟩ hk'
    simp only [slot.a_b_static_freq_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals try (obtain ⟨x1, x2⟩ := x; simp only at x_post1 x_post2 ⊢; subst x_post2; step*)
    all_goals first
      | scalar_tac
      | (have : f1.length = f'.length + 1 := by simp [f1_post]
         scalar_tac)
      | (simp [alloc.vec.Vec.set_val_eq]; scalar_tac)
  · exact hk
@[local step]
theorem b_static_freq_spec (f) : slot.a_b_static_freq f ⦃ fun r => slot.A_B_FSZ.val ≤ r.length ⦄ := U1! slot.a_b_static_freq
@[local step]
theorem b_extra_bits_loop0_spec (freq) (c : Std.U64) (k : Std.Usize) (hk : 8 ≤ k.val) (hk28 : k.val ≤ 28)
    (hc : c.val ≤ (k.val - 8) * 2 ^ 35) :
    slot.a_b_extra_bits_loop0 freq c k ⦃ fun r => r.val ≤ 20 * 2 ^ 35 ⦄ := by
  rw [slot.a_b_extra_bits_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => 28 - k'.val)
    (inv := fun (c', k') => 8 ≤ k'.val ∧ k'.val ≤ 28 ∧ c'.val ≤ (k'.val - 8) * 2 ^ 35)
  · rintro ⟨c', k'⟩ ⟨h1, h2, h3⟩
    simp only [slot.a_b_extra_bits_loop0.body]
    step*
    all_goals
      try (have := Nat.mul_le_mul (show i3.val ≤ 4294967295 by scalar_tac) (show i6.val ≤ 5 by scalar_tac))
      scalar_tac
  · exact ⟨hk, hk28, hc⟩
@[local step]
theorem b_extra_bits_loop1_spec (freq) (c : Std.U64) (k : Std.Usize) (hk : 4 ≤ k.val) (hk30 : k.val ≤ 30)
    (hc : c.val ≤ 20 * 2 ^ 35 + (k.val - 4) * 2 ^ 36) :
    slot.a_b_extra_bits_loop1 freq c k ⦃ fun r => r.val ≤ 20 * 2 ^ 35 + 26 * 2 ^ 36 ⦄ := by
  rw [slot.a_b_extra_bits_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => 30 - k'.val)
    (inv := fun (c', k') => 4 ≤ k'.val ∧ k'.val ≤ 30 ∧ c'.val ≤ 20 * 2 ^ 35 + (k'.val - 4) * 2 ^ 36)
  · rintro ⟨c', k'⟩ ⟨h1, h2, h3⟩
    simp only [slot.a_b_extra_bits_loop1.body]
    step*
    all_goals
      try (have := Nat.mul_le_mul (show i2.val ≤ 4294967295 by scalar_tac) (show i5.val ≤ 14 by scalar_tac))
      scalar_tac
  · exact ⟨hk, hk30, hc⟩
@[local step]
theorem b_extra_bits_spec (freq) :
    slot.a_b_extra_bits freq ⦃ fun _ => True ⦄ := U1! slot.a_b_extra_bits
@[local step]
theorem b_self_cost_loop0_spec (freq tl k) :
    slot.a_b_self_cost_loop0 freq tl k ⦃ fun _ => True ⦄ := U6! slot.a_b_self_cost_loop0 slot.a_b_self_cost_loop0.body
@[local step]
theorem b_self_cost_loop1_spec (freq k td) :
    slot.a_b_self_cost_loop1 freq k td ⦃ fun _ => True ⦄ := U7! slot.a_b_self_cost_loop1 slot.a_b_self_cost_loop1.body
@[local step]
theorem b_self_cost_loop2_spec (freq) (k : Std.Usize) (lt c : Std.U64) (hlt : lt.val < 131072) (hk : k.val ≤ 286)
    (hc : c.val ≤ k.val * 2 ^ 49) :
    slot.a_b_self_cost_loop2 freq k lt c ⦃ fun r => r.val ≤ 286 * 2 ^ 49 ⦄ := by
  rw [slot.a_b_self_cost_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (k', _) => 286 - k'.val)
    (inv := fun (k', c') => k'.val ≤ 286 ∧ c'.val ≤ k'.val * 2 ^ 49)
  · rintro ⟨k', c'⟩ ⟨h1, h2⟩
    simp only [slot.a_b_self_cost_loop2.body]
    split
    · step*
      apply WP.spec_bind (Pₘ := fun (c1 : Std.U64) => c1.val ≤ c'.val + 2 ^ 49)
      · split
        · split
          · step*
            all_goals
              have := Nat.mul_le_mul (show i1.val ≤ 4294967295 by scalar_tac)
                (show i2.val ≤ 131071 by scalar_tac)
              scalar_tac
          · simp
        · simp
      · intro c1 hc1
        step*
        scalar_tac
    · simp; scalar_tac
  · exact ⟨hk, hc⟩
@[local step]
theorem b_self_cost_loop3_spec (freq) (k : Std.Usize) (ld c : Std.U64) (hld : ld.val < 131072) (hk : k.val ≤ 30)
    (hc : c.val ≤ 286 * 2 ^ 49 + k.val * 2 ^ 49) :
    slot.a_b_self_cost_loop3 freq k ld c ⦃ fun r => r.val ≤ 316 * 2 ^ 49 ⦄ := by
  rw [slot.a_b_self_cost_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun (k', _) => 30 - k'.val)
    (inv := fun (k', c') => k'.val ≤ 30 ∧ c'.val ≤ 286 * 2 ^ 49 + k'.val * 2 ^ 49)
  · rintro ⟨k', c'⟩ ⟨h1, h2⟩
    simp only [slot.a_b_self_cost_loop3.body]
    split
    · step*
      apply WP.spec_bind (Pₘ := fun (c1 : Std.U64) => c1.val ≤ c'.val + 2 ^ 49)
      · split
        · split
          · step*
            all_goals
              have := Nat.mul_le_mul (show i2.val ≤ 4294967295 by scalar_tac)
                (show i3.val ≤ 131071 by scalar_tac)
              scalar_tac
          · simp
        · simp
      · intro c1 hc1
        step*
        scalar_tac
    · simp; scalar_tac
  · exact ⟨hk, hc⟩
@[local step]
theorem b_self_cost_spec (freq) : slot.a_b_self_cost freq ⦃ fun r => r.val ≤ 316 * 2 ^ 45 ⦄ := by
  rw [slot.a_b_self_cost]
  step*
  repeat' (split <;> step*)
  all_goals (rw [r_post1, Nat.shiftRight_eq_div_pow]; scalar_tac)
@[local step]
theorem b_rec_spec (l) (d : Std.Usize) (full) (hd : 1 ≤ d.val) : slot.a_b_rec l d full ⦃ fun _ => True ⦄ := U1! slot.a_b_rec
@[local step]
theorem b_add_record_loop_spec (rv) (nr q wq : Std.Usize) (dropped) (hwq : wq.val ≤ q.val) :
    slot.a_b_add_record_loop rv nr q wq dropped ⦃ fun r => r.2.val ≤ max q.val nr.val ⦄ := by
  rw [slot.a_b_add_record_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, q', _, _) => nr.val - q'.val)
    (inv := fun (_, q', wq', _) => wq'.val ≤ q'.val ∧ q'.val ≤ max q.val nr.val)
  · rintro ⟨rv', q', wq', dr'⟩ ⟨h1, h2⟩
    simp only [slot.a_b_add_record_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hwq, by scalar_tac⟩
@[local step]
theorem b_add_record_spec (rv) (nr nf l : Std.Usize) (d : Std.Usize) (flag) (hd : 1 ≤ d.val) :
    slot.a_b_add_record rv nr nf l d flag ⦃ fun r => r.1.1.val ≤ max nr.val slot.A_B_RB.val ⦄ := U1! slot.a_b_add_record
@[local step]
theorem b_descend_loop0_loop0_spec (a) (i cap c l : Std.Usize) (wc wi) (run : Std.Usize) (hl : l.val ≤ 2 ^ 31) (hcap : cap.val ≤ 258) :
    slot.a_b_descend_loop0_loop0 a i cap c l wc wi run ⦃ fun r => r.1.val ≤ max l.val cap.val + 8 ⦄ := by
  rw [slot.a_b_descend_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (l', _, _, run') => cap.val + 8 - l'.val + min run'.val 1)
    (inv := fun (l', _, _, run') => l'.val ≤ max l.val cap.val + 8 ∧ (run'.val = 1 → l'.val ≤ max l.val cap.val))
  · rintro ⟨l', wc', wi', run'⟩ ⟨h1, h2⟩
    simp only [slot.a_b_descend_loop0_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨by scalar_tac, fun _ => by scalar_tac⟩
theorem engB_rec_blk (a1 : Std.Array Std.U64 32768#usize) (rv : Std.Array Std.U32 32#usize) (wp : Std.U64)
    (l best scap rbest c d nr nf bl bd : Std.Usize) (L D : Nat) (hd : 1 ≤ d.val) (hl : l.val ≤ L)
    (hbl : bl.val ≤ L) (hdD : d.val ≤ D) (hbd : bd.val ≤ D) (hnr : nr.val ≤ slot.A_B_RB.val) :
    (if l > best then do
        let rl2 ← if l < scap then ok l else ok scap
        let (a4, i15, i16, i17) ←
          if rl2 > rbest then do
              let flag ←
                if c ≥ 1#usize then do
                    let i18 ← c - 1#usize
                    let i19 ← i18 % slot.A_B_WR
                    let i20 ← a1.index_usize i19
                    let i21 ← i20 >>> 56#i32
                    if i21 = wp then slot.A_B_FULL else ok 0#u32
                  else ok 0#u32
              let ((nr2, nf2), rv2) ← slot.a_b_add_record rv nr nf rl2 d flag
              ok (rv2, rl2, nr2, nf2)
            else ok (rv, rbest, nr, nf)
        ok (a4, l, i15, i16, i17, l, d)
      else ok (rv, best, rbest, nr, nf, bl, bd)) ⦃
      fun (x : Std.Array Std.U32 32#usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize ×
        Std.Usize) =>
      x.2.2.2.1.val ≤ slot.A_B_RB.val ∧ x.2.2.2.2.2.1.val ≤ L ∧ x.2.2.2.2.2.2.val ≤ D ⦄ := by
  split
  · step*
    repeat' (split <;> step*)
    all_goals try (obtain ⟨⟨x1, x2⟩, x3⟩ := x; simp only at *; step*)
    all_goals scalar_tac
  · simp only [WP.spec_ok]; exact ⟨hnr, hbl, hbd⟩
attribute [local step] engB_arr_index_le engB_arr_update_le in
theorem engB_tree_blk (t : Std.Array Std.U32 65536#usize) (lt ls rs cs cur l ll rl : Std.Usize) (i L : Nat)
    (hT : LeAll t.val i) (hcur : cur.val ≤ i) (hi : i < 67108864) (hcs : cs.val ≤ 65534)
    (hl : l.val ≤ L) (hll : ll.val ≤ L) (hrl : rl.val ≤ L) :
    (if lt = 1#usize then do
        let i16 ← ls % slot.A_B_TS
        let i17 ← lift (UScalar.cast UScalarTy.U32 cur)
        let a5 ← t.update i16 i17
        let ls2 ← cs + 1#usize
        let i18 ← ls2 % slot.A_B_TS
        let i19 ← a5.index_usize i18
        let cur2 ← lift (UScalar.cast UScalarTy.Usize i19)
        ok (a5, cur2, ls2, rs, l, rl)
      else do
        let i16 ← rs % slot.A_B_TS
        let i17 ← lift (UScalar.cast UScalarTy.U32 cur)
        let a5 ← t.update i16 i17
        let i18 ← cs % slot.A_B_TS
        let i19 ← a5.index_usize i18
        let cur2 ← lift (UScalar.cast UScalarTy.Usize i19)
        ok (a5, cur2, ls, cs, ll, l)) ⦃
      fun (x : Std.Array Std.U32 65536#usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize) =>
      LeAll x.1.val i ∧ x.2.1.val ≤ i ∧ x.2.2.2.2.1.val ≤ L ∧ x.2.2.2.2.2.val ≤ L ⦄ := by
  have hc : (UScalar.cast UScalarTy.U32 cur).val = cur.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)
  split
  · step*
    all_goals first
      | exact ⟨by assumption, by scalar_tac, hl, hrl⟩
      | scalar_tac
  · step*
    all_goals first
      | exact ⟨by assumption, by scalar_tac, hll, hl⟩
      | scalar_tac
def engB_DInv (i : Nat) (tree : Std.Array Std.U32 65536#usize) (pn : Std.Array Std.U32 32#usize)
    (step cur ll rl fuel nr bl bd : Nat) : Prop :=
  LeAll tree.val i ∧ LeAll pn.val i ∧ cur ≤ i ∧ ll ≤ 2 ^ 30 ∧ rl ≤ 2 ^ 30 ∧ step + fuel ≤ 2 ^ 20 ∧
    nr ≤ slot.A_B_RB.val ∧ bl ≤ 2 ^ 30 ∧ bd ≤ i
theorem engB_DInv.mk {i : Nat} {tree : Std.Array Std.U32 65536#usize} {pn : Std.Array Std.U32 32#usize}
    {step cur ll rl fuel nr bl bd : Nat} (h1 : LeAll tree.val i) (h2 : LeAll pn.val i)
    (h3 : cur ≤ i ∧ ll ≤ 2 ^ 30 ∧ rl ≤ 2 ^ 30 ∧ step + fuel ≤ 2 ^ 20 ∧ nr ≤ slot.A_B_RB.val ∧
      bl ≤ 2 ^ 30 ∧ bd ≤ i) :
    engB_DInv i tree pn step cur ll rl fuel nr bl bd :=
  ⟨h1, h2, h3⟩
abbrev engB_DState := Std.Array Std.U32 65536#usize × Std.Array Std.U32 32#usize × Std.Array Std.U32 32#usize ×
  Std.Array Std.U32 32#usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize ×
  Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize
abbrev engB_DOut := Std.Array Std.U32 65536#usize × Std.Array Std.U32 32#usize × Std.Array Std.U32 32#usize ×
  Std.Array Std.U32 32#usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize × Std.Usize
def engB_DPost (i fuel : Nat) (r : ControlFlow engB_DState engB_DOut) : Prop :=
  match r with
  | .done y => LeAll y.1.val i ∧ LeAll y.2.1.val i ∧ y.2.2.2.2.2.1.val ≤ slot.A_B_RB.val ∧
      y.2.2.2.2.2.2.2.1.val ≤ 2 ^ 30 ∧ y.2.2.2.2.2.2.2.2.val ≤ i
  | .cont x' => engB_DInv i x'.1 x'.2.1 x'.2.2.2.2.1.val x'.2.2.2.2.2.1.val x'.2.2.2.2.2.2.2.2.1.val
      x'.2.2.2.2.2.2.2.2.2.1.val x'.2.2.2.2.2.2.2.2.2.2.1.val x'.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val
      x'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val x'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ∧
      x'.2.2.2.2.2.2.2.2.2.2.1.val < fuel
set_option maxHeartbeats 4000000 in
attribute [local step] engB_arr_index_le_d engB_arr_update_le_d in
theorem engB_desc_tail (a1 : Std.Array Std.U64 32768#usize) (t : Std.Array Std.U32 65536#usize)
    (PN PF rv : Std.Array Std.U32 32#usize) (wp : Std.U64)
    (i cap scap l c d lt ls rs cur ll rl fuel best rbest nr nf bl bd step1 : Std.Usize)
    (hT : LeAll t.val i.val) (hPN : LeAll PN.val i.val) (hi : i.val < 67108864) (hcap : cap.val ≤ 258)
    (hcur : cur.val ≤ i.val) (hll : ll.val ≤ 2 ^ 30) (hrl : rl.val ≤ 2 ^ 30) (hl : l.val ≤ 2 ^ 30)
    (hf : 0 < fuel.val) (hsf : step1.val + fuel.val ≤ 2 ^ 20 + 1) (hnr : nr.val ≤ slot.A_B_RB.val)
    (hbl : bl.val ≤ 2 ^ 30) (hd1 : 1 ≤ d.val) (hd : d.val ≤ i.val) (hbd : bd.val ≤ i.val) (hc : c.val < i.val) :
    (do
      let (rv1, best1, rbest1, nr1, nf1, bl1, bd1) ←
        if l > best then do
            let rl2 ← if l < scap then ok l else ok scap
            let (a4, i15, i16, i17) ←
              if rl2 > rbest then do
                  let flag ←
                    if c ≥ 1#usize then do
                        let i18 ← c - 1#usize
                        let i19 ← i18 % slot.A_B_WR
                        let i20 ← a1.index_usize i19
                        let i21 ← i20 >>> 56#i32
                        if i21 = wp then slot.A_B_FULL else ok 0#u32
                      else ok 0#u32
                  let ((nr2, nf2), rv2) ← slot.a_b_add_record rv nr nf rl2 d flag
                  ok (rv2, rl2, nr2, nf2)
                else ok (rv, rbest, nr, nf)
            ok (a4, l, i15, i16, i17, l, d)
          else ok (rv, best, rbest, nr, nf, bl, bd)
      let i15 ← c % slot.A_B_WR
      let cs ← 2#usize * i15
      if l ≥ cap then do
          let i16 ← cs % slot.A_B_TS
          let i17 ← t.index_usize i16
          let i18 ← ls % slot.A_B_TS
          let a4 ← t.update i18 i17
          let i19 ← cs + 1#usize
          let i20 ← i19 % slot.A_B_TS
          let i21 ← a4.index_usize i20
          let i22 ← rs % slot.A_B_TS
          let a5 ← a4.update i22 i21
          ok
              (cont
                (a5, PN, PF, rv1, step1, cur, ls, rs, ll, rl, 0#usize, best1, rbest1, nr1, nf1, bl1, bd1))
        else do
          let (a4, cur1, ls1, rs1, ll1, rl1) ←
            if lt = 1#usize then do
                let i16 ← ls % slot.A_B_TS
                let i17 ← lift (UScalar.cast UScalarTy.U32 cur)
                let a5 ← t.update i16 i17
                let ls2 ← cs + 1#usize
                let i18 ← ls2 % slot.A_B_TS
                let i19 ← a5.index_usize i18
                let cur2 ← lift (UScalar.cast UScalarTy.Usize i19)
                ok (a5, cur2, ls2, rs, l, rl)
              else do
                let i16 ← rs % slot.A_B_TS
                let i17 ← lift (UScalar.cast UScalarTy.U32 cur)
                let a5 ← t.update i16 i17
                let i18 ← cs % slot.A_B_TS
                let i19 ← a5.index_usize i18
                let cur2 ← lift (UScalar.cast UScalarTy.Usize i19)
                ok (a5, cur2, ls, cs, ll, l)
          let fuel1 ← fuel - 1#usize
          if fuel1 = 0#usize then do
              let i16 ← ls1 % slot.A_B_TS
              let a5 ← a4.update i16 0#u32
              let i17 ← rs1 % slot.A_B_TS
              let a6 ← a5.update i17 0#u32
              ok
                  (cont
                    (a6, PN, PF, rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))
            else
              ok
                (cont
                  (a4, PN, PF, rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1)))
      ⦃ engB_DPost i.val fuel.val ⦄ := by
  apply WP.spec_bind (engB_rec_blk a1 rv wp l best scap rbest c d nr nf bl bd (2 ^ 30) i.val hd1 hl hbl hd hbd hnr)
  rintro ⟨rv1, best1, rbest1, nr1, nf1, bl1, bd1⟩ ⟨hr1, hr2, hr3⟩
  step* +scalarTac -grind
  · exact ⟨engB_DInv.mk (by assumption) hPN (by scalar_tac), by scalar_tac⟩
  · apply WP.spec_bind (engB_tree_blk t lt ls rs cs cur l ll rl i.val (2 ^ 30) hT hcur hi (by scalar_tac) hl hll hrl)
    rintro ⟨a4, cur1, ls1, rs1, ll1, rl1⟩ ⟨ht1, ht2, ht3, ht4⟩
    step* +scalarTac -grind
    all_goals exact ⟨engB_DInv.mk (by assumption) hPN (by scalar_tac), by scalar_tac⟩
set_option maxHeartbeats 4000000 in
attribute [local step] engB_arr_index_mut_spec in
theorem engB_desc_known (a1 : Std.Array Std.U64 32768#usize) (t : Std.Array Std.U32 65536#usize)
    (pn pf' rv : Std.Array Std.U32 32#usize) (wp : Std.U64) (pf : Std.U32)
    (i cap scap c d i2 ls rs cur ll rl fuel best rbest nr nf bl bd step : Std.Usize)
    (hT : LeAll t.val i.val) (hP : LeAll pn.val i.val) (hi : i.val < 67108864) (hcap : cap.val ≤ 258)
    (hcur : cur.val ≤ i.val) (hll : ll.val ≤ 2 ^ 30) (hrl : rl.val ≤ 2 ^ 30) (h4 : 4 ≤ pf.val)
    (hf : 0 < fuel.val) (hsf : step.val + fuel.val ≤ 2 ^ 20) (hnr : nr.val ≤ slot.A_B_RB.val)
    (hbl : bl.val ≤ 2 ^ 30) (hd1 : 1 ≤ d.val) (hd : d.val ≤ i.val) (hbd : bd.val ≤ i.val) (hc : c.val < i.val)
    (hi2 : i2.val < 32) :
    (do
      let i3 ← pf >>> 2#i32
      let i4 ← lift (UScalar.cast UScalarTy.Usize i3)
      let l1 ← i4 - 1#usize
      let i5 ← pf >>> 1#i32
      let i6 ← lift (i5 &&& 1#u32)
      let lt ← lift (UScalar.cast UScalarTy.Usize i6)
      if step < slot.A_B_PS then do
          let (_, index_mut_back) ← pn.index_mut_usize i2
          let i7 ← lift (UScalar.cast UScalarTy.U32 c)
          let i8 ← if l1 < cap then ok 1#u32 else ok 0#u32
          let i9 ← lift (UScalar.cast UScalarTy.U32 lt)
          let i10 ← i9 <<< 1#i32
          let i11 ← lift (i8 ||| i10)
          let i12 ← lift (UScalar.cast UScalarTy.U32 l1)
          let i13 ← i12 <<< 2#i32
          let (_, index_mut_back1) ← pf'.index_mut_usize i2
          let i14 ← lift (i11 ||| i13)
          let step1 ← step + 1#usize
          let (rv1, best1, rbest1, nr1, nf1, bl1, bd1) ←
            if l1 > best then do
                let rl2 ← if l1 < scap then ok l1 else ok scap
                let (a4, u15, u16, u17) ←
                  if rl2 > rbest then do
                      let flag ←
                        if c ≥ 1#usize then do
                            let u18 ← c - 1#usize
                            let u19 ← u18 % slot.A_B_WR
                            let u20 ← a1.index_usize u19
                            let u21 ← u20 >>> 56#i32
                            if u21 = wp then slot.A_B_FULL else ok 0#u32
                          else ok 0#u32
                      let ((nr2, nf2), rv2) ← slot.a_b_add_record rv nr nf rl2 d flag
                      ok (rv2, rl2, nr2, nf2)
                    else ok (rv, rbest, nr, nf)
                ok (a4, l1, u15, u16, u17, l1, d)
              else ok (rv, best, rbest, nr, nf, bl, bd)
          let u15 ← c % slot.A_B_WR
          let cs ← 2#usize * u15
          if l1 ≥ cap then do
              let u16 ← cs % slot.A_B_TS
              let u17 ← t.index_usize u16
              let u18 ← ls % slot.A_B_TS
              let a4 ← t.update u18 u17
              let u19 ← cs + 1#usize
              let u20 ← u19 % slot.A_B_TS
              let u21 ← a4.index_usize u20
              let u22 ← rs % slot.A_B_TS
              let a5 ← a4.update u22 u21
              ok
                  (cont
                    (a5, index_mut_back i7, index_mut_back1 i14, rv1, step1, cur, ls, rs, ll, rl, 0#usize, best1, rbest1, nr1, nf1, bl1, bd1))
            else do
              let (a4, cur1, ls1, rs1, ll1, rl1) ←
                if lt = 1#usize then do
                    let u16 ← ls % slot.A_B_TS
                    let u17 ← lift (UScalar.cast UScalarTy.U32 cur)
                    let a5 ← t.update u16 u17
                    let ls2 ← cs + 1#usize
                    let u18 ← ls2 % slot.A_B_TS
                    let u19 ← a5.index_usize u18
                    let cur2 ← lift (UScalar.cast UScalarTy.Usize u19)
                    ok (a5, cur2, ls2, rs, l1, rl)
                  else do
                    let u16 ← rs % slot.A_B_TS
                    let u17 ← lift (UScalar.cast UScalarTy.U32 cur)
                    let a5 ← t.update u16 u17
                    let u18 ← cs % slot.A_B_TS
                    let u19 ← a5.index_usize u18
                    let cur2 ← lift (UScalar.cast UScalarTy.Usize u19)
                    ok (a5, cur2, ls, cs, ll, l1)
              let fuel1 ← fuel - 1#usize
              if fuel1 = 0#usize then do
                  let u16 ← ls1 % slot.A_B_TS
                  let a5 ← a4.update u16 0#u32
                  let u17 ← rs1 % slot.A_B_TS
                  let a6 ← a5.update u17 0#u32
                  ok
                      (cont
                        (a6, index_mut_back i7, index_mut_back1 i14, rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))
                else
                  ok
                    (cont
                      (a4, index_mut_back i7, index_mut_back1 i14, rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))
        else do
          let step1 ← step + 1#usize
          let (rv1, best1, rbest1, nr1, nf1, bl1, bd1) ←
            if l1 > best then do
                let rl2 ← if l1 < scap then ok l1 else ok scap
                let (a4, u15, u16, u17) ←
                  if rl2 > rbest then do
                      let flag ←
                        if c ≥ 1#usize then do
                            let u18 ← c - 1#usize
                            let u19 ← u18 % slot.A_B_WR
                            let u20 ← a1.index_usize u19
                            let u21 ← u20 >>> 56#i32
                            if u21 = wp then slot.A_B_FULL else ok 0#u32
                          else ok 0#u32
                      let ((nr2, nf2), rv2) ← slot.a_b_add_record rv nr nf rl2 d flag
                      ok (rv2, rl2, nr2, nf2)
                    else ok (rv, rbest, nr, nf)
                ok (a4, l1, u15, u16, u17, l1, d)
              else ok (rv, best, rbest, nr, nf, bl, bd)
          let u15 ← c % slot.A_B_WR
          let cs ← 2#usize * u15
          if l1 ≥ cap then do
              let u16 ← cs % slot.A_B_TS
              let u17 ← t.index_usize u16
              let u18 ← ls % slot.A_B_TS
              let a4 ← t.update u18 u17
              let u19 ← cs + 1#usize
              let u20 ← u19 % slot.A_B_TS
              let u21 ← a4.index_usize u20
              let u22 ← rs % slot.A_B_TS
              let a5 ← a4.update u22 u21
              ok
                  (cont
                    (a5, pn, pf', rv1, step1, cur, ls, rs, ll, rl, 0#usize, best1, rbest1, nr1, nf1, bl1, bd1))
            else do
              let (a4, cur1, ls1, rs1, ll1, rl1) ←
                if lt = 1#usize then do
                    let u16 ← ls % slot.A_B_TS
                    let u17 ← lift (UScalar.cast UScalarTy.U32 cur)
                    let a5 ← t.update u16 u17
                    let ls2 ← cs + 1#usize
                    let u18 ← ls2 % slot.A_B_TS
                    let u19 ← a5.index_usize u18
                    let cur2 ← lift (UScalar.cast UScalarTy.Usize u19)
                    ok (a5, cur2, ls2, rs, l1, rl)
                  else do
                    let u16 ← rs % slot.A_B_TS
                    let u17 ← lift (UScalar.cast UScalarTy.U32 cur)
                    let a5 ← t.update u16 u17
                    let u18 ← cs % slot.A_B_TS
                    let u19 ← a5.index_usize u18
                    let cur2 ← lift (UScalar.cast UScalarTy.Usize u19)
                    ok (a5, cur2, ls, cs, ll, l1)
              let fuel1 ← fuel - 1#usize
              if fuel1 = 0#usize then do
                  let u16 ← ls1 % slot.A_B_TS
                  let a5 ← a4.update u16 0#u32
                  let u17 ← rs1 % slot.A_B_TS
                  let a6 ← a5.update u17 0#u32
                  ok
                      (cont
                        (a6, pn, pf', rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))
                else
                  ok
                    (cont
                      (a4, pn, pf', rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))) ⦃ engB_DPost i.val fuel.val ⦄ := by
  have hpf2 := engB_u32_shr2 pf
  have hc32 : (UScalar.cast UScalarTy.U32 c).val = c.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)
  step* +scalarTac -grind
  · apply WP.spec_bind (Pₘ := fun (_ : Std.U32) => True)
    · split <;> simp
    · intro i8 _
      step* +scalarTac -grind
      exact engB_desc_tail a1 t (index_mut_back i7) (index_mut_back1 i14) rv wp i cap scap l1 c d lt ls rs
        cur ll rl fuel best rbest nr nf bl bd step1 hT
        (by rw [‹index_mut_back = pn.set _›, Std.Array.set_val_eq]
            exact LeAll_set hP _ _ (by scalar_tac))
        hi hcap hcur hll hrl (by scalar_tac) hf (by scalar_tac) hnr hbl hd1 hd hbd hc
  · exact engB_desc_tail a1 t pn pf' rv wp i cap scap l1 c d lt ls rs cur ll rl fuel best
      rbest nr nf bl bd step1 hT hP hi hcap hcur hll hrl (by scalar_tac) hf (by scalar_tac)
      hnr hbl hd1 hd hbd hc
set_option maxHeartbeats 4000000 in
attribute [local step] engB_arr_index_mut_spec_b in
theorem engB_desc_cmp (a1 : Std.Array Std.U64 32768#usize) (t : Std.Array Std.U32 65536#usize)
    (pn pf' rv : Std.Array Std.U32 32#usize) (wp : Std.U64)
    (i cap scap c d hn hl l ls rs cur ll rl fuel best rbest nr nf bl bd step : Std.Usize)
    (hT : LeAll t.val i.val) (hP : LeAll pn.val i.val) (hi : i.val < 67108864) (hcap : cap.val ≤ 258)
    (hcur : cur.val ≤ i.val) (hll : ll.val ≤ 2 ^ 30) (hrl : rl.val ≤ 2 ^ 30) (hlb : l.val ≤ 2 ^ 30)
    (hhl : hl.val ≤ 2 ^ 30)
    (hf : 0 < fuel.val) (hsf : step.val + fuel.val ≤ 2 ^ 20) (hnr : nr.val ≤ slot.A_B_RB.val)
    (hbl : bl.val ≤ 2 ^ 30) (hd1 : 1 ≤ d.val) (hd : d.val ≤ i.val) (hbd : bd.val ≤ i.val) (hc : c.val < i.val) :
    (do
      let l1 ← if c = hn then if hl > l then ok hl else ok l else ok l
      let i3 ← lift (core.num.Usize.wrapping_add c l1)
      let i4 ← i3 % slot.A_B_WR
      let wc ← a1.index_usize i4
      let i5 ← lift (core.num.Usize.wrapping_add i l1)
      let i6 ← i5 % slot.A_B_WR
      let wi ← a1.index_usize i6
      let (l2, wc1, wi1, run) ← slot.a_b_descend_loop0_loop0 a1 i cap c l1 wc wi 1#usize
      let l3 ←
        if run = 1#usize then do
            let i7 ← lift (wc1 ^^^ wi1)
            let i8 ← lift (core.num.U64.leading_zeros i7)
            let i9 ← i8 / 8#u32
            let i10 ← lift (UScalar.cast UScalarTy.Usize i9)
            l2 + i10
          else ok l2
      let l4 ← if l3 > cap then ok cap else ok l3
      let lt ← if wc1 < wi1 then ok 1#usize else ok 0#usize
      if step < slot.A_B_PS then do
          let i7 ← step % slot.A_B_PS
          let (_, index_mut_back) ← pn.index_mut_usize i7
          let i8 ← lift (UScalar.cast UScalarTy.U32 c)
          let i9 ← if l4 < cap then ok 1#u32 else ok 0#u32
          let i10 ← lift (UScalar.cast UScalarTy.U32 lt)
          let i11 ← i10 <<< 1#i32
          let i12 ← lift (i9 ||| i11)
          let i13 ← lift (UScalar.cast UScalarTy.U32 l4)
          let i14 ← i13 <<< 2#i32
          let (_, index_mut_back1) ← pf'.index_mut_usize i7
          let i15 ← lift (i12 ||| i14)
          let step1 ← step + 1#usize
          let (rv1, best1, rbest1, nr1, nf1, bl1, bd1) ←
            if l4 > best then do
                let rl2 ← if l4 < scap then ok l4 else ok scap
                let (a4, u15, u16, u17) ←
                  if rl2 > rbest then do
                      let flag ←
                        if c ≥ 1#usize then do
                            let u18 ← c - 1#usize
                            let u19 ← u18 % slot.A_B_WR
                            let u20 ← a1.index_usize u19
                            let u21 ← u20 >>> 56#i32
                            if u21 = wp then slot.A_B_FULL else ok 0#u32
                          else ok 0#u32
                      let ((nr2, nf2), rv2) ← slot.a_b_add_record rv nr nf rl2 d flag
                      ok (rv2, rl2, nr2, nf2)
                    else ok (rv, rbest, nr, nf)
                ok (a4, l4, u15, u16, u17, l4, d)
              else ok (rv, best, rbest, nr, nf, bl, bd)
          let u15 ← c % slot.A_B_WR
          let cs ← 2#usize * u15
          if l4 ≥ cap then do
              let u16 ← cs % slot.A_B_TS
              let u17 ← t.index_usize u16
              let u18 ← ls % slot.A_B_TS
              let a4 ← t.update u18 u17
              let u19 ← cs + 1#usize
              let u20 ← u19 % slot.A_B_TS
              let u21 ← a4.index_usize u20
              let u22 ← rs % slot.A_B_TS
              let a5 ← a4.update u22 u21
              ok
                  (cont
                    (a5, index_mut_back i8, index_mut_back1 i15, rv1, step1, cur, ls, rs, ll, rl, 0#usize, best1, rbest1, nr1, nf1, bl1, bd1))
            else do
              let (a4, cur1, ls1, rs1, ll1, rl1) ←
                if lt = 1#usize then do
                    let u16 ← ls % slot.A_B_TS
                    let u17 ← lift (UScalar.cast UScalarTy.U32 cur)
                    let a5 ← t.update u16 u17
                    let ls2 ← cs + 1#usize
                    let u18 ← ls2 % slot.A_B_TS
                    let u19 ← a5.index_usize u18
                    let cur2 ← lift (UScalar.cast UScalarTy.Usize u19)
                    ok (a5, cur2, ls2, rs, l4, rl)
                  else do
                    let u16 ← rs % slot.A_B_TS
                    let u17 ← lift (UScalar.cast UScalarTy.U32 cur)
                    let a5 ← t.update u16 u17
                    let u18 ← cs % slot.A_B_TS
                    let u19 ← a5.index_usize u18
                    let cur2 ← lift (UScalar.cast UScalarTy.Usize u19)
                    ok (a5, cur2, ls, cs, ll, l4)
              let fuel1 ← fuel - 1#usize
              if fuel1 = 0#usize then do
                  let u16 ← ls1 % slot.A_B_TS
                  let a5 ← a4.update u16 0#u32
                  let u17 ← rs1 % slot.A_B_TS
                  let a6 ← a5.update u17 0#u32
                  ok
                      (cont
                        (a6, index_mut_back i8, index_mut_back1 i15, rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))
                else
                  ok
                    (cont
                      (a4, index_mut_back i8, index_mut_back1 i15, rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))
        else do
          let step1 ← step + 1#usize
          let (rv1, best1, rbest1, nr1, nf1, bl1, bd1) ←
            if l4 > best then do
                let rl2 ← if l4 < scap then ok l4 else ok scap
                let (a4, u15, u16, u17) ←
                  if rl2 > rbest then do
                      let flag ←
                        if c ≥ 1#usize then do
                            let u18 ← c - 1#usize
                            let u19 ← u18 % slot.A_B_WR
                            let u20 ← a1.index_usize u19
                            let u21 ← u20 >>> 56#i32
                            if u21 = wp then slot.A_B_FULL else ok 0#u32
                          else ok 0#u32
                      let ((nr2, nf2), rv2) ← slot.a_b_add_record rv nr nf rl2 d flag
                      ok (rv2, rl2, nr2, nf2)
                    else ok (rv, rbest, nr, nf)
                ok (a4, l4, u15, u16, u17, l4, d)
              else ok (rv, best, rbest, nr, nf, bl, bd)
          let u15 ← c % slot.A_B_WR
          let cs ← 2#usize * u15
          if l4 ≥ cap then do
              let u16 ← cs % slot.A_B_TS
              let u17 ← t.index_usize u16
              let u18 ← ls % slot.A_B_TS
              let a4 ← t.update u18 u17
              let u19 ← cs + 1#usize
              let u20 ← u19 % slot.A_B_TS
              let u21 ← a4.index_usize u20
              let u22 ← rs % slot.A_B_TS
              let a5 ← a4.update u22 u21
              ok
                  (cont
                    (a5, pn, pf', rv1, step1, cur, ls, rs, ll, rl, 0#usize, best1, rbest1, nr1, nf1, bl1, bd1))
            else do
              let (a4, cur1, ls1, rs1, ll1, rl1) ←
                if lt = 1#usize then do
                    let u16 ← ls % slot.A_B_TS
                    let u17 ← lift (UScalar.cast UScalarTy.U32 cur)
                    let a5 ← t.update u16 u17
                    let ls2 ← cs + 1#usize
                    let u18 ← ls2 % slot.A_B_TS
                    let u19 ← a5.index_usize u18
                    let cur2 ← lift (UScalar.cast UScalarTy.Usize u19)
                    ok (a5, cur2, ls2, rs, l4, rl)
                  else do
                    let u16 ← rs % slot.A_B_TS
                    let u17 ← lift (UScalar.cast UScalarTy.U32 cur)
                    let a5 ← t.update u16 u17
                    let u18 ← cs % slot.A_B_TS
                    let u19 ← a5.index_usize u18
                    let cur2 ← lift (UScalar.cast UScalarTy.Usize u19)
                    ok (a5, cur2, ls, cs, ll, l4)
              let fuel1 ← fuel - 1#usize
              if fuel1 = 0#usize then do
                  let u16 ← ls1 % slot.A_B_TS
                  let a5 ← a4.update u16 0#u32
                  let u17 ← rs1 % slot.A_B_TS
                  let a6 ← a5.update u17 0#u32
                  ok
                      (cont
                        (a6, pn, pf', rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))
                else
                  ok
                    (cont
                      (a4, pn, pf', rv1, step1, cur1, ls1, rs1, ll1, rl1, fuel1, best1, rbest1, nr1, nf1, bl1, bd1))) ⦃ engB_DPost i.val fuel.val ⦄ := by
  have hc32 : (UScalar.cast UScalarTy.U32 c).val = c.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)
  apply WP.spec_bind (Pₘ := fun (l1 : Std.Usize) => l1.val ≤ 2 ^ 30)
  · split
    · split <;> simp <;> scalar_tac
    · simp; scalar_tac
  · intro l1 hl1
    step* +scalarTac -grind
    apply WP.spec_bind (Pₘ := fun (l3 : Std.Usize) => l3.val ≤ 2 ^ 30 + 300)
    · split
      · step* +scalarTac -grind
        all_goals scalar_tac
      · simp; scalar_tac
    · intro l3 hl3
      apply WP.spec_bind (Pₘ := fun (l4 : Std.Usize) => l4.val ≤ cap.val)
      · split <;> simp <;> scalar_tac
      · intro l4 hl4
        apply WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
        · split <;> simp
        · intro lt _
          step* +scalarTac -grind
          · apply WP.spec_bind (Pₘ := fun (_ : Std.U32) => True)
            · split <;> simp
            · intro i9 _
              step* +scalarTac -grind
              exact engB_desc_tail a1 t (index_mut_back i8) (index_mut_back1 i15) rv wp i cap scap l4 c d lt
                ls rs cur ll rl fuel best rbest nr nf bl bd step1 hT
                (by rw [‹index_mut_back = pn.set _›, Std.Array.set_val_eq]
                    exact LeAll_set hP _ _ (by scalar_tac))
                hi hcap hcur hll hrl (by scalar_tac) hf (by scalar_tac) hnr hbl hd1 hd hbd hc
          · exact engB_desc_tail a1 t pn pf' rv wp i cap scap l4 c d lt ls rs cur ll rl fuel
              best rbest nr nf bl bd step1 hT hP hi hcap hcur hll hrl (by scalar_tac) hf
              (by scalar_tac) hnr hbl hd1 hd hbd hc
set_option maxHeartbeats 8000000 in
attribute [local step] engB_arr_index_le_g engB_arr_update_le_g engB_arr_index_mut_spec_c in
@[local step]
theorem b_descend_loop0_spec (a : Std.Array Std.U32 65536#usize) (a1) (a2 : Std.Array Std.U32 32#usize) (a3)
    (plen hn hl i cap scap : Std.Usize) (wp rv) (step cur ls rs ll rl fuel best rbest nr nf bl bd : Std.Usize)
    (hi : i.val < 67108864) (hcap : cap.val ≤ 258) (hhl : hl.val ≤ 2 ^ 30)
    (hinv : engB_DInv i.val a a2 step.val cur.val ll.val rl.val fuel.val nr.val bl.val bd.val) :
    slot.a_b_descend_loop0 a a1 a2 a3 plen hn hl i cap scap wp rv step cur ls rs ll rl fuel best rbest nr nf bl bd
      ⦃ fun r => LeAll r.1.val i.val ∧ LeAll r.2.1.val i.val ∧ r.2.2.2.2.2.1.val ≤ slot.A_B_RB.val ∧
        r.2.2.2.2.2.2.2.1.val ≤ 2 ^ 30 ∧ r.2.2.2.2.2.2.2.2.val ≤ i.val ⦄ := by
  rw [slot.a_b_descend_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, _, _, fuel', _, _, _, _, _, _) => fuel'.val)
    (inv := fun (t', pn', _, _, step', cur', _, _, ll', rl', fuel', _, _, nr', _, bl', bd') =>
      engB_DInv i.val t' pn' step'.val cur'.val ll'.val rl'.val fuel'.val nr'.val bl'.val bd'.val)
  · rintro ⟨t', pn', pf', rv', step', cur', ls', rs', ll', rl', fuel', best', rbest', nr', nf', bl', bd'⟩
      ⟨hT, hP, hcur, hll, hrl, hsf, hnr, hbl, hbd⟩
    have hpf : LeAll pf'.val 4294967295 := engB_LeAll_u32 _
    show WP.spec (slot.a_b_descend_loop0.body a1 plen hn hl i cap scap wp t' pn' pf' rv' step' cur' ls' rs'
      ll' rl' fuel' best' rbest' nr' nf' bl' bd') _
    unfold slot.a_b_descend_loop0.body
    by_cases hf : fuel' > 0#usize
    · rw [if_pos hf]
      have hf' : 0 < fuel'.val := by scalar_tac
      step* +scalarTac -grind
      all_goals try (refine ⟨engB_DInv.mk ‹LeAll a5.val i.val› hP (by scalar_tac), by scalar_tac⟩)
      · -- `c = i - d`: the wrapping distance is exact since `cur ≤ i`
        rw [d_post, engB_wsub_val i1 cur' (by scalar_tac)]; scalar_tac
      · have hd1 : 1 ≤ d.val := by
          rw [d_post, engB_wsub_val i1 cur' (by scalar_tac)]; scalar_tac
        have hci : c.val < i.val := by scalar_tac
        apply WP.spec_bind (Pₘ := fun (k : Bool) => k = true → 4 ≤ pf.val)
        · split
          · step* +scalarTac -grind
            all_goals first
              | (intro h; simp at h)
              | (intro h; simp only [decide_eq_true_eq] at h; scalar_tac)
          · simp
        · intro known hknown
          apply WP.spec_bind (Pₘ := fun (l : Std.Usize) => l.val ≤ 2 ^ 30)
          · split <;> simp <;> scalar_tac
          · intro l hlb
            split
            · refine WP.spec_mono (engB_desc_known a1 t' pn' pf' rv' wp pf i cap scap c d i2 ls' rs' cur' ll'
                rl' fuel' best' rbest' nr' nf' bl' bd' step' hT hP hi hcap hcur hll hrl (hknown ‹_›) hf' hsf
                hnr hbl hd1 (by scalar_tac) hbd hci (by scalar_tac)) ?_
              intro r hr; cases r <;> exact hr
            · refine WP.spec_mono (engB_desc_cmp a1 t' pn' pf' rv' wp i cap scap c d hn hl l ls' rs' cur' ll'
                rl' fuel' best' rbest' nr' nf' bl' bd' step' hT hP hi hcap hcur hll hrl hlb hhl hf' hsf
                hnr hbl hd1 (by scalar_tac) hbd hci) ?_
              intro r hr; cases r <;> exact hr
    · rw [if_neg hf]
      simp only [WP.spec_ok]
      exact ⟨hT, hP, hnr, hbl, hbd⟩
  · exact hinv
@[local step]
theorem b_descend_spec (mf : slot.BMf) (first i cap scap best0 wp rv) (nr0 : Std.Usize) (nf0) (depth : Std.Usize)
    (hi : i.val < 67108864) (hcap : cap.val ≤ 258) (hfirst : first.val ≤ i.val)
    (htree : LeAll mf.tree.val i.val) (hpn : LeAll mf.pn.val i.val) (hhl : mf.hl.val ≤ 2 ^ 30)
    (hnr : nr0.val ≤ slot.A_B_RB.val) (hdepth : depth.val ≤ 1048576) :
    slot.a_b_descend mf first i cap scap best0 wp rv nr0 nf0 depth ⦃ fun r =>
      r.1.1.val ≤ slot.A_B_RB.val ∧ LeAll r.2.1.tree.val i.val ∧ LeAll r.2.1.pn.val i.val ∧
      r.2.1.hl.val ≤ 2 ^ 30 ∧ r.2.1.head = mf.head ∧ r.2.1.head3 = mf.head3 ⦄ := by
  rw [slot.a_b_descend]
  have hinv : engB_DInv i.val mf.tree mf.pn (0#usize).val first.val (0#usize).val (0#usize).val
      depth.val nr0.val (0#usize).val (0#usize).val := engB_DInv.mk htree hpn (by simp; scalar_tac)
  step*
  repeat' (split <;> step*)
  all_goals simp_all <;> scalar_tac
@[local step]
theorem b_byte_at_spec (s p) :
    slot.a_b_byte_at s p ⦃ fun _ => True ⦄ := U1! slot.a_b_byte_at
@[local step]
theorem b_engine_loop0_spec (segcap : Std.Usize) (cc) (hseg : segcap.val < 67108864) :
    slot.a_b_engine_loop0 segcap cc ⦃ fun r => segcap.val < r.length ⦄ := by
  rw [slot.a_b_engine_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun cc_ => segcap.val + 1 - cc_.length)
    (inv := fun _ => True)
  · rintro cc_ _
    simp only [slot.a_b_engine_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem b_engine_loop1_spec (input x k) :
    slot.a_b_engine_loop1 input x k ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_engine_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (x_, k_) => 8 - k_.val)
    (inv := fun _ => True)
  · rintro ⟨x_, k_⟩ _
    simp only [slot.a_b_engine_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
def engB_MfInv (mf : slot.BMf) (i : Nat) : Prop :=
  LeAll mf.head.val i ∧ LeAll mf.head3.val i ∧ LeAll mf.tree.val i ∧ LeAll mf.pn.val i ∧
    mf.hl.val ≤ 2 ^ 30
theorem engB_MfInv_init (w : Std.Array Std.U64 32768#usize) (pf : Std.Array Std.U32 32#usize) (plen hn : Std.Usize) :
    engB_MfInv
      { head := Std.Array.repeat 65536#usize 0#u32, head3 := Std.Array.repeat 16384#usize 0#u32,
        tree := Std.Array.repeat 65536#usize 0#u32, w := w, pn := Std.Array.repeat 32#usize 0#u32, pf := pf,
        plen := plen, hn := hn, hl := 0#usize } (0#usize).val := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Std.Array.repeat_val] <;>
    first | exact LeAll_replicate _ _ _ (by simp) | simp
@[local step]
theorem b_engine_loop2_loop0_loop0_spec (input : Slice Std.U8) (mf : slot.BMf) (x) (wfill top : Std.Usize)
    (htop : top.val ≤ input.length) (hn26 : input.length < 67108864) :
    slot.a_b_engine_loop2_loop0_loop0 input mf x wfill top ⦃ fun r =>
      r.1.head = mf.head ∧ r.1.head3 = mf.head3 ∧ r.1.tree = mf.tree ∧ r.1.pn = mf.pn ∧ r.1.hl = mf.hl ⦄ := by
  rw [slot.a_b_engine_loop2_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, wfill_) => top.val - wfill_.val)
    (inv := fun (mf_, _, _) => mf_.head = mf.head ∧ mf_.head3 = mf.head3 ∧ mf_.tree = mf.tree ∧
      mf_.pn = mf.pn ∧ mf_.hl = mf.hl)
  · rintro ⟨mf_, x_, wfill_⟩ ⟨h1, h2, h3, h4, h5⟩
    simp only [slot.a_b_engine_loop2_loop0_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals first
      | exact ⟨h1, h2, h3, h4, h5⟩
      | (refine ⟨⟨h1, h2, h3, h4, h5⟩, ?_⟩; scalar_tac)
      | scalar_tac
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
@[local step]
theorem b_engine_loop2_loop0_loop1_spec (rv) (rs : alloc.vec.Vec Std.U32) (rn nr q : Std.Usize)
    (hrn : rn.val + nr.val < 4294967295) (hrs : rn.val ≤ rs.length) :
    slot.a_b_engine_loop2_loop0_loop1 rv rs rn nr q ⦃ fun r => r.2.val ≤ rn.val + nr.val ∧ r.2.val ≤ r.1.length ⦄ := by
  rw [slot.a_b_engine_loop2_loop0_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, q') => nr.val - q'.val)
    (inv := fun (rs', rn', q') => rn'.val + q.val = rn.val + q'.val ∧ q.val ≤ q'.val ∧
      q'.val ≤ max q.val nr.val ∧ rn'.val ≤ rs'.length)
  · rintro ⟨rs', rn', q'⟩ ⟨h1, h2, h3, h4⟩
    simp only [slot.a_b_engine_loop2_loop0_loop1.body]
    step*
    all_goals scalar_tac
  · exact ⟨rfl, le_refl _, by scalar_tac, hrs⟩
theorem engB_h3_blk (w : Std.Array Std.U64 32768#usize) (rv : Std.Array Std.U32 32#usize)
    (wi wp : Std.U64) (i p3 d3 h3dist scap : Std.Usize) (hd : 0 < p3.val → d3.val ≤ i.val) :
    (if p3 > 0#usize then
        if d3 ≥ 1#usize then
          if d3 ≤ h3dist then
            if scap ≥ 3#usize then do
              let c ← i - d3
              let i14 ← c % slot.A_B_WR
              let i15 ← w.index_usize i14
              let x3 ← lift (i15 ^^^ wi)
              let i16 ← x3 >>> 40#i32
              if i16 = 0#u64 then do
                  let i17 ← x3 >>> 32#i32
                  if (i17 != 0#u64) = true then do
                      let flag ←
                        if c ≥ 1#usize then do
                            let i18 ← c - 1#usize
                            let i19 ← i18 % slot.A_B_WR
                            let i20 ← w.index_usize i19
                            let i21 ← i20 >>> 56#i32
                            if i21 = wp then slot.A_B_FULL else ok 0#u32
                          else ok 0#u32
                      let ((nr1, nf1), rv2) ← slot.a_b_add_record rv 0#usize 0#usize 3#usize d3 flag
                      ok (rv2, nr1, nf1, 3#usize)
                    else ok (rv, 0#usize, 0#usize, 2#usize)
                else ok (rv, 0#usize, 0#usize, 2#usize)
            else ok (rv, 0#usize, 0#usize, 2#usize)
          else ok (rv, 0#usize, 0#usize, 2#usize)
        else ok (rv, 0#usize, 0#usize, 2#usize)
      else ok (rv, 0#usize, 0#usize, 2#usize)) ⦃
      fun (x : Std.Array Std.U32 32#usize × Std.Usize × Std.Usize × Std.Usize) =>
        x.2.1.val ≤ slot.A_B_RB.val ⦄ := by
  repeat' (split <;> step*)
  all_goals scalar_tac
def engB_PPost (b i : Nat)
    (r : ControlFlow (slot.BMf × Std.Array Std.U32 32#usize × alloc.vec.Vec Std.U32 × Std.U64 × Std.Usize ×
      Std.Usize × Std.Usize) (slot.BMf × Std.Array Std.U32 32#usize × alloc.vec.Vec Std.U32 × Std.U64 ×
      Std.Usize × Std.Usize)) : Prop :=
  match r with
  | .done y => engB_MfInv y.1 b ∧ y.2.2.2.2.2.val ≤ 33 * b ∧ y.2.2.2.2.2.val ≤ y.2.2.1.length
  | .cont x' => x'.2.2.2.2.2.2.val ≤ b ∧ x'.2.2.2.2.2.1.val ≤ 33 * x'.2.2.2.2.2.2.val ∧
      x'.2.2.2.2.2.1.val ≤ x'.2.2.1.length ∧ engB_MfInv x'.1 x'.2.2.2.2.2.2.val ∧
      b - x'.2.2.2.2.2.2.val < b - i
theorem engB_arr_index_le_f {n : Std.Usize} (a : Std.Array Std.U32 n) (j : Std.Usize) (B : Nat)
    (h : LeAll a.val B) (hj : j.val < a.length) :
    a.index_usize j ⦃ fun x => x = a.val[j.val] ∧ x.val ≤ B ⦄ := engB_arr_index_le a j B h hj
attribute [local step] engB_arr_index_le_f in
theorem engB_pos_tail (depth : Std.Usize) (mf1 : slot.BMf) (a1 : Std.Array Std.U32 16384#usize)
    (rv1 : Std.Array Std.U32 32#usize) (rs : alloc.vec.Vec Std.U32) (x1 : Std.U64) (wfill1 : Std.Usize)
    (wi wp : Std.U64) (i i12 cap scap nr nf best rn b : Std.Usize)
    (hib : i.val < b.val) (hb : b.val < 67108864) (hi12 : i12.val = i.val + 1) (hcap : cap.val ≤ 258)
    (hH : LeAll mf1.head.val i.val) (hH3 : LeAll a1.val (i.val + 1)) (hT : LeAll mf1.tree.val i.val)
    (hP : LeAll mf1.pn.val i.val) (hL : mf1.hl.val ≤ 2 ^ 30) (hnr : nr.val ≤ slot.A_B_RB.val)
    (hdepth : depth.val ≤ 1048576) (hrn : rn.val ≤ 33 * i.val) (hrs : rn.val ≤ rs.length) :
    (do
      let i14 ← wi >>> 32#i32
      let i15 ← lift (UScalar.cast UScalarTy.U32 i14)
      let i16 ← lift (core.num.U32.wrapping_mul i15 2654435761#u32)
      let i17 ← 32#u32 - slot.A_B_HBITS
      let i18 ← i16 >>> i17
      let i19 ← lift (UScalar.cast UScalarTy.Usize i18)
      let h ← i19 % slot.A_B_HSIZE
      let i20 ← mf1.head.index_usize h
      let first ← lift (UScalar.cast UScalarTy.Usize i20)
      let i21 ← lift (UScalar.cast UScalarTy.U32 i12)
      let a2 ← mf1.head.update h i21
      let ((nr1, _, _, _), mf2, rv2) ←
        slot.a_b_descend
            { head := a2, head3 := a1, tree := mf1.tree, w := mf1.w, pn := mf1.pn, pf := mf1.pf,
              plen := mf1.plen, hn := mf1.hn, hl := mf1.hl }
            first i cap scap best wp rv1 nr nf depth
      let (rs1, rn1) ← slot.a_b_engine_loop2_loop0_loop1 rv2 rs rn nr1 0#usize
      let i22 ← lift (UScalar.cast UScalarTy.U32 nr1)
      let (rn2, rs2) ← slot.a_b_put rs1 rn1 i22
      let i23 ← i + 1#usize
      ok (cont (mf2, rv2, rs2, x1, wfill1, rn2, i23))) ⦃ engB_PPost b.val i.val ⦄ := by
  have hi21 : (UScalar.cast UScalarTy.U32 i12).val = i.val + 1 := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)]; scalar_tac
  step*
  rename Std.Usize × Std.Usize × Std.Usize × Std.Usize => xr
  obtain ⟨nr1, x2, x3, x4⟩ := xr
  have hnr1 : nr1.val ≤ slot.A_B_RB.val := by assumption
  try simp only
  step*
  simp only [engB_PPost]
  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ⟨?_, ?_, ?_, ?_, ?_⟩, by scalar_tac⟩
  · rw [‹mf2.head = a2›, a2_post, Std.Array.set_val_eq]
    exact LeAll_set (LeAll_mono hH (by scalar_tac)) _ _ (by scalar_tac)
  · rw [‹mf2.head3 = a1›]; exact LeAll_mono hH3 (by scalar_tac)
  · exact LeAll_mono ‹LeAll mf2.tree.val i.val› (by scalar_tac)
  · exact LeAll_mono ‹LeAll mf2.pn.val i.val› (by scalar_tac)
  · exact ‹mf2.hl.val ≤ 2 ^ 30›
set_option maxHeartbeats 4000000 in
attribute [local step] engB_arr_index_le_e in
@[local step]
theorem b_engine_loop2_loop0_spec (input : Slice Std.U8) (depth h3dist n : Std.Usize) (mf : slot.BMf) (rv)
    (rs : alloc.vec.Vec Std.U32) (x wfill) (rn a b i : Std.Usize)
    (hn : n.val = input.length) (hn26 : n.val < 67108864) (hdepth : depth.val ≤ 1048576)
    (hb : b.val ≤ n.val) (hib : i.val ≤ b.val) (hrn : rn.val ≤ 33 * i.val) (hrs : rn.val ≤ rs.length)
    (hmf : engB_MfInv mf i.val) :
    slot.a_b_engine_loop2_loop0 input depth h3dist n mf rv rs x wfill rn a b i ⦃ fun r =>
      engB_MfInv r.1 b.val ∧ r.2.2.2.2.2.val ≤ 33 * b.val ∧ r.2.2.2.2.2.val ≤ r.2.2.1.length ⦄ := by
  rw [slot.a_b_engine_loop2_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, i') => b.val - i'.val)
    (inv := fun (mf', _, rs', _, _, rn', i') => i'.val ≤ b.val ∧ rn'.val ≤ 33 * i'.val ∧
      rn'.val ≤ rs'.length ∧ engB_MfInv mf' i'.val)
  · rintro ⟨mf', rv', rs', x', wfill', rn', i'⟩ ⟨hib', hrn', hrs', hH, hH3, hT, hP, hL⟩
    simp only [slot.a_b_engine_loop2_loop0.body]
    by_cases hlt : i' < b
    · rw [if_pos hlt]
      have hlt' : i'.val < b.val := hlt
      step*
      apply WP.spec_bind (Pₘ := fun (top : Std.Usize) => top.val ≤ n.val)
      · split <;> simp <;> scalar_tac
      intro top htop
      step*
      · -- n - i ≥ 4
        simp only [← mf1_post1, ← mf1_post2, ← mf1_post3, ← mf1_post4, ← mf1_post5] at hH hH3 hT hP hL
        apply WP.spec_bind (Pₘ := fun (cap : Std.Usize) => cap.val ≤ 258)
        · split <;> simp <;> scalar_tac
        intro cap hcap
        step*
        apply WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
        · split <;> simp
        intro scap _
        step*
        apply WP.spec_bind (Pₘ := fun (_ : Std.U64) => True)
        · split
          · step*
          · simp
        intro wp _
        step*
        have hp3 : p3.val = i11.val := by
          rw [p3_post]; exact UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)
        have hd3 : d3.val = i'.val + 1 - p3.val := by
          rw [d3_post, engB_wsub_val i12 p3 (by omega)]; omega
        have hi13 : i13.val = i'.val + 1 := by
          rw [i13_post, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)]; omega
        have hH3' : LeAll a1.val (i'.val + 1) := by
          rw [a1_post, Std.Array.set_val_eq]
          exact LeAll_set (LeAll_mono hH3 (by omega)) _ _ (by omega)
        apply WP.spec_bind (engB_h3_blk mf1.w rv' wi wp i' p3 d3 h3dist scap (fun _ => by omega))
        rintro ⟨rv1, nr, nf, best⟩ hnr
        simp only [Std.uncurry_apply_pair]
        refine WP.spec_mono (engB_pos_tail depth mf1 a1 rv1 rs' x1 wfill1 wi wp i' i12 cap scap nr nf best rn' b
          hlt' (by omega) (by omega) hcap hH hH3' hT hP hL hnr hdepth hrn' hrs') ?_
        intro r hr; cases r <;> exact hr
      · -- n - i < 4: one empty record count
        refine ⟨by scalar_tac, by scalar_tac, rn1_post2, ⟨?_, ?_, ?_, ?_, ?_⟩, by scalar_tac⟩
        · rw [mf1_post1]; exact LeAll_mono hH (by scalar_tac)
        · rw [mf1_post2]; exact LeAll_mono hH3 (by scalar_tac)
        · rw [mf1_post3]; exact LeAll_mono hT (by scalar_tac)
        · rw [mf1_post4]; exact LeAll_mono hP (by scalar_tac)
        · rw [mf1_post5]; exact hL
    · rw [if_neg hlt]
      simp only [WP.spec_ok]
      have he : i'.val = b.val := by scalar_tac
      rw [he] at hH hH3 hT hP hrn'
      exact ⟨⟨hH, hH3, hT, hP, hL⟩, hrn', hrs'⟩
  · exact ⟨hib, hrn, hrs, hmf⟩
@[local step]
theorem b_engine_loop2_loop1_spec (input : Slice Std.U8) (bpasses cuts : Std.Usize)
    (bf bs rs : alloc.vec.Vec Std.U32) (cc : alloc.vec.Vec Std.U64) (rn a m p : Std.Usize)
    (ham : a.val + m.val ≤ input.length) (hm : m.val < cc.length) (hm26 : m.val < 67108864)
    (hrn : rn.val ≤ rs.length) (hcuts : cuts.val ≤ 65536) :
    slot.a_b_engine_loop2_loop1 input bpasses cuts bf bs rs cc rn a m p ⦃ fun r =>
      bf.length ≤ r.1.length ∧ r.2.2.length = cc.length ⦄ := by
  rw [slot.a_b_engine_loop2_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, p') => bpasses.val - p'.val)
    (inv := fun (bf', _, cc', _) => bf.length ≤ bf'.length ∧ cc'.length = cc.length)
  · rintro ⟨bf', bs', cc', p'⟩ ⟨h1, h2⟩
    simp only [slot.a_b_engine_loop2_loop1.body]
    step*
    all_goals scalar_tac
  · exact ⟨le_refl _, rfl⟩
@[local step]
theorem b_engine_loop2_loop2_spec (freq) (bf : alloc.vec.Vec Std.U32) (k2) (hbf : slot.A_B_FSZ.val ≤ bf.length) :
    slot.a_b_engine_loop2_loop2 freq bf k2 ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_engine_loop2_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (freq_, k2_) => slot.A_B_FSZ.val - k2_.val)
    (inv := fun _ => True)
  · rintro ⟨freq_, k2_⟩ _
    simp only [slot.a_b_engine_loop2_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem b_engine_loop2_spec (input : Slice Std.U8) (plan) (depth h3dist mode bpasses cuts n : Std.Usize)
    (mf : slot.BMf) (rv freq) (bf bs : alloc.vec.Vec Std.U32) (keep) (rs : alloc.vec.Vec Std.U32)
    (cc : alloc.vec.Vec Std.U64) (x wfill) (rn a : Std.Usize)
    (hn : n.val = input.length) (hn26 : n.val < 67108864) (hcuts : cuts.val ≤ 65536)
    (hdepth : depth.val ≤ 1048576) (ha : a.val ≤ n.val) (hrn : rn.val ≤ 33 * a.val) (hrs : rn.val ≤ rs.length)
    (hmf : engB_MfInv mf a.val) (hcc : n.val < cc.length ∨ slot.A_B_SEG.val < cc.length)
    (hbf : 0 < a.val → slot.A_B_FSZ.val ≤ bf.length) :
    slot.a_b_engine_loop2 input plan depth h3dist mode bpasses cuts n mf rv freq bf bs keep rs cc x wfill rn a
      ⦃ fun r => r.2.2.2.2.2.val ≤ r.2.2.2.1.length ∧ r.2.2.2.2.1.length = cc.length ⦄ := by
  rw [slot.a_b_engine_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, _, _, _, a') => n.val - a'.val)
    (inv := fun (_, mf', _, _, bf', _, rs', cc', _, _, rn', a') => a'.val ≤ n.val ∧
      rn'.val ≤ 33 * a'.val ∧ rn'.val ≤ rs'.length ∧ engB_MfInv mf' a'.val ∧ cc'.length = cc.length ∧
      (0 < a'.val → slot.A_B_FSZ.val ≤ bf'.length))
  · rintro ⟨plan', mf', rv', freq', bf', bs', rs', cc', x', wfill', rn', a'⟩ ⟨ha', hrn', hrs', hmf', hcc', hbf'⟩
    simp only [slot.a_b_engine_loop2.body]
    split
    · step*
      apply WP.spec_bind (Pₘ := fun (m : Std.Usize) =>
        0 < m.val ∧ m.val ≤ n.val - a'.val ∧ m.val ≤ slot.A_B_SEG.val)
      · split <;> simp <;> scalar_tac
      rintro m ⟨hm0, hm1, hm2⟩
      have hmc : m.val < cc'.length := by scalar_tac
      step*
      apply WP.spec_bind (Pₘ := fun (rn1 : Std.Usize) => rn1.val ≤ rn'.val)
      · split <;> simp <;> scalar_tac
      intro rn1 hrn1
      step*
      apply WP.spec_bind (Pₘ := fun (bf1 : alloc.vec.Vec Std.U32) => slot.A_B_FSZ.val ≤ bf1.length)
      · split
        · step*
        · simp only [WP.spec_ok]; scalar_tac
      intro bf1 hbf1
      step*
      apply WP.spec_bind (Pₘ := fun (bs1 : alloc.vec.Vec Std.U32) => 0 < bs1.length)
      · split
        · step*
        · simp only [WP.spec_ok]; scalar_tac
      intro bs1 hbs1
      step*
      · -- mode 1: block passes on this segment
        exact ⟨by scalar_tac, mf1_post2, mf1_post3, mf1_post1, by scalar_tac, fun _ => by scalar_tac,
          by scalar_tac⟩
      · -- modes 0 and 2: refine the segment when its parse costs more than its own entropy
        apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × alloc.vec.Vec Std.U32 ×
            alloc.vec.Vec Std.U64) => slot.A_B_FSZ.val ≤ x.1.length ∧ x.2.2.length = cc.length)
        · split
          · step*
            all_goals scalar_tac
          · split
            · step*
              all_goals scalar_tac
            · simp only [WP.spec_ok]; scalar_tac
        rintro ⟨bf3, bs4, cc2⟩ ⟨hbf3, hcc2⟩
        step*
        exact ⟨by scalar_tac, mf1_post2, mf1_post3, mf1_post1, by scalar_tac, fun _ => hbf3,
          by scalar_tac⟩
    · simp only [WP.spec_ok]
      exact ⟨hrs', hcc'⟩
  · exact ⟨ha, hrn, hrs, hmf, rfl, hbf⟩
@[local step]
theorem b_engine_loop3_spec (input : Slice Std.U8) (bpasses cuts n : Std.Usize)
    (bf bs rs : alloc.vec.Vec Std.U32) (cc : alloc.vec.Vec Std.U64) (rn nb p : Std.Usize)
    (hn : n.val = input.length) (hn26 : n.val < 67108864) (hcc : n.val < cc.length)
    (hrn : rn.val ≤ rs.length) (hnb : nb.val ≤ 1048576) (hcuts : cuts.val ≤ 65536) :
    slot.a_b_engine_loop3 input bpasses cuts n bf bs rs cc rn nb p ⦃ fun r => r.length = cc.length ⦄ := by
  rw [slot.a_b_engine_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, p') => bpasses.val - p'.val)
    (inv := fun (_, _, cc', nb', _) => cc'.length = cc.length ∧ nb'.val ≤ 1048576)
  · rintro ⟨bf', bs', cc', nb', p'⟩ ⟨h1, h2⟩
    simp only [slot.a_b_engine_loop3.body]
    step*
    repeat' (split <;> step*)
    all_goals try (obtain ⟨x1, x2, x3⟩ := x; simp only at x_post1 x_post2 ⊢; step*)
    all_goals scalar_tac
  · exact ⟨rfl, hnb⟩
@[local step]
theorem b_engine_spec (input : Slice Std.U8) (plan) (depth h3dist mode bpasses cuts : Std.Usize)
    (hn : input.length < 67108864) (h1 : depth.val ≤ 65536) (h2 : h3dist.val ≤ 65536)
    (h3 : mode.val ≤ 65536) (h4 : bpasses.val ≤ 65536) (h5 : cuts.val ≤ 65536) :
    slot.a_b_engine input plan depth h3dist mode bpasses cuts ⦃ fun _ => True ⦄ := by
  rw [slot.a_b_engine]
  step*
  apply WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
  · split
    · step*
    · simp only [WP.spec_ok]
  intro keep _
  apply WP.spec_bind (Pₘ := fun (segcap : Std.Usize) =>
    (segcap.val = input.length ∨ segcap.val = slot.A_B_SEG.val) ∧ (keep = 1#usize → segcap.val = input.length))
  · split
    · simp only [WP.spec_ok]; exact ⟨Or.inl (by simp), fun _ => by simp⟩
    · split
      · simp only [WP.spec_ok]; exact ⟨Or.inl (by simp), fun _ => by simp⟩
      · simp only [WP.spec_ok]; exact ⟨Or.inr (by simp), fun h => absurd h ‹_›⟩
  rintro segcap ⟨hs1, hs2⟩
  step*
  all_goals first
    | exact engB_MfInv_init _ _ _ _
    | scalar_tac
@[local step]
theorem C_GROUP_spec : slot.A_C_GROUP ⦃ fun x => x.val = 2147483648 ⦄ := by
  unfold slot.A_C_GROUP; step*
@[local step]
theorem C_LONG_ONLY_spec : slot.A_C_LONG_ONLY ⦃ fun x => x.val = 536870912 ⦄ := by
  unfold slot.A_C_LONG_ONLY; step*
theorem C_BLOCK_bounds : 8192 ≤ slot.A_C_BLOCK.val ∧ slot.A_C_BLOCK.val ≤ 1048576 := by simp [slot.A_C_BLOCK]
theorem C_WS_val : slot.A_C_WS.val = 32768 := by simp [slot.A_C_WS]
theorem C_KS_val : slot.A_C_KS.val = 65536 := by simp [slot.A_C_KS]
theorem C_HS_bounds : 2 ≤ slot.A_C_HS.val ∧ slot.A_C_HS.val ≤ 65536 := by simp [slot.A_C_HS]
theorem C_MS_val : slot.A_C_MS.val = 544 := by simp [slot.A_C_MS]
theorem C_PMASK_lt : slot.A_C_PMASK.val < 2 ^ 27 := by simp [slot.A_C_PMASK]
theorem C_KEEP_le : slot.A_C_KEEP.val ≤ 32 := by simp [slot.A_C_KEEP]
theorem C_SCALE_le : slot.A_C_SCALE.val ≤ 256 := by simp [slot.A_C_SCALE]
theorem C_UNUSED_LIT_le : slot.A_C_UNUSED_LIT.val ≤ 65536 := by simp [slot.A_C_UNUSED_LIT]
theorem C_UNUSED_LEN_le : slot.A_C_UNUSED_LEN.val ≤ 65536 := by simp [slot.A_C_UNUSED_LEN]
theorem C_UNUSED_DIST_le : slot.A_C_UNUSED_DIST.val ≤ 65536 := by simp [slot.A_C_UNUSED_DIST]
theorem C_UNUSED_LEN_W_le : slot.A_C_UNUSED_LEN_W.val ≤ 65536 := by simp [slot.A_C_UNUSED_LEN_W]
theorem C_UNUSED_DIST_W_le : slot.A_C_UNUSED_DIST_W.val ≤ 65536 := by simp [slot.A_C_UNUSED_DIST_W]
theorem C_TAX_W_le : slot.A_C_TAX_W.val ≤ 65536 := by simp [slot.A_C_TAX_W]
theorem C_TAX_C4_le : slot.A_C_TAX_C4.val ≤ 65536 := by simp [slot.A_C_TAX_C4]
theorem C_TAX_BT_le : slot.A_C_TAX_BT.val ≤ 65536 := by simp [slot.A_C_TAX_BT]
theorem C_TOKPEN_le : slot.A_C_TOKPEN.val ≤ 65536 := by simp [slot.A_C_TOKPEN]
theorem C_TOKPEN_W_le : slot.A_C_TOKPEN_W.val ≤ 65536 := by simp [slot.A_C_TOKPEN_W]
theorem C_TOKPEN_C4_le : slot.A_C_TOKPEN_C4.val ≤ 65536 := by simp [slot.A_C_TOKPEN_C4]
theorem C_TOKPEN_BT_le : slot.A_C_TOKPEN_BT.val ≤ 65536 := by simp [slot.A_C_TOKPEN_BT]
theorem C_CHAIN4_RATIO_le : slot.A_C_CHAIN4_RATIO.val ≤ 65535 := by simp [slot.A_C_CHAIN4_RATIO]
theorem C_STOP_DIV_pos : 0 < slot.A_C_STOP_DIV.val := by simp [slot.A_C_STOP_DIV]
theorem C_UP_MIN_ge : 1 ≤ slot.A_C_UP_MIN.val := by simp [slot.A_C_UP_MIN]
theorem C_REP_STEP_bounds : 1 ≤ slot.A_C_REP_STEP.val ∧ slot.A_C_REP_STEP.val ≤ 1048576 := by simp [slot.A_C_REP_STEP]
theorem C_REP6_MIN_le : slot.A_C_REP6_MIN.val ≤ 1048576 := by simp [slot.A_C_REP6_MIN]
theorem engC_LEXTRA_le (i : Nat) (h : i < 29) : (slot.A_C_LEXTRA.val[i]!).val ≤ 5 := by
  unfold slot.A_C_LEXTRA; simp only [Array.make]; revert i; decide
theorem engC_DEXTRA_le (i : Nat) (h : i < 30) : (slot.A_C_DEXTRA.val[i]!).val ≤ 13 := by
  unfold slot.A_C_DEXTRA; simp only [Array.make]; revert i; decide
@[local step]
theorem C_LEXTRA_index_spec (i : Std.Usize) (h : i.val < 29) :
    Array.index_usize slot.A_C_LEXTRA i ⦃ fun x => x.val ≤ 5 ⦄ := by
  have := engC_LEXTRA_le i.val h
  step*
  subst x_post
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)] at this
  exact this
@[local step]
theorem C_DEXTRA_index_spec (i : Std.Usize) (h : i.val < 30) :
    Array.index_usize slot.A_C_DEXTRA i ⦃ fun x => x.val ≤ 13 ⦄ := by
  have := engC_DEXTRA_le i.val h
  step*
  subst x_post
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by scalar_tac)] at this
  exact this
@[local step]
theorem engC_wadd_usize_spec (x y : Std.Usize) :
    lift (core.num.Usize.wrapping_add x y) ⦃ fun z => z = core.num.Usize.wrapping_add x y ∧
      (x.val + y.val ≤ Usize.max → z.val = x.val + y.val) ⦄ := by
  simp only [lift, WP.spec_ok, true_and]
  intro h
  rw [core.num.Usize.wrapping_add_val_eq, UScalar.size_UScalarTyUsize]
  apply Nat.mod_eq_of_lt
  scalar_tac
@[local step]
theorem engC_wadd_u32_spec (x y : Std.U32) :
    lift (core.num.U32.wrapping_add x y) ⦃ fun z => z = core.num.U32.wrapping_add x y ∧
      (x.val + y.val ≤ U32.max → z.val = x.val + y.val) ⦄ := by
  simp only [lift, WP.spec_ok, true_and]
  intro h
  rw [core.num.U32.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac
@[local step]
theorem engC_mul_u64_spec (x y : Std.U64)
    (h : (x.val ≤ 4294967295 ∧ y.val ≤ 4294967295) ∨ x.val * y.val ≤ U64.max) :
    (x * y) ⦃ fun z => z.val = x.val * y.val ∧ (x.val ≤ 4294967295 → z.val ≤ 4294967295 * y.val) ⦄ := by
  have h' : x.val * y.val ≤ U64.max := by
    rcases h with ⟨hx, hy⟩ | h
    · have := Nat.mul_le_mul hx hy
      scalar_tac
    · exact h
  step*
  refine ⟨z_post, fun hx => ?_⟩
  rw [z_post]
  exact Nat.mul_le_mul_right _ hx
@[local step]
theorem engC_mul_u32_spec (x y : Std.U32)
    (h : (x.val ≤ 16777215 ∧ y.val ≤ 256) ∨ x.val * y.val ≤ U32.max) :
    (x * y) ⦃ fun z => z.val = x.val * y.val ∧ (y.val ≤ 256 → z.val ≤ 256 * x.val) ⦄ := by
  have h' : x.val * y.val ≤ U32.max := by
    rcases h with ⟨hx, hy⟩ | h
    · have := Nat.mul_le_mul hx hy
      scalar_tac
    · exact h
  step*
  refine ⟨z_post, fun hy => ?_⟩
  rw [z_post, Nat.mul_comm]
  exact Nat.mul_le_mul_right _ hy
@[local step]
theorem engC_div_u64_spec (x y : Std.U64) (h : y.val ≠ 0) :
    (x / y) ⦃ fun z => z.val = x.val / y.val ∧ (x.val ≤ 65536 * y.val → z.val ≤ 65536) ⦄ := by
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec x h
  rw [hz]
  simp only [WP.spec_ok]
  refine ⟨hv, fun hx => ?_⟩
  rw [hv]
  exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hx)
@[local step]
theorem engC_cast_usize_u64_spec (x : Std.Usize) :
    lift (UScalar.cast .U64 x) ⦃ fun y => y = UScalar.cast .U64 x ∧ y.val = x.val ⦄ := by
  simp only [lift, WP.spec_ok, true_and]
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  have := x.hBounds
  have : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ UScalarTy.U64.numBits := by
    apply Nat.pow_le_pow_right (by decide)
    simp only [UScalarTy.numBits]
    cases System.Platform.numBits_eq <;> simp [*]
  omega
@[local step]
theorem engC_cast_u64_usize_spec (x : Std.U64) :
    lift (UScalar.cast .Usize x) ⦃ fun y => y = UScalar.cast .Usize x ∧ (x.val ≤ 4294967295 → y.val = x.val) ⦄ := by
  simp only [lift, WP.spec_ok, true_and]
  intro h
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  have : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
    apply Nat.pow_le_pow_right (by decide)
    simp only [UScalarTy.numBits]
    exact numBits_ge
  omega
@[local step]
theorem engC_push_spec {α : Type} (v : alloc.vec.Vec α) (x : α) (h : v.length < Usize.max) :
    alloc.vec.Vec.push v x ⦃ fun v1 => v1.val = v.val ++ [x] ∧ v1.length = v.length + 1 ⦄ := by
  step*
  exact ⟨v1_post, by simp [v1_post]⟩
theorem engC_LeAll_repeat {ty : UScalarTy} (n : Std.Usize) (x : UScalar ty) (B : Nat) (h : x.val ≤ B) :
    LeAll (Array.repeat n x).val B := by
  simp only [Array.repeat]
  exact LeAll_replicate _ _ _ h
theorem engC_with_capacity_length {α : Type} (n : Std.Usize) : (alloc.vec.Vec.with_capacity α n).length = 0 := rfl
theorem engC_ite_spec {α : Type} {c : Prop} [Decidable c] {A B : Result α} {P : α → Prop}
    (hA : c → A ⦃ P ⦄) (hB : ¬c → B ⦃ P ⦄) : (if c then A else B) ⦃ P ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h
theorem engC_bind_ite_spec {α β : Type} {c : Prop} [Decidable c] {A B : Result α} {k : α → Result β}
    {P : β → Prop} (hA : c → (A >>= k) ⦃ P ⦄) (hB : ¬c → (B >>= k) ⦃ P ⦄) :
    ((if c then A else B) >>= k) ⦃ P ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact hA h
  · rw [if_neg h]; exact hB h
@[local step]
theorem c_rep_rates_loop_spec (s : Slice Std.U8) (n : Std.Usize) (head) (r4 r6 probes p : Std.Usize)
    (hn : n.val = s.length) (hn26 : n.val < 67108864) (hr4 : r4.val ≤ probes.val) (hr6 : r6.val ≤ probes.val)
    (hpr : probes.val ≤ p.val) (hp : p.val ≤ n.val + slot.A_C_REP_STEP.val) :
    slot.a_c_rep_rates_loop s n head r4 r6 probes p ⦃ fun r => r.1.val ≤ 65536 ∧ r.2.val ≤ 65536 ⦄ := by
  have f1 := C_REP_STEP_bounds
  have f2 := C_REP6_MIN_le
  have f3 := C_WS_val
  rw [slot.a_c_rep_rates_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, p') => n.val + slot.A_C_REP_STEP.val - p'.val)
    (inv := fun (_, r4', r6', pr', p') => r4'.val ≤ pr'.val ∧ r6'.val ≤ pr'.val ∧ pr'.val ≤ p'.val ∧
      p'.val ≤ n.val + slot.A_C_REP_STEP.val)
  · rintro ⟨h', r4', r6', pr', p'⟩ ⟨i1, i2, i3, i4⟩
    simp only [slot.a_c_rep_rates_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hr4, hr6, hpr, hp⟩
@[local step]
theorem c_rep_rates_spec (s : Slice Std.U8) (hn26 : s.length < 67108864) :
    slot.a_c_rep_rates s ⦃ fun r => r.1.val ≤ 65536 ∧ r.2.val ≤ 65536 ⦄ := U1! slot.a_c_rep_rates
@[local step]
theorem c_clear_span_loop_spec (plan e_nd p) :
    slot.a_c_clear_span_loop plan e_nd p ⦃ fun r => r.length = plan.length ⦄ := by
  rw [slot.a_c_clear_span_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, p') => e_nd.val - p'.val)
    (inv := fun (plan', _) => plan'.length = plan.length)
  · rintro ⟨plan', p'⟩ hinv
    simp only [slot.a_c_clear_span_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · rfl
@[local step]
theorem c_clear_span_spec (plan p0 e_nd) :
    slot.a_c_clear_span plan p0 e_nd ⦃ fun r => r.length = plan.length ⦄ := U1! slot.a_c_clear_span
@[local step]
theorem c_dsym_spec (d) : slot.a_c_dsym d ⦃ fun r => r.val < 256 ⦄ := U1! slot.a_c_dsym
@[local step]
theorem c_lsym_spec (len) : slot.a_c_lsym len ⦃ fun r => r.val < 256 ⦄ := U1! slot.a_c_lsym
@[local step]
theorem c_path_block_loop0_spec (lf df) :
    slot.a_c_path_block_loop0 lf df 0#usize ⦃ fun r => LeAll r.1.val 0 ∧ LeAll r.2.val 0 ⦄ := by
  rw [slot.a_c_path_block_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, k) => 288 - k.val)
    (inv := fun (lf', df', k) => k.val ≤ 288 ∧
      (∀ j (hj : j < k.val) (hl : j < lf'.val.length), (lf'.val[j]).val = 0) ∧
      (∀ j (hj : j < k.val) (hl : j < df'.val.length), (df'.val[j]).val = 0))
  · rintro ⟨lf', df', k⟩ ⟨hk, hz1, hz2⟩
    simp only [slot.a_c_path_block_loop0.body]
    step*
    · refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro j hj hl
        subst a_post
        simp only [Array.set_val_eq, List.getElem_set]
        split
        · rfl
        · exact hz1 j (by scalar_tac) (by simpa using hl)
      · intro j hj hl
        subst a1_post
        simp only [Array.set_val_eq, List.getElem_set]
        split
        · rfl
        · exact hz2 j (by scalar_tac) (by simpa using hl)
    · have : k.val = 288 := by scalar_tac
      refine ⟨?_, ?_⟩
      · intro j hl
        have hl' : j < 288 := by simpa using hl
        rw [hz1 j (by omega) hl]
      · intro j hl
        have hl' : j < 288 := by simpa using hl
        rw [hz2 j (by omega) hl]
  · exact ⟨by simp, fun j hj => by simp at hj, fun j hj => by simp at hj⟩
@[local step]
theorem c_path_block_loop1_spec (s : Slice Std.U8) (choice) (lf df) (n p t : Std.Usize)
    (hn : n.val = s.length) (hlf : LeAll lf.val t.val) (hdf : LeAll df.val t.val) :
    slot.a_c_path_block_loop1 s choice lf df n p t ⦃ fun r => p.val ≤ r.2.2.val ∧ (p.val ≤ n.val → r.2.2.val ≤ n.val) ⦄ := by
  have hB := C_BLOCK_bounds
  rw [slot.a_c_path_block_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, t') => slot.A_C_BLOCK.val - t'.val)
    (inv := fun (lf', df', p', t') => LeAll lf'.val t'.val ∧ LeAll df'.val t'.val ∧ p.val ≤ p'.val ∧
      (p.val ≤ n.val → p'.val ≤ n.val))
  · rintro ⟨lf', df', p', t'⟩ ⟨hlf', hdf', hp1, hp2⟩
    simp only [slot.a_c_path_block_loop1.body]
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Array Std.U32 288#usize × Std.Array Std.U32 288#usize × Std.Usize) =>
      LeAll x.1.val (t'.val + 1) ∧ LeAll x.2.1.val (t'.val + 1) ∧ p'.val < x.2.2.val ∧ x.2.2.val ≤ n.val)
    · split
      · step*
        · -- a match: one length and one distance counter go up (wrapping, but they cannot wrap)
          have h6 := LeAll_get hlf' i5.val (by scalar_tac)
          have h12 := LeAll_get hdf' i11.val (by scalar_tac)
          refine ⟨?_, ?_, by scalar_tac, by scalar_tac⟩
          · rw [a_post, Array.set_val_eq]; exact LeAll_set_succ hlf' _ _ (by scalar_tac)
          · rw [a1_post, Array.set_val_eq]; exact LeAll_set_succ hdf' _ _ (by scalar_tac)
        · -- the literal counter cannot overflow
          have := LeAll_get hlf' i4.val (by scalar_tac)
          scalar_tac
        · -- a literal (the match does not fit)
          have := LeAll_get hlf' i4.val (by scalar_tac)
          refine ⟨?_, LeAll_mono hdf' (by omega), by scalar_tac, by scalar_tac⟩
          rw [a_post, Array.set_val_eq]; exact LeAll_set_succ hlf' _ _ (by scalar_tac)
      · -- a literal
        step*
        · have := LeAll_get hlf' i3.val (by scalar_tac)
          scalar_tac
        · have := LeAll_get hlf' i3.val (by scalar_tac)
          refine ⟨?_, LeAll_mono hdf' (by omega), by scalar_tac, by scalar_tac⟩
          rw [a_post, Array.set_val_eq]; exact LeAll_set_succ hlf' _ _ (by scalar_tac)
    · rintro ⟨lf1, df1, p1⟩ ⟨h1, h2, h3, h4⟩
      step*
  · exact ⟨hlf, hdf, le_refl _, fun h => h⟩
@[local step]
theorem c_path_block_spec (s choice p0 lf df) :
    slot.a_c_path_block s choice p0 lf df ⦃ fun r => p0.val ≤ r.1.val ∧ (p0.val ≤ s.length → r.1.val ≤ s.length) ⦄ := by
  rw [slot.a_c_path_block]
  step*
@[local step]
theorem c_fixed_bits_loop0_spec (lf) (bits : Std.U64) (i : Std.Usize) (hi : i.val ≤ 288)
    (hb : bits.val ≤ 3 + i.val * 2 ^ 40) :
    slot.a_c_fixed_bits_loop0 lf bits i ⦃ fun r => r.val ≤ 3 + 288 * 2 ^ 40 ⦄ := by
  rw [slot.a_c_fixed_bits_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i') => 288 - i'.val)
    (inv := fun (bits', i') => i'.val ≤ 288 ∧ bits'.val ≤ 3 + i'.val * 2 ^ 40)
  · rintro ⟨bits', i'⟩ ⟨hi', hb'⟩
    simp only [slot.a_c_fixed_bits_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hi, hb⟩
@[local step]
theorem c_fixed_bits_loop1_spec (df) (bits : Std.U64) (d : Std.Usize) (hd : d.val ≤ 30)
    (hb : bits.val ≤ 3 + 288 * 2 ^ 40 + d.val * 2 ^ 40) :
    slot.a_c_fixed_bits_loop1 df bits d ⦃ fun r => r.val ≤ 3 + 318 * 2 ^ 40 ⦄ := by
  rw [slot.a_c_fixed_bits_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, d') => 30 - d'.val)
    (inv := fun (bits', d') => d'.val ≤ 30 ∧ bits'.val ≤ 3 + 288 * 2 ^ 40 + d'.val * 2 ^ 40)
  · rintro ⟨bits', d'⟩ ⟨hd', hb'⟩
    simp only [slot.a_c_fixed_bits_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hd, hb⟩
@[local step]
theorem c_fixed_bits_spec (lf df) :
    slot.a_c_fixed_bits lf df ⦃ fun _ => True ⦄ := U1! slot.a_c_fixed_bits
@[local step]
theorem c_rle_run_loop0_spec (clf) (r : Std.Usize) (extra : Std.U64) (fuel : Std.Usize)
    (hx : extra.val + 7 * fuel.val ≤ 2 ^ 40) :
    slot.a_c_rle_run_loop0 clf r extra fuel ⦃ fun res => res.2.2.val ≤ extra.val + 7 * fuel.val ⦄ := by
  rw [slot.a_c_rle_run_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, f) => f.val)
    (inv := fun (_, _, e, f) => e.val + 7 * f.val ≤ extra.val + 7 * fuel.val)
  · rintro ⟨clf', r', e', f'⟩ hinv
    simp only [slot.a_c_rle_run_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · simp
@[local step]
theorem c_rle_run_loop1_spec (clf) (r : Std.Usize) (extra : Std.U64) (fuel : Std.Usize)
    (hx : extra.val + 2 * fuel.val ≤ 2 ^ 40) :
    slot.a_c_rle_run_loop1 clf r extra fuel ⦃ fun res => res.2.2.val ≤ extra.val + 2 * fuel.val ⦄ := by
  rw [slot.a_c_rle_run_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, f) => f.val)
    (inv := fun (_, _, e, f) => e.val + 2 * f.val ≤ extra.val + 2 * fuel.val)
  · rintro ⟨clf', r', e', f'⟩ hinv
    simp only [slot.a_c_rle_run_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · simp
@[local step]
theorem c_rle_run_spec (clf v) (r0 : Std.Usize) (hr0 : 1 ≤ r0.val ∧ r0.val ≤ 512) :
    slot.a_c_rle_run clf v r0 ⦃ fun r => r.1.val ≤ 7 * (r0.val + 1) ⦄ := U1! slot.a_c_rle_run
@[local step]
theorem c_radix_pass_loop0_spec (sw) (k : Std.Usize) (shift : Std.U32) (hshift : shift.val < 32) :
    slot.a_c_radix_pass_loop0 sw k shift (Array.repeat 257#usize 0#usize) 0#usize ⦃ fun r => LeAll r.val 288 ⦄ := by
  rw [slot.a_c_radix_pass_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i') => 288 - i'.val)
    (inv := fun (cnt', i') => i'.val ≤ 288 ∧ LeAll cnt'.val i'.val)
  · rintro ⟨cnt', i'⟩ ⟨hi', hc'⟩
    simp only [slot.a_c_radix_pass_loop0.body]
    step*
    all_goals first
      | scalar_tac
      | exact LeAll_mono hc' (by scalar_tac)
      | (refine ⟨by scalar_tac, ?_, by scalar_tac⟩
         rw [a_post, Array.set_val_eq, show i9.val = i'.val + 1 by scalar_tac]
         apply LeAll_set_succ hc'
         have := LeAll_get hc' i5.val (by scalar_tac)
         scalar_tac)
  · exact ⟨by simp, engC_LeAll_repeat _ _ _ (by simp)⟩
@[local step]
theorem c_radix_pass_loop1_spec (cnt) (hcnt : LeAll cnt.val 288) :
    slot.a_c_radix_pass_loop1 cnt 1#usize ⦃ fun r => LeAll r.val 74016 ⦄ := by
  rw [slot.a_c_radix_pass_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, c') => 257 - c'.val)
    (inv := fun (cnt', c') => 1 ≤ c'.val ∧ c'.val ≤ 257 ∧
      (∀ j (hj : j < cnt'.val.length), j < c'.val → (cnt'.val[j]).val ≤ 288 * c'.val) ∧
      (∀ j (hj : j < cnt'.val.length), c'.val ≤ j → (cnt'.val[j]).val ≤ 288))
  · rintro ⟨cnt', c'⟩ ⟨hc1, hc2, hlo, hhi⟩
    simp only [slot.a_c_radix_pass_loop1.body]
    step*
    · have hi : i.val ≤ 288 := by rw [i_post]; exact hhi _ _ (le_refl _)
      have hi2 : i2.val ≤ 288 * c'.val := by rw [i2_post]; exact hlo _ _ (by scalar_tac)
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, by scalar_tac⟩
      · intro j hj hjc
        subst a_post
        simp only [Array.set_val_eq, List.getElem_set]
        split
        · scalar_tac
        · have hj' : j < (↑cnt' : List Std.Usize).length := by simpa using hj
          have := hlo j hj' (by scalar_tac)
          scalar_tac
      · intro j hj hjc
        subst a_post
        simp only [Array.set_val_eq, List.getElem_set]
        split
        · scalar_tac
        · exact hhi j (by simpa using hj) (by scalar_tac)
    · intro j hj
      have hj2 : j < 257 := by simpa using hj
      have := hlo j hj (by scalar_tac)
      scalar_tac
  · refine ⟨by simp, by simp, ?_, ?_⟩
    · intro j hj hj1
      have := hcnt j hj
      simp at hj1 ⊢
      omega
    · intro j hj _
      exact hcnt j hj
@[local step]
theorem c_radix_pass_loop2_spec (sw ss dw ds) (k : Std.Usize) (shift : Std.U32) (cnt) (hshift : shift.val < 32)
    (hcnt : LeAll cnt.val 74016) :
    slot.a_c_radix_pass_loop2 sw ss dw ds k shift cnt 0#usize ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_radix_pass_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, j') => 288 - j'.val)
    (inv := fun (_, _, cnt', j') => j'.val ≤ 288 ∧ LeAll cnt'.val (74016 + j'.val))
  · rintro ⟨dw', ds', cnt', j'⟩ ⟨hj', hc'⟩
    simp only [slot.a_c_radix_pass_loop2.body]
    step*
    all_goals first
      | scalar_tac
      | (have := LeAll_get hc' i3.val (by scalar_tac)
         scalar_tac)
      | (refine ⟨by scalar_tac, ?_, by scalar_tac⟩
         rw [a2_post, Array.set_val_eq, show j1.val = j'.val + 1 by scalar_tac, ← Nat.add_assoc]
         apply LeAll_set_succ hc'
         have := LeAll_get hc' i3.val (by scalar_tac)
         scalar_tac)
  · exact ⟨by simp, by simpa using hcnt⟩
@[local step]
theorem c_radix_pass_spec (sw ss dw ds) (k : Std.Usize) (shift : Std.U32) (hshift : shift.val < 32) :
    slot.a_c_radix_pass sw ss dw ds k shift ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_radix_pass]
  step*
@[local step]
theorem c_huff_lengths_loop0_spec (freq m lens aw asy) (k i : Std.Usize) (hk : k.val ≤ i.val) (hi : i.val ≤ 288) :
    slot.a_c_huff_lengths_loop0 freq m lens aw asy k i ⦃ fun r => r.2.2.2.val ≤ 288 ⦄ := by
  rw [slot.a_c_huff_lengths_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, i') => 288 - i'.val)
    (inv := fun (_, _, _, k', i') => k'.val ≤ i'.val ∧ i'.val ≤ 288)
  · rintro ⟨lens', aw', asy', k', i'⟩ ⟨hk', hi'⟩
    simp only [slot.a_c_huff_lengths_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hk, hi⟩
@[local step]
theorem c_huff_lengths_loop1_loop0_spec (aw) (k : Std.Usize) (iw ipar lpar) (li ii ni : Std.Usize) (w2) (t : Std.Usize)
    (hii : ii.val ≤ 2 ^ 20) :
    slot.a_c_huff_lengths_loop1_loop0 aw k iw ipar lpar li ii ni w2 t ⦃ fun r => r.2.2.2.1.val ≤ ii.val + 2 ⦄ := by
  rw [slot.a_c_huff_lengths_loop1_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, t') => 2 - t'.val)
    (inv := fun (_, _, _, ii', _, t') => ii'.val + t.val ≤ ii.val + t'.val ∧ t.val ≤ t'.val ∧
      (t.val ≤ 2 → t'.val ≤ 2) ∧ (2 < t.val → t'.val = t.val))
  · rintro ⟨ipar', lpar', li', ii', w2', t'⟩ ⟨h1, h2, h3, h4⟩
    simp only [slot.a_c_huff_lengths_loop1_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · simp
@[local step]
theorem c_huff_lengths_loop1_spec (aw) (k : Std.Usize) (iw ipar lpar) (li ii ni : Std.Usize) (hii : ii.val ≤ 2 * ni.val)
    (hni : ni.val ≤ 287) (hk : k.val ≤ 288) :
    slot.a_c_huff_lengths_loop1 aw k iw ipar lpar li ii ni ⦃ fun r => ni.val ≤ r.2.2.val ∧ (ni.val + 1 < k.val → ni.val < r.2.2.val) ⦄ := by
  rw [slot.a_c_huff_lengths_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, ni') => 287 - ni'.val)
    (inv := fun (_, _, _, _, ii', ni') => ni.val ≤ ni'.val ∧ ni'.val ≤ 287 ∧ ii'.val ≤ 2 * ni'.val)
  · rintro ⟨iw', ipar', lpar', li', ii', ni'⟩ ⟨h1, h2, h3⟩
    simp only [slot.a_c_huff_lengths_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨le_refl _, hni, hii⟩
@[local step]
theorem c_huff_lengths_loop2_spec (ipar idep j) :
    slot.a_c_huff_lengths_loop2 ipar idep j ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_huff_lengths_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (idep_, j_) => j_.val)
    (inv := fun _ => True)
  · rintro ⟨idep_, j_⟩ _
    simp only [slot.a_c_huff_lengths_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem c_huff_lengths_loop3_spec (lens asy k lpar idep x) :
    slot.a_c_huff_lengths_loop3 lens asy k lpar idep x ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_huff_lengths_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun (lens_, x_) => k.val - x_.val)
    (inv := fun _ => True)
  · rintro ⟨lens_, x_⟩ _
    simp only [slot.a_c_huff_lengths_loop3.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem c_huff_lengths_spec (freq m lens) : slot.a_c_huff_lengths freq m lens ⦃ fun _ => True ⦄ := U1! slot.a_c_huff_lengths
@[local step]
theorem c_dyn_bits_loop0_spec (lf ll) (body : Std.U64) (hlit i : Std.Usize) (hi : i.val ≤ 286)
    (hb : body.val ≤ i.val * 2 ^ 41) :
    slot.a_c_dyn_bits_loop0 lf ll body hlit i ⦃ fun r => r.1.val ≤ 286 * 2 ^ 41 ∧ r.2.val ≤ max hlit.val 286 ⦄ := by
  rw [slot.a_c_dyn_bits_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, i') => 286 - i'.val)
    (inv := fun (b', h', i') => i'.val ≤ 286 ∧ b'.val ≤ i'.val * 2 ^ 41 ∧ h'.val ≤ max hlit.val 286)
  · rintro ⟨b', h', i'⟩ ⟨h1, h2, h3⟩
    simp only [slot.a_c_dyn_bits_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hi, hb, by scalar_tac⟩
@[local step]
theorem c_dyn_bits_loop1_spec (df dl) (body : Std.U64) (hdist any : Std.Usize) (d : Std.Usize) (hd : d.val ≤ 30)
    (hb : body.val ≤ 286 * 2 ^ 41 + d.val * 2 ^ 41) :
    slot.a_c_dyn_bits_loop1 df dl body hdist any d ⦃ fun r => r.1.val ≤ 316 * 2 ^ 41 ∧ r.2.1.val ≤ max hdist.val 30 ⦄ := by
  rw [slot.a_c_dyn_bits_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, d') => 30 - d'.val)
    (inv := fun (b', h', _, d') => d'.val ≤ 30 ∧ b'.val ≤ 286 * 2 ^ 41 + d'.val * 2 ^ 41 ∧ h'.val ≤ max hdist.val 30)
  · rintro ⟨b', h', a', d'⟩ ⟨h1, h2, h3⟩
    simp only [slot.a_c_dyn_bits_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hd, hb, by scalar_tac⟩
@[local step]
theorem c_dyn_bits_loop2_spec (ll dl hlit total seq i2) :
    slot.a_c_dyn_bits_loop2 ll dl hlit total seq i2 ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_dyn_bits_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (seq_, i2_) => total.val - i2_.val)
    (inv := fun _ => True)
  · rintro ⟨seq_, i2_⟩ _
    simp only [slot.a_c_dyn_bits_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem c_dyn_bits_loop3_loop0_spec (total seq) (j r : Std.Usize) (v) (hj : j.val ≤ 512) (hr : r.val ≤ 512) :
    slot.a_c_dyn_bits_loop3_loop0 total seq j v r ⦃ fun res => r.val ≤ res.val ∧ res.val ≤ max r.val 512 ∧
      (j.val + r.val ≤ 512 → j.val + res.val ≤ 512) ⦄ := by
  rw [slot.a_c_dyn_bits_loop3_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun r' => 512 - r'.val)
    (inv := fun r' => r.val ≤ r'.val ∧ r'.val ≤ max r.val 512 ∧ (j.val + r.val ≤ 512 → j.val + r'.val ≤ 512))
  · rintro r' ⟨h1, h2, h3⟩
    simp only [slot.a_c_dyn_bits_loop3_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨le_refl _, by scalar_tac, fun h => h⟩
@[local step]
theorem c_dyn_bits_loop3_spec (clf) (extra : Std.U64) (total seq) (j : Std.Usize) (hj : j.val ≤ 512)
    (hx : extra.val ≤ j.val * 4096) :
    slot.a_c_dyn_bits_loop3 clf extra total seq j ⦃ fun r => r.2.val ≤ 513 * 4096 ⦄ := by
  rw [slot.a_c_dyn_bits_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, j') => 512 - j'.val)
    (inv := fun (_, e', j') => j'.val ≤ 512 ∧ e'.val ≤ j'.val * 4096)
  · rintro ⟨clf', e', j'⟩ ⟨h1, h2⟩
    simp only [slot.a_c_dyn_bits_loop3.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hj, hx⟩
@[local step]
theorem c_dyn_bits_loop4_spec (cl hclen) :
    slot.a_c_dyn_bits_loop4 cl hclen ⦃ fun r => r.val ≤ hclen.val ⦄ := by
  rw [slot.a_c_dyn_bits_loop4]
  apply Std.loop.spec_decr_nat
    (measure := fun h' => h'.val)
    (inv := fun h' => h'.val ≤ hclen.val)
  · rintro h' h1
    simp only [slot.a_c_dyn_bits_loop4.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact le_refl _
@[local step]
theorem c_dyn_bits_loop5_spec (clf cl) (hdr : Std.U64) (c : Std.Usize) (hc : c.val ≤ 19)
    (hh : hdr.val ≤ 2 ^ 40 + c.val * 2 ^ 35) :
    slot.a_c_dyn_bits_loop5 clf cl hdr c ⦃ fun r => r.val ≤ 2 ^ 40 + 19 * 2 ^ 35 ⦄ := by
  rw [slot.a_c_dyn_bits_loop5]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, c') => 19 - c'.val)
    (inv := fun (h', c') => c'.val ≤ 19 ∧ h'.val ≤ 2 ^ 40 + c'.val * 2 ^ 35)
  · rintro ⟨h', c'⟩ ⟨h1, h2⟩
    simp only [slot.a_c_dyn_bits_loop5.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hc, hh⟩
@[local step]
theorem c_dyn_bits_spec (lf df) : slot.a_c_dyn_bits lf df ⦃ fun _ => True ⦄ := U1! slot.a_c_dyn_bits
@[local step]
theorem c_plan_blocks_loop0_loop0_spec (s : Slice Std.U8) (ec q : Std.Usize)
    (hec : ec.val ≤ s.length) (hn26 : s.length < 67108864) :
    slot.a_c_plan_blocks_loop0_loop0 s ec (Array.repeat 288#usize 0#u32) q ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_plan_blocks_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, q') => ec.val - q'.val)
    (inv := fun (lb', q') => LeAll lb'.val q'.val)
  · rintro ⟨lb', q'⟩ hlb'
    simp only [slot.a_c_plan_blocks_loop0_loop0.body]
    step*
    all_goals first
      | (have := LeAll_get hlb' i1.val (by scalar_tac)
         scalar_tac)
      | (refine ⟨?_, by scalar_tac⟩
         rw [a_post, Array.set_val_eq, show q1.val = q'.val + 1 by scalar_tac]
         apply LeAll_set_succ hlb'
         have := LeAll_get hlb' i1.val (by scalar_tac)
         scalar_tac)
  · exact engC_LeAll_repeat _ _ _ (by simp)
@[local step]
theorem c_plan_blocks_loop0_spec (s : Slice Std.U8) (plan) (n : Std.Usize) (lf df p fuel) (hn : n.val = s.length)
    (hn26 : n.val < 67108864) :
    slot.a_c_plan_blocks_loop0 s plan n lf df p fuel ⦃ fun _ => True ⦄ := by
  have hB := C_BLOCK_bounds
  rw [slot.a_c_plan_blocks_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, f) => f.val)
    (inv := fun _ => True)
  · rintro ⟨plan', lf', df', p', f'⟩ _
    simp only [slot.a_c_plan_blocks_loop0.body]
    step*
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split <;> step*
    rintro ca _
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Usize) => p'.val ≤ x.val ∧ x.val ≤ n.val)
    · split <;> step*
      all_goals scalar_tac
    rintro eb ⟨heb1, heb2⟩
    apply WP.spec_bind (Pₘ := fun (x : Std.Usize) => p'.val ≤ x.val ∧ x.val ≤ n.val)
    · split <;> step*
      all_goals scalar_tac
    rintro ec ⟨hec1, hec2⟩
    step*
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split <;> step*
    rintro cb _
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split <;> step*
    rintro cb1 _
    step*
    all_goals scalar_tac
  · trivial
@[local step]
theorem c_plan_blocks_spec (s : Slice Std.U8) (plan) (hn26 : s.length < 67108864) :
    slot.a_c_plan_blocks s plan ⦃ fun _ => True ⦄ := U1! slot.a_c_plan_blocks
@[local step]
theorem c_is_dna_loop_spec (s : Slice Std.U8) (n allow : Std.Usize) (bad i : Std.Usize) (hn : n.val ≤ s.length)
    (hbad : bad.val ≤ i.val) :
    slot.a_c_is_dna_loop s n allow bad i ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_is_dna_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i') => n.val - i'.val)
    (inv := fun (bad', i') => bad'.val ≤ i'.val)
  · rintro ⟨bad', i'⟩ hb'
    simp only [slot.a_c_is_dna_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hbad
@[local step]
theorem c_is_dna_spec (s) :
    slot.a_c_is_dna s ⦃ fun _ => True ⦄ := U1! slot.a_c_is_dna
@[local step]
theorem c_push_model_loop0_spec (lf df ll dl) (est : Std.U64) (q : Std.Usize) (hq : q.val ≤ 288)
    (he : est.val ≤ 70 + q.val * 2 ^ 42) :
    slot.a_c_push_model_loop0 lf df ll dl est q ⦃ fun r => r.val ≤ 70 + 288 * 2 ^ 42 ⦄ := by
  rw [slot.a_c_push_model_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, q') => 288 - q'.val)
    (inv := fun (e', q') => q'.val ≤ 288 ∧ e'.val ≤ 70 + q'.val * 2 ^ 42)
  · rintro ⟨e', q'⟩ ⟨h1, h2⟩
    simp only [slot.a_c_push_model_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hq, he⟩
@[local step]
theorem c_push_model_loop1_spec (models) (tokpen : Std.U32) (ll) (i : Std.Usize) (htok : tokpen.val ≤ 65536)
    (hm : models.length + (256 - i.val) < 4294967295) :
    slot.a_c_push_model_loop1 models tokpen ll i ⦃ fun r => r.length = models.length + (256 - i.val) ⦄ := by
  have h1 := C_SCALE_le
  have h2 := C_UNUSED_LIT_le
  rw [slot.a_c_push_model_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, i') => 256 - i'.val)
    (inv := fun (m', i') => m'.length = models.length + (i'.val - i.val) ∧ i.val ≤ i'.val ∧ i'.val ≤ max i.val 256)
  · rintro ⟨m', i'⟩ ⟨h3, h4, h5⟩
    simp only [slot.a_c_push_model_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨by simp, le_refl _, by scalar_tac⟩
@[local step]
theorem c_push_model_loop2_spec (models) (tax ulen tokpen : Std.U32) (ll) (l : Std.Usize) (htax : tax.val ≤ 65536)
    (hulen : ulen.val ≤ 65536) (htok : tokpen.val ≤ 65536) (hl : 3 ≤ l.val)
    (hm : models.length + (259 - l.val) < 4294967295) :
    slot.a_c_push_model_loop2 models tax ulen tokpen ll l ⦃ fun r => r.length = models.length + (259 - l.val) ⦄ := by
  have h1 := C_SCALE_le
  rw [slot.a_c_push_model_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, l') => 259 - l'.val)
    (inv := fun (m', l') => m'.length = models.length + (l'.val - l.val) ∧ l.val ≤ l'.val ∧ l'.val ≤ max l.val 259)
  · rintro ⟨m', l'⟩ ⟨h3, h4, h5⟩
    simp only [slot.a_c_push_model_loop2.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨by simp, le_refl _, by scalar_tac⟩
@[local step]
theorem c_push_model_loop3_spec (models) (udist : Std.U32) (dl) (d : Std.Usize) (hud : udist.val ≤ 65536)
    (hm : models.length + (32 - d.val) < 4294967295) :
    slot.a_c_push_model_loop3 models udist dl d ⦃ fun r => r.length = models.length + (32 - d.val) ⦄ := by
  have h1 := C_SCALE_le
  rw [slot.a_c_push_model_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, d') => 32 - d'.val)
    (inv := fun (m', d') => m'.length = models.length + (d'.val - d.val) ∧ d.val ≤ d'.val ∧ d'.val ≤ max d.val 32)
  · rintro ⟨m', d'⟩ ⟨h3, h4, h5⟩
    simp only [slot.a_c_push_model_loop3.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨by simp, le_refl _, by scalar_tac⟩
@[local step]
theorem c_push_model_spec (models lf df) (tax ulen udist tokpen : Std.U32) (htax : tax.val ≤ 65536) (hulen : ulen.val ≤ 65536)
    (hud : udist.val ≤ 65536) (htok : tokpen.val ≤ 65536) (hm : models.length + 544 < 4294967295) :
    slot.a_c_push_model models lf df tax ulen udist tokpen ⦃ fun r => r.1.val ≤ 70 + 288 * 2 ^ 42 ∧ r.2.length = models.length + 544 ⦄ := U1! slot.a_c_push_model
@[local step]
theorem c_restat_loop0_loop0_spec (s : Slice Std.U8) (choice) (n : Std.Usize) (lf df) (p t : Std.Usize)
    (hn : n.val ≤ s.length) (hnc : n.val ≤ choice.length) (hn26 : n.val < 67108864) :
    slot.a_c_restat_loop0_loop0 s choice n lf df p t ⦃ fun r => p.val ≤ r.2.2.val ∧
      r.2.2.val ≤ max p.val (n.val + 511) ∧
      (p.val < n.val → t.val < slot.A_C_BLOCK.val → p.val < r.2.2.val) ∧
      (r.2.2.val < n.val → p.val + (slot.A_C_BLOCK.val - t.val) ≤ r.2.2.val) ⦄ := by
  have hB := C_BLOCK_bounds
  rw [slot.a_c_restat_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, t') => slot.A_C_BLOCK.val - t'.val)
    (inv := fun (_, _, p', t') => p.val + (t'.val - t.val) ≤ p'.val ∧ t.val ≤ t'.val ∧
      p'.val ≤ max p.val (n.val + 511) ∧ t'.val ≤ max t.val slot.A_C_BLOCK.val)
  · rintro ⟨lf', df', p', t'⟩ ⟨h1, h2, h3, h4⟩
    simp only [slot.a_c_restat_loop0_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨by simp, le_refl _, by scalar_tac, by scalar_tac⟩
@[local step]
theorem c_restat_loop0_spec (s : Slice Std.U8) (choice models bstart) (tax ulen udist tokpen : Std.U32)
    (total : Std.U64) (n : Std.Usize) (lf df) (p : Std.Usize)
    (hn : n.val ≤ s.length) (hnc : n.val ≤ choice.length) (hn26 : n.val < 67108864)
    (htax : tax.val ≤ 65536) (hulen : ulen.val ≤ 65536) (hud : udist.val ≤ 65536) (htok : tokpen.val ≤ 65536)
    (hb : 544 * bstart.length ≤ models.length + 544)
    (ht : 544 * total.val ≤ models.length * (70 + 288 * 2 ^ 42))
    (hm : models.length * 8192 < 544 * (n.val + 8192))
    (hp : p.val < n.val → models.length * 8192 ≤ 544 * p.val) :
    slot.a_c_restat_loop0 s choice models bstart tax ulen udist tokpen total n lf df p ⦃ fun r =>
      544 * r.2.1.length ≤ r.1.length + 544 ∧ 544 * r.2.2.1.val ≤ r.1.length * (70 + 288 * 2 ^ 42) ∧
      r.1.length * 8192 < 544 * (n.val + 8192) ⦄ := by
  have hB := C_BLOCK_bounds
  rw [slot.a_c_restat_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, p') => n.val - p'.val)
    (inv := fun (m', b', t', _, _, p') => 544 * b'.length ≤ m'.length + 544 ∧
      544 * t'.val ≤ m'.length * (70 + 288 * 2 ^ 42) ∧ m'.length * 8192 < 544 * (n.val + 8192) ∧
      (p'.val < n.val → m'.length * 8192 ≤ 544 * p'.val))
  · rintro ⟨m', b', t', lf', df', p'⟩ ⟨h1, h2, h3, h4⟩
    simp only [slot.a_c_restat_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hb, ht, hm, hp⟩
@[local step]
theorem c_restat_spec (s : Slice Std.U8) (choice models bstart) (tax ulen udist tokpen : Std.U32)
    (hn26 : s.length < 67108864) (htax : tax.val ≤ 65536) (hulen : ulen.val ≤ 65536) (hud : udist.val ≤ 65536)
    (htok : tokpen.val ≤ 65536) :
    slot.a_c_restat s choice models bstart tax ulen udist tokpen ⦃ fun r => r.2.2.length ≤ 1048576 ⦄ := U1! slot.a_c_restat
@[local step]
theorem c_greedy_choice_loop0_spec (choice n p) :
    slot.a_c_greedy_choice_loop0 choice n p ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_greedy_choice_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (choice_, p_) => n.val - p_.val)
    (inv := fun _ => True)
  · rintro ⟨choice_, p_⟩ _
    simp only [slot.a_c_greedy_choice_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem c_greedy_choice_loop1_spec (clist choice n gmin) (m k : Std.Usize) (hm : m.val = clist.length) (hk : 1 ≤ k.val) :
    slot.a_c_greedy_choice_loop1 clist choice n gmin m k ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_greedy_choice_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, k') => m.val - k'.val)
    (inv := fun (_, k') => 1 ≤ k'.val)
  · rintro ⟨choice', k'⟩ hk'
    simp only [slot.a_c_greedy_choice_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hk
@[local step]
theorem c_greedy_choice_spec (clist choice n gmin) :
    slot.a_c_greedy_choice clist choice n gmin ⦃ fun _ => True ⦄ := U1! slot.a_c_greedy_choice
@[local step]
theorem c_load_model_loop0_spec (models : alloc.vec.Vec Std.U32) (lit_c len_c) (base i : Std.Usize) (hb : base.val + slot.A_C_MS.val ≤ models.length) :
    slot.a_c_load_model_loop0 models lit_c len_c base i ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_load_model_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (lit_c_, len_c_, i_) => 256 - i_.val)
    (inv := fun _ => True)
  · rintro ⟨lit_c_, len_c_, i_⟩ _
    simp only [slot.a_c_load_model_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem c_load_model_loop1_spec (models : alloc.vec.Vec Std.U32) (dst_c) (base d : Std.Usize) (hb : base.val + slot.A_C_MS.val ≤ models.length) :
    slot.a_c_load_model_loop1 models dst_c base d ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_load_model_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (dst_c_, d_) => 32 - d_.val)
    (inv := fun _ => True)
  · rintro ⟨dst_c_, d_⟩ _
    simp only [slot.a_c_load_model_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem c_load_model_spec (models) (b : Std.Usize) (lit_c len_c dst_c) (hb : b.val ≤ 1048576) :
    slot.a_c_load_model models b lit_c len_c dst_c ⦃ fun _ => True ⦄ := U1! slot.a_c_load_model
@[local step]
theorem c_group_start_spec (clist ge) :
    slot.a_c_group_start clist ge ⦃ fun r => r.val ≤ ge.val ⦄ := U1! slot.a_c_group_start
@[local step]
theorem c_dp_pass_loop0_loop0_spec (bstart : alloc.vec.Vec Std.U32) (b q : Std.Usize) (hb : b.val < bstart.length) :
    slot.a_c_dp_pass_loop0_loop0 bstart b q ⦃ fun r => r.val ≤ b.val ⦄ := by
  rw [slot.a_c_dp_pass_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun b' => b'.val)
    (inv := fun b' => b'.val ≤ b.val)
  · rintro b' hb'
    simp only [slot.a_c_dp_pass_loop0_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact le_refl _
@[local step]
theorem c_dp_pass_loop0_loop1_spec (s : Slice Std.U8) (choice : Slice Std.U32) (ring lit_c next) (p lo : Std.Usize)
    (hp : p.val ≤ s.length) (hc : s.length ≤ choice.length) :
    slot.a_c_dp_pass_loop0_loop1 s choice ring lit_c next p lo ⦃ fun r => r.1.length = choice.length ∧ r.2.2.2.val ≤ p.val ⦄ := by
  rw [slot.a_c_dp_pass_loop0_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, p') => p'.val)
    (inv := fun (c', _, _, p') => c'.length = choice.length ∧ p'.val ≤ p.val)
  · rintro ⟨c', r', n', p'⟩ ⟨h1, h2⟩
    simp only [slot.a_c_dp_pass_loop0_loop1.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨rfl, le_refl _⟩
@[local step]
theorem c_dp_pass_loop0_loop2_loop0_spec (ring len_c) (p : Std.Usize) (best ch) (l : Std.Usize) (dc tag) (len : Std.Usize)
    (hp : p.val ≤ 2 ^ 30) (hl : l.val ≤ 511) (hlen : 3 ≤ len.val) :
    slot.a_c_dp_pass_loop0_loop2_loop0 ring len_c p best ch l dc tag len ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_dp_pass_loop0_loop2_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, len') => l.val + 1 - len'.val)
    (inv := fun (_, _, len') => 3 ≤ len'.val)
  · rintro ⟨b', c', len'⟩ h1
    simp only [slot.a_c_dp_pass_loop0_loop2_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hlen
@[local step]
theorem c_dp_pass_loop0_loop2_spec (clist ring len_c dst_c) (ge p : Std.Usize) (best ch) (prev room k : Std.Usize)
    (hp : p.val ≤ 2 ^ 30) (hprev : 2 ≤ prev.val ∧ prev.val ≤ 511)
    (hk : k.val ≤ clist.length) (hcl : clist.length < 4294967295) :
    slot.a_c_dp_pass_loop0_loop2 clist ring len_c dst_c ge p best ch prev room k ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_dp_pass_loop0_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, k') => clist.length - k'.val)
    (inv := fun (_, _, prev', k') => 2 ≤ prev'.val ∧ prev'.val ≤ 511 ∧ k'.val ≤ clist.length)
  · rintro ⟨b', c', prev', k'⟩ ⟨h1, h2, h3⟩
    simp only [slot.a_c_dp_pass_loop0_loop2.body]
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Usize) => 2 ≤ x.val ∧ x.val ≤ 511)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro prev1 ⟨hq1, hq2⟩
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Usize) => x.val ≤ 511)
    · split <;> step*
      all_goals scalar_tac
    rintro l1 hl1
    step*
    all_goals scalar_tac
  · exact ⟨hprev.1, hprev.2, hk⟩
@[local step]
theorem c_dp_pass_loop0_spec (s : Slice Std.U8) (clist models : alloc.vec.Vec Std.U32) (bstart : alloc.vec.Vec Std.U32) (choice : Slice Std.U32)
    (n : Std.Usize) (ring lit_c len_c dst_c) (b loaded ge gs gp : Std.Usize) (next) (p fuel : Std.Usize)
    (hn : n.val = s.length) (hn26 : n.val < 67108864) (hc : n.val ≤ choice.length) (hb : b.val < bstart.length)
    (hnb : bstart.length ≤ 1048576) (hp : p.val ≤ n.val) (hgp : gp.val ≤ n.val ∨ gp.val < 2 ^ 27)
    (hcl : clist.length < 4294967295) (hgs : gs.val ≤ ge.val) (hge : ge.val ≤ clist.length) :
    slot.a_c_dp_pass_loop0 s clist models bstart choice n ring lit_c len_c dst_c b loaded ge gs gp next p fuel ⦃ fun _ => True ⦄ := by
  have hpm := C_PMASK_lt
  rw [slot.a_c_dp_pass_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, _, _, _, _, f) => f.val)
    (inv := fun (c', _, _, _, _, b', _, ge', gs', gp', _, p', _) => c'.length = choice.length ∧
      b'.val < bstart.length ∧ p'.val ≤ n.val ∧ (gp'.val ≤ n.val ∨ gp'.val < 2 ^ 27) ∧
      gs'.val ≤ ge'.val ∧ ge'.val ≤ clist.length)
  · rintro ⟨c', r', l1', l2', d', b', ld', ge', gs', gp', nx', p', f'⟩ ⟨h1, h2, h3, h4, h5, h6⟩
    simp only [slot.a_c_dp_pass_loop0.body]
    step*
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split <;> step*
    rintro ⟨lit_c1, len_c1, dst_c1, loaded1⟩ _
    step*
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
    rintro lo _
    step*
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split <;> step*
    rintro ⟨best1, ch1⟩ _
    step*
    all_goals scalar_tac
  · exact ⟨rfl, hb, hp, hgp, hgs, hge⟩
@[local step]
theorem c_dp_pass_spec (s : Slice Std.U8) (clist models) (bstart : alloc.vec.Vec Std.U32) (choice)
    (hn26 : s.length < 67108864) (hnb : bstart.length ≤ 1048576) (hcl : clist.length < 4294967295) :
    slot.a_c_dp_pass s clist models bstart choice ⦃ fun _ => True ⦄ := by
  have hms := C_MS_val
  have hpm := C_PMASK_lt
  rw [slot.a_c_dp_pass]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac
@[local step]
theorem c_pack_spec (len) (d : Std.Usize) (hd : 1 ≤ d.val) : slot.a_c_pack len d ⦃ fun _ => True ⦄ := U1! slot.a_c_pack
@[local step]
theorem c_push_cands_loop_spec (clist : alloc.vec.Vec Std.U32) (ml md) (cnt : Std.Usize) (flag) (top : Std.Usize)
    (pushed : Std.U32) (i : Std.Usize)
    (hcl : clist.length + (cnt.val - i.val) < 4294967295) (hpu : pushed.val ≤ 1) :
    slot.a_c_push_cands_loop clist ml md cnt flag top pushed i ⦃ fun r =>
      r.1.length ≤ clist.length + (cnt.val - i.val) ∧ r.2.2.val ≤ pushed.val + (cnt.val - i.val) ∧
      (top.val ≤ 258 → r.2.1.val ≤ 258) ⦄ := by
  rw [slot.a_c_push_cands_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, i') => 64 - i'.val)
    (inv := fun (c', t', u', i') => c'.length + (cnt.val - i'.val) ≤ clist.length + (cnt.val - i.val) ∧
      u'.val + (cnt.val - i'.val) ≤ pushed.val + (cnt.val - i.val) ∧ i.val ≤ i'.val ∧
      (top.val ≤ 258 → t'.val ≤ 258))
  · rintro ⟨c', t', u', i'⟩ ⟨h1, h2, h3, h4⟩
    simp only [slot.a_c_push_cands_loop.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨le_refl _, le_refl _, le_refl _, fun h => h⟩
@[local step]
theorem c_push_cands_spec (clist : alloc.vec.Vec Std.U32) (p ml md cnt r1 flag)
    (hcl : clist.length + slot.A_C_KEEP.val + 2 < 4294967295) :
    slot.a_c_push_cands clist p ml md cnt r1 flag ⦃ fun r => r.2.length ≤ clist.length + slot.A_C_KEEP.val + 2 ∧
      r.1.val ≤ 258 ⦄ := U1! slot.a_c_push_cands
@[local step]
theorem c_nt_code_spec (b) :
    slot.a_c_nt_code b ⦃ fun _ => True ⦄ := U1! slot.a_c_nt_code
@[local step]
theorem c_word_be_spec (s) (i : Std.Usize) (hi : i.val + 8 ≤ Usize.max) : slot.a_c_word_be s i ⦃ fun _ => True ⦄ := U1! slot.a_c_word_be
@[local step]
theorem c_extend_loop0_loop0_spec (s : Slice Std.U8) (a b lim k : Std.Usize) (ha : a.val + lim.val ≤ s.length) (hb : b.val + lim.val ≤ s.length) :
    slot.a_c_extend_loop0_loop0 s a b lim k ⦃ fun _ => True ⦄ := U4! slot.a_c_extend_loop0_loop0 slot.a_c_extend_loop0_loop0.body
@[local step]
theorem c_extend_loop0_loop1_spec (s : Slice Std.U8) (a b lim k : Std.Usize) (ha : a.val + lim.val ≤ s.length) (hb : b.val + lim.val ≤ s.length) :
    slot.a_c_extend_loop0_loop1 s a b lim k ⦃ fun _ => True ⦄ := U4! slot.a_c_extend_loop0_loop1 slot.a_c_extend_loop0_loop1.body
@[local step]
theorem c_extend_loop0_spec (s : Slice Std.U8) (a b lim k fuel : Std.Usize) (ha : a.val + lim.val ≤ s.length)
    (hb : b.val + lim.val ≤ s.length) (hk : k.val ≤ 2 ^ 31) (hlim : lim.val ≤ 2 ^ 31) :
    slot.a_c_extend_loop0 s a b lim k fuel ⦃ fun _ => True ⦄ := by
  rw [slot.a_c_extend_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, f') => f'.val)
    (inv := fun (k', _) => k'.val ≤ 2 ^ 31)
  · rintro ⟨k', f'⟩ hk'
    simp only [slot.a_c_extend_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hk
@[local step]
theorem c_extend_spec (s : Slice Std.U8) (a b k0 lim : Std.Usize) (ha : a.val + lim.val ≤ s.length) (hb : b.val + lim.val ≤ s.length)
    (hk0 : k0.val ≤ 2 ^ 31) (hlim : lim.val ≤ 2 ^ 31) :
    slot.a_c_extend s a b k0 lim ⦃ fun _ => True ⦄ := U1! slot.a_c_extend
@[local step]
theorem c_chain_walk_loop_spec (s : Slice Std.U8) (p k0 depth : Std.Usize) (prev ml md) (lim cur best cnt steps : Std.Usize)
    (hp : p.val + lim.val ≤ s.length) (hlim : lim.val ≤ 258) (hk0 : k0.val ≤ 2 ^ 31) :
    slot.a_c_chain_walk_loop s p k0 depth prev ml md lim cur best cnt steps ⦃ fun _ => True ⦄ := by
  have hws := C_WS_val
  rw [slot.a_c_chain_walk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, st) => depth.val - st.val)
    (inv := fun _ => True)
  · rintro ⟨ml', md', cur', best', cnt', st'⟩ _
    simp only [slot.a_c_chain_walk_loop.body]
    step*
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ⟨ml1, md1, best1, cnt1⟩ _
    step*
    all_goals scalar_tac
  · trivial
@[local step]
theorem c_chain_walk_spec (s : Slice Std.U8) (p key k0 best0 depth head prev ml md) (hp : p.val < s.length) (hk0 : k0.val ≤ 2 ^ 31) :
    slot.a_c_chain_walk s p key k0 best0 depth head prev ml md ⦃ fun _ => True ⦄ := by
  have hws := C_WS_val
  have hhs := C_HS_bounds
  rw [slot.a_c_chain_walk]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac
@[local step]
theorem c_put_kid_spec (kids) (which : Std.Usize) (idx v) (hw : which.val ≤ 1) :
    slot.a_c_put_kid kids which idx v ⦃ fun _ => True ⦄ := by
  have hws := C_WS_val
  have hks := C_KS_val
  rw [slot.a_c_put_kid]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac
@[local step]
theorem c_bt_find_loop_spec (back) (s : Slice Std.U8) (p depth kids ml md) (lim cur lw li gw gi llen glen : Std.Usize)
    (best cnt steps i)
    (hp : p.val + lim.val ≤ s.length) (hlim : lim.val ≤ 258) (hlw : lw.val ≤ 1) (hgw : gw.val ≤ 1)
    (hll : llen.val ≤ lim.val) (hgl : glen.val ≤ lim.val) :
    slot.a_c_bt_find_loop back s p depth kids ml md lim cur lw li gw gi llen glen best cnt steps i ⦃ fun _ => True ⦄ := by
  have hws := C_WS_val
  have hks := C_KS_val
  rw [slot.a_c_bt_find_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, _, _, _, _, st) => depth.val - st.val)
    (inv := fun (_, _, _, _, lw', _, gw', _, ll', gl', _, _, _) => lw'.val ≤ 1 ∧ gw'.val ≤ 1 ∧
      ll'.val ≤ lim.val ∧ gl'.val ≤ lim.val)
  · rintro ⟨kids', ml', md', cur', lw', li', gw', gi', ll', gl', best', cnt', st'⟩ ⟨h1, h2, h3, h4⟩
    simp only [slot.a_c_bt_find_loop.body]
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Usize) => x.val ≤ lim.val)
    · split <;> step*
      all_goals scalar_tac
    rintro k0 hk0
    step*
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ⟨ml1, md1, best1, cnt1⟩ _
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Array Std.U32 65536#usize × Std.Usize × Std.Usize × Std.Usize ×
        Std.Usize × Std.Usize × Std.Usize × Std.Usize) =>
      x.2.2.1.val ≤ 1 ∧ x.2.2.2.2.1.val ≤ 1 ∧ x.2.2.2.2.2.2.1.val ≤ lim.val ∧ x.2.2.2.2.2.2.2.val ≤ lim.val)
    · split <;> step*
      all_goals scalar_tac
    rintro ⟨kids1, cur1, lw1, li1, gw1, gi1, llen1, glen1⟩ ⟨h5, h6, h7, h8⟩
    step*
    all_goals scalar_tac
  · exact ⟨hlw, hgw, hll, hgl⟩
@[local step]
theorem c_bt_find_spec (s : Slice Std.U8) (p h depth head kids ml md) (hp : p.val < s.length) :
    slot.a_c_bt_find s p h depth head kids ml md ⦃ fun _ => True ⦄ := by
  have hws := C_WS_val
  have hhs := C_HS_bounds
  rw [slot.a_c_bt_find]
  step*
  repeat' (split <;> step*)
  all_goals scalar_tac
@[local step]
theorem c_find_dna_loop0_spec (s : Slice Std.U8) (n key : Std.Usize) (run run2 q : Std.Usize) (hn : n.val = s.length)
    (hrun : run.val ≤ q.val) (hrun2 : run2.val ≤ q.val) (hq : q.val ≤ 7) :
    slot.a_c_find_dna_loop0 s n key run run2 q ⦃ fun r => r.2.1.val ≤ 7 ∧ r.2.2.val ≤ 7 ⦄ := by
  rw [slot.a_c_find_dna_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, q') => 7 - q'.val)
    (inv := fun (_, r1, r2, q') => r1.val ≤ q'.val ∧ r2.val ≤ q'.val ∧ q'.val ≤ 7)
  · rintro ⟨k', r1, r2, q'⟩ ⟨h1, h2, h3⟩
    simp only [slot.a_c_find_dna_loop0.body]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hrun, hrun2, hq⟩
@[local step]
theorem c_find_dna_loop1_spec (s : Slice Std.U8) (clist) (depth_lo n : Std.Usize) (head8 prev8 head3 kids ml md)
    (key run run2 p skip_to : Std.Usize)
    (hn : n.val = s.length) (hn26 : n.val < 67108864) (hrun : run.val ≤ p.val + 7) (hrun2 : run2.val ≤ p.val + 7)
    (hp : p.val ≤ n.val) (hcl : clist.length ≤ 34 * p.val) :
    slot.a_c_find_dna_loop1 s clist depth_lo n head8 prev8 head3 kids ml md key run run2 p skip_to ⦃ fun r =>
      r.length ≤ 34 * n.val ⦄ := by
  have hws := C_WS_val
  have hhs := C_HS_bounds
  have hkp := C_KEEP_le
  have hup := C_UP_MIN_ge
  rw [slot.a_c_find_dna_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, _, _, _, _, p', _) => n.val - p'.val)
    (inv := fun (c', _, _, _, _, _, _, _, r1, r2, p', _) => r1.val ≤ p'.val + 7 ∧ r2.val ≤ p'.val + 7 ∧
      p'.val ≤ n.val ∧ c'.length ≤ 34 * p'.val)
  · rintro ⟨c', h8', pv8', h3', kids', ml', md', key', r1, r2, p', sk'⟩ ⟨h1, h2, h3, h4⟩
    unfold slot.a_c_find_dna_loop1.body
    step*
    apply WP.spec_bind (Pₘ := fun (x : Std.Usize × Std.Usize × Std.Usize) =>
      x.2.1.val ≤ p'.val + 8 ∧ x.2.2.val ≤ p'.val + 8)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ⟨key1, run1, run21⟩ ⟨hr1, hr2⟩
    step*
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.Array Std.U32 65536#usize ×
        Std.Array Std.U32 32768#usize × Std.Array Std.U32 65536#usize × Std.Array Std.U32 65536#usize ×
        Std.Array Std.U32 64#usize × Std.Array Std.U32 64#usize × Std.Usize) =>
      x.1.length ≤ c'.length + 34)
    · apply engC_ite_spec
      · intro hc
        step*
        · -- a lower-case letter: binary tree on 3-byte keys
          apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
          · apply engC_ite_spec
            · intro hs
              step*
              apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
              · apply engC_ite_spec
                · intro hcnt
                  step*
                  apply engC_bind_ite_spec <;> intro _ <;> step*
                · intro hcnt
                  step*
              · rintro ⟨v2, a4, a5, i17⟩ hv2
                step*
            · intro hs
              step*
          · rintro ⟨v1, a, a1, a2, a3, i16⟩ hv1
            step*
        · -- any other byte above 'z'
          apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
          · apply engC_ite_spec
            · -- a run of at least 8 nucleotides: exact 8-mer chains
              intro hr
              apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
              · apply engC_ite_spec
                · intro hs
                  step*
                  apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
                  · apply engC_ite_spec
                    · intro hcnt
                      step*
                      apply engC_bind_ite_spec <;> intro _ <;> step*
                    · intro hcnt
                      step*
                  · rintro ⟨v2, a9, a10, i5⟩ hv2
                    step*
                · intro hs
                  step*
              · rintro ⟨v1, a5, a6, a7, a8, i3⟩ hv1
                step*
            · -- other runs (newlines allowed): chains on whole words
              intro hr
              apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
              · apply engC_ite_spec
                · intro hr2
                  step*
                  apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
                  · apply engC_ite_spec
                    · intro hcnt
                      step*
                      apply engC_bind_ite_spec <;> intro _ <;> step*
                    · intro hcnt
                      step*
                  · rintro ⟨v2, a9, a10, i10⟩ hv2
                    step*
                · intro hr2
                  step*
              · rintro ⟨v1, a5, a6, a7, a8, i3⟩ hv1
                step*
          · rintro ⟨v, a, a1, a2, a3, a4, i2⟩ hv
            step*
        · -- any other byte below 'a'
          apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
          · apply engC_ite_spec
            · -- a run of at least 8 nucleotides: exact 8-mer chains
              intro hr
              apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
              · apply engC_ite_spec
                · intro hs
                  step*
                  apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
                  · apply engC_ite_spec
                    · intro hcnt
                      step*
                      apply engC_bind_ite_spec <;> intro _ <;> step*
                    · intro hcnt
                      step*
                  · rintro ⟨v2, a9, a10, i5⟩ hv2
                    step*
                · intro hs
                  step*
              · rintro ⟨v1, a5, a6, a7, a8, i3⟩ hv1
                step*
            · -- other runs (newlines allowed): chains on whole words
              intro hr
              apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
              · apply engC_ite_spec
                · intro hr2
                  step*
                  apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × _) => x.1.length ≤ c'.length + 34)
                  · apply engC_ite_spec
                    · intro hcnt
                      step*
                      apply engC_bind_ite_spec <;> intro _ <;> step*
                    · intro hcnt
                      step*
                  · rintro ⟨v2, a9, a10, i10⟩ hv2
                    step*
                · intro hr2
                  step*
              · rintro ⟨v1, a5, a6, a7, a8, i3⟩ hv1
                step*
          · rintro ⟨v, a, a1, a2, a3, a4, i2⟩ hv
            step*
      · intro hc
        step*
    rintro ⟨clist1, head81, prev81, head31, kids1, ml1, md1, skip_to1⟩ hc1
    step*
    all_goals scalar_tac
  · exact ⟨hrun, hrun2, hp, hcl⟩
@[local step]
theorem c_find_dna_spec (s : Slice Std.U8) (clist) (depth_lo) (hn26 : s.length < 67108864) (hcl : clist.length = 0) :
    slot.a_c_find_dna s clist depth_lo ⦃ fun r => r.length ≤ 34 * s.length ⦄ := by
  rw [slot.a_c_find_dna]
  step*
@[local step]
theorem c_run_len_spec (s : Slice Std.U8) (p : Std.Usize) (hp : p.val ≤ 2 ^ 31) : slot.a_c_run_len s p ⦃ fun _ => True ⦄ := U1! slot.a_c_run_len
@[local step]
theorem c_find_bin_loop_spec (s : Slice Std.U8) (clist) (chain depth n : Std.Usize) (head lt kids ml md)
    (p skip_to pend : Std.Usize)
    (hn : n.val = s.length) (hn26 : n.val < 67108864) (hp : p.val ≤ n.val) (hcl : clist.length ≤ 34 * p.val) :
    slot.a_c_find_bin_loop s clist chain depth n head lt kids ml md p skip_to pend ⦃ fun r => r.length ≤ 34 * n.val ⦄ := by
  have hws := C_WS_val
  have hhs := C_HS_bounds
  have hkp := C_KEEP_le
  rw [slot.a_c_find_bin_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, _, _, p', _, _) => n.val - p'.val)
    (inv := fun (c', _, _, _, _, _, p', _, _) => p'.val ≤ n.val ∧ c'.length ≤ 34 * p'.val)
  · rintro ⟨c', hd', lt', kids', ml', md', p', sk', pe'⟩ ⟨h1, h2⟩
    unfold slot.a_c_find_bin_loop.body
    step*
    apply WP.spec_bind (Pₘ := fun _ => True)
    · split <;> step*
    rintro key _
    step*
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.Array Std.U32 65536#usize ×
        Std.Array Std.U32 32768#usize × Std.Array Std.U32 65536#usize × Std.Array Std.U32 64#usize ×
        Std.Array Std.U32 64#usize × Std.Usize × Std.Usize) =>
      x.1.length ≤ c'.length + 34)
    · split
      · -- p ≥ skip_to: search, push the candidates, maybe skip ahead
        step*
        apply WP.spec_bind (Pₘ := fun _ => True)
        · split <;> step*
        rintro ⟨head2, lt2, kids2, ml2, md2, cnt⟩ _
        step*
        apply WP.spec_bind (Pₘ := fun _ => True)
        · repeat' (split <;> step*)
        rintro r1 _
        step*
        apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.Usize) =>
          x.1.length ≤ c'.length + 34 ∧ x.2.val ≤ 258)
        · repeat' (split <;> step*)
          all_goals scalar_tac
        rintro ⟨clist2, top⟩ ⟨hc2, htop⟩
        step*
        apply WP.spec_bind (Pₘ := fun _ => True)
        · repeat' (split <;> step*)
          all_goals scalar_tac
        rintro ⟨i19, i20⟩ _
        step*
      · -- inside a skipped stretch: only the chain insert
        step*
        apply WP.spec_bind (Pₘ := fun _ => True)
        · split <;> step*
        rintro ⟨a, a1⟩ _
        step*
    rintro ⟨clist1, head1, lt1, kids1, ml1, md1, skip_to1, pend1⟩ hc1
    step*
    all_goals scalar_tac
  · exact ⟨hp, hcl⟩
@[local step]
theorem c_find_bin_spec (s : Slice Std.U8) (clist chain depth) (hn26 : s.length < 67108864) (hcl : clist.length = 0) :
    slot.a_c_find_bin s clist chain depth ⦃ fun r => r.length ≤ 34 * s.length ⦄ := by
  rw [slot.a_c_find_bin]
  step*
set_option hygiene false in
local notation "U9!" q0__:max q1__:max => (by
  have h1 := C_UNUSED_LEN_le
  have h2 := C_UNUSED_DIST_le
  have h3 := C_STOP_DIV_pos
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun (_, _, _, _, pass') => passes.val - pass'.val)
    (inv := fun (_, _, b', _, _) => b'.length ≤ 1048576)
  · rintro ⟨out', models', b', le', pass'⟩ hb'
    simp only [q1__]
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · exact hnb)
@[local step]
theorem c_engine_loop0_spec (input : Slice Std.U8) (out min_dna dna) (clist : alloc.vec.Vec Std.U32) (models)
    (bstart : alloc.vec.Vec Std.U32) (passes) (tax tokpen : Std.U32) (last_est pass)
    (hn26 : input.length < 67108864) (htax : tax.val ≤ 65536) (htok : tokpen.val ≤ 65536)
    (hnb : bstart.length ≤ 1048576) (hcl : clist.length < 4294967295) :
    slot.a_c_engine_loop0 input out min_dna dna clist models bstart passes tax tokpen last_est pass ⦃ fun _ => True ⦄ := U9! slot.a_c_engine_loop0 slot.a_c_engine_loop0.body
@[local step]
theorem c_engine_loop1_spec (input : Slice Std.U8) (out min_dna dna) (clist : alloc.vec.Vec Std.U32) (models)
    (bstart : alloc.vec.Vec Std.U32) (passes) (tax tokpen : Std.U32) (last_est pass)
    (hn26 : input.length < 67108864) (htax : tax.val ≤ 65536) (htok : tokpen.val ≤ 65536)
    (hnb : bstart.length ≤ 1048576) (hcl : clist.length < 4294967295) :
    slot.a_c_engine_loop1 input out min_dna dna clist models bstart passes tax tokpen last_est pass ⦃ fun _ => True ⦄ := U9! slot.a_c_engine_loop1 slot.a_c_engine_loop1.body
@[local step]
theorem c_engine_loop2_spec (input : Slice Std.U8) (out min_dna dna) (clist : alloc.vec.Vec Std.U32) (models)
    (bstart : alloc.vec.Vec Std.U32) (passes) (tax tokpen : Std.U32) (last_est pass)
    (hn26 : input.length < 67108864) (htax : tax.val ≤ 65536) (htok : tokpen.val ≤ 65536)
    (hnb : bstart.length ≤ 1048576) (hcl : clist.length < 4294967295) :
    slot.a_c_engine_loop2 input out min_dna dna clist models bstart passes tax tokpen last_est pass ⦃ fun _ => True ⦄ := U9! slot.a_c_engine_loop2 slot.a_c_engine_loop2.body
@[local step]
theorem c_engine_spec (input : Slice Std.U8) (out) (depth depth_lo wdp passes_w passes_bt passes_dna min_dna passes_c4 : Std.Usize)
    (hn : input.length < 67108864) (h1 : depth.val ≤ 65536) (h2 : depth_lo.val ≤ 65536) (h3 : wdp.val ≤ 65536)
    (h4 : passes_w.val ≤ 65536) (h5 : passes_bt.val ≤ 65536) (h6 : passes_dna.val ≤ 65536) (h7 : min_dna.val ≤ 65536)
    (h8 : passes_c4.val ≤ 65536) :
    slot.a_c_engine input out depth depth_lo wdp passes_w passes_bt passes_dna min_dna passes_c4 ⦃ fun _ => True ⦄ := by
  have f1 := C_TAX_W_le
  have f2 := C_TAX_C4_le
  have f3 := C_TAX_BT_le
  have f4 := C_UNUSED_LEN_W_le
  have f5 := C_UNUSED_DIST_W_le
  have f6 := C_TOKPEN_le
  have f7 := C_TOKPEN_W_le
  have f8 := C_TOKPEN_C4_le
  have f9 := C_TOKPEN_BT_le
  have f10 := C_UNUSED_LEN_le
  have f11 := C_UNUSED_DIST_le
  have f12 := C_CHAIN4_RATIO_le
  rw [slot.a_c_engine]
  step*
  · -- dna = 0, few 6-byte repeats: weights DP (4-byte chains)
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32) => x.length ≤ 34 * input.length)
    · repeat' (split <;> step*)
      all_goals exact engC_with_capacity_length _
    rintro clist1 hc1
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
    rintro passes _
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro tax htax
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ulen hulen
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro udist hudist
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
    rintro gmin _
    step*
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.U32) => x.2.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ⟨out1, tokpen⟩ htok
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · -- dna = 0, repetitive: tree or 4-byte chains
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro chain4 _
    step*
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32) => x.length ≤ 34 * input.length)
    · repeat' (split <;> step*)
      all_goals exact engC_with_capacity_length _
    rintro clist1 hc1
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
    rintro passes _
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro tax htax
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ulen hulen
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro udist hudist
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
    rintro gmin _
    step*
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.U32) => x.2.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ⟨out1, tokpen⟩ htok
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
  · -- DNA
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32) => x.length ≤ 34 * input.length)
    · repeat' (split <;> step*)
      all_goals exact engC_with_capacity_length _
    rintro clist1 hc1
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
    rintro passes _
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro tax htax
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ulen hulen
    apply WP.spec_bind (Pₘ := fun (x : Std.U32) => x.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro udist hudist
    apply WP.spec_bind (Pₘ := fun _ => True)
    · repeat' (split <;> step*)
    rintro gmin _
    step*
    apply WP.spec_bind (Pₘ := fun (x : alloc.vec.Vec Std.U32 × Std.U32) => x.2.val ≤ 65536)
    · repeat' (split <;> step*)
      all_goals scalar_tac
    rintro ⟨out1, tokpen⟩ htok
    step*
    repeat' (split <;> step*)
    all_goals scalar_tac
theorem spine_CFG_le : ∀ r ∈ slot.A_CFG.val, ∀ x ∈ r.val, x.val ≤ 65536 := by
  unfold slot.A_CFG; decide
theorem spine_CFG_skip : ∀ r ∈ slot.A_CFG.val, (r.val[0]!).val = 0 → 3 ≤ (r.val[2]!).val := by
  unfold slot.A_CFG; decide
theorem spine_knob_le {m : Std.Usize} {r : Array Std.Usize m} (hr : ∀ x ∈ r.val, x.val ≤ 65536)
    {x : Std.Usize} {j : Nat} {hj : j < r.val.length} (hx : x = r.val[j]) : x.val ≤ 65536 := by
  subst hx; exact hr _ (List.getElem_mem _)
theorem spine_knob_skip {m : Std.Usize} {r : Array Std.Usize m}
    (hs : (r.val[0]!).val = 0 → 3 ≤ (r.val[2]!).val)
    {x0 x2 : Std.Usize} {h0 : 0 < r.val.length} {h2 : 2 < r.val.length}
    (hx0 : x0 = r.val[0]) (hz : x0 = 0#usize) (hx2 : x2 = r.val[2]) : 3 ≤ x2.val := by
  rw [getElem!_pos r.val 0 h0, getElem!_pos r.val 2 h2, ← hx0, ← hx2, hz] at hs
  exact hs rfl
@[local step]
theorem plan_cfg_spec (input : Slice Std.U8) (k) (hn : input.length < 67108864) :
    slot.a_plan_cfg input k ⦃ fun _ => True ⦄ := by
  rw [slot.a_plan_cfg]
  step*
  all_goals
    have hc : c ∈ slot.A_CFG.val := by rw [c_post]; exact List.getElem_mem _
    first
    | exact spine_knob_le (spine_CFG_le c hc) (by assumption)
    | exact spine_knob_skip (spine_CFG_skip c hc) (by assumption) (by assumption) (by assumption)
theorem spine_make_plan_lt_spec (input : Slice Std.U8) (hn : input.length < 67108864) :
    slot.a_make_plan input ⦃ fun _ => True ⦄ := by
  rw [slot.a_make_plan]
  step*
@[local step]
theorem make_plan_spec (input) : slot.a_make_plan input ⦃ fun _ => True ⦄ := by
  rw [slot.a_make_plan]
  step*
@[local step]
theorem make_plan_k_spec (input) (k : Std.Usize) : slot.a_make_plan_k input k ⦃ fun _ => True ⦄ := by
  rw [slot.a_make_plan_k]
  step*
theorem parse_mode_spec (input : Slice Std.U8) (out : Slice Std.U32) (k : Std.Usize)
    (hlen : input.length ≤ out.length) :
    slot.a_parse_mode input out k ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.a_parse_mode]
  step*
  refine ⟨by assumption, by assumption, ?_⟩
  unfold LZ77.Valid
  assumption
theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.a_parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.a_parse]
  step*
  refine ⟨by assumption, by assumption, ?_⟩
  unfold LZ77.Valid
  assumption
end EA
set_option hygiene false in
local notation "U12!" q0__:max q1__:max => (by
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
local notation "U13!" => (by
  (
  exact match_len_loop_spec input a b cap 0#usize ha hb (by scalar_tac)
    (LZ77.Matches.zero input a.val b.val)))
namespace EB
open Aeneas Aeneas.Std Result ControlFlow
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open LZ77 (toks bytes bytes_length bytes_getElem! Matches emit_lit emit_match ite_ok)
theorem spec_ite_cut {α : Type} (c : Prop) [Decidable c] (a b : Result α) (Q : α → Prop)
    (ha : c → a ⦃ Q ⦄) (hb : ¬c → b ⦃ Q ⦄) : (if c then a else b) ⦃ Q ⦄ := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h
set_option hygiene false in
local notation "U10!" q0__:max => (by
  rw [q0__]
  try simp only [ite_ok]
  step*
  all_goals (repeat (split <;> step*))
  all_goals scalar_tac)
@[local step]
theorem get_spec (v : Slice Std.U32) (i : Std.Usize) :
    slot.b_get v i ⦃ fun _ => True ⦄ := U10! slot.b_get
@[local step]
theorem set_spec (v : Slice Std.U32) (i : Std.Usize) (x : Std.U32) :
    slot.b_set v i x ⦃ fun _ => True ⦄ := U10! slot.b_set
set_option hygiene false in
local notation "U11!" q0__:max => (by
  rw [q0__]
  simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (split <;> step*))
  all_goals scalar_tac)
@[local step]
theorem bump_spec (v : Slice Std.U32) (i : Std.Usize) (by0 : Std.U32) :
    slot.b_bump v i by0 ⦃ fun _ => True ⦄ := U11! slot.b_bump
@[local step]
theorem set64_spec (v : Slice Std.U64) (i : Std.Usize) (x : Std.U64) :
    slot.b_set64 v i x ⦃ fun _ => True ⦄ := U10! slot.b_set64
@[local step]
theorem get8_spec (v : Slice Std.U8) (i : Std.Usize) :
    slot.b_get8 v i ⦃ fun _ => True ⦄ := U10! slot.b_get8
@[local step]
theorem byte_at_spec (input : Slice Std.U8) (i : Std.Usize) :
    slot.b_byte_at input i ⦃ fun _ => True ⦄ := U10! slot.b_byte_at
@[local step]
theorem setc_spec (a : Array Std.U32 65536#usize) (i : Std.Usize) (x : Std.U32) :
    slot.b_setc a i x ⦃ fun _ => True ⦄ := U10! slot.b_setc
theorem filled_loop0_spec (x : Std.U32) (v0 : alloc.vec.Vec Std.U32) (n8 i0 : Std.Usize)
    (hn8 : 8 * n8.val ≤ Std.Usize.max) (h0 : v0.length = 8 * i0.val) (hi : i0.val ≤ n8.val) :
    slot.b_filled_loop0 x v0 n8 i0 ⦃ fun r => r.length = 8 * n8.val ⦄ := by
  rw [slot.b_filled_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n8.val - s.2.val)
    (inv := fun s => s.1.length = 8 * s.2.val ∧ s.2.val ≤ n8.val)
  · rintro ⟨v, i⟩ ⟨hv, hle⟩
    simp only at hv hle
    simp only [slot.b_filled_loop0.body]
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
    slot.b_filled_loop1 n x v0 j0 ⦃ fun r => r.length = n.val ⦄ := by
  rw [slot.b_filled_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.val)
    (inv := fun s => s.1.length = s.2.val ∧ s.2.val ≤ n.val)
  · rintro ⟨v, j⟩ ⟨hv, hle⟩
    simp only at hv hle
    simp only [slot.b_filled_loop1.body]
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
    slot.b_filled n x ⦃ fun r => r.length = n.val ⦄ := by
  rw [slot.b_filled]
  step*
  apply Std.WP.spec_bind (filled_loop0_spec x _ n8 0#usize (by scalar_tac)
    (by simp [alloc.vec.Vec.with_capacity]) (by scalar_tac))
  intro v1 hv1
  step*
  exact filled_loop1_spec n x v1 j (by scalar_tac) (by scalar_tac)
@[local step]
theorem push_guarded_spec (v : alloc.vec.Vec Std.U32) (x : Std.U32) :
    slot.b_push_guarded v x ⦃ fun _ => True ⦄ := U10! slot.b_push_guarded
@[local step]
theorem sel_spec (f : Std.Usize) (a : Std.Usize) (b : Std.Usize) :
    slot.b_sel f a b ⦃ fun _ => True ⦄ := U10! slot.b_sel
@[local step]
theorem sel32_spec (f : Std.Usize) (a : Std.U32) (b : Std.U32) :
    slot.b_sel32 f a b ⦃ fun _ => True ⦄ := U10! slot.b_sel32
@[local step]
theorem sel64_spec (f : Std.Usize) (a : Std.U64) (b : Std.U64) :
    slot.b_sel64 f a b ⦃ fun _ => True ⦄ := U10! slot.b_sel64
@[local step]
theorem ge_spec (a : Std.Usize) (b : Std.Usize) :
    slot.b_ge a b ⦃ fun _ => True ⦄ := U10! slot.b_ge
@[local step]
theorem lt_spec (a : Std.Usize) (b : Std.Usize) :
    slot.b_lt a b ⦃ fun _ => True ⦄ := U10! slot.b_lt
@[local step]
theorem eq_spec (a : Std.Usize) (b : Std.Usize) :
    slot.b_eq a b ⦃ fun _ => True ⦄ := U10! slot.b_eq
@[local step]
theorem lt32_spec (a : Std.U32) (b : Std.U32) :
    slot.b_lt32 a b ⦃ fun _ => True ⦄ := U10! slot.b_lt32
@[local step]
theorem lt64_spec (a : Std.U64) (b : Std.U64) :
    slot.b_lt64 a b ⦃ fun _ => True ⦄ := U10! slot.b_lt64
@[local step]
theorem umin_spec (a : Std.Usize) (b : Std.Usize) :
    slot.b_umin a b ⦃ fun _ => True ⦄ := U10! slot.b_umin
@[local step]
theorem umax_spec (a : Std.Usize) (b : Std.Usize) :
    slot.b_umax a b ⦃ fun _ => True ⦄ := U10! slot.b_umax
@[local step]
theorem eq64_spec (a : Std.U64) (b : Std.U64) :
    slot.b_eq64 a b ⦃ fun _ => True ⦄ := U10! slot.b_eq64
@[local step]
theorem umin64_spec (a : Std.U64) (b : Std.U64) :
    slot.b_umin64 a b ⦃ fun _ => True ⦄ := U10! slot.b_umin64
@[local step]
theorem push_if_spec (v : alloc.vec.Vec Std.U32) (f : Std.Usize) (x : Std.U32) :
    slot.b_push_if v f x ⦃ fun _ => True ⦄ := U10! slot.b_push_if
@[local step]
theorem umin32_spec (a : Std.U32) (b : Std.U32) :
    slot.b_umin32 a b ⦃ fun _ => True ⦄ := U10! slot.b_umin32
@[local step]
theorem dslot_old_spec (d : Std.Usize) :
    slot.b_dslot_old d ⦃ fun _ => True ⦄ := U11! slot.b_dslot_old
@[local step]
theorem dslot_spec (d : Std.Usize) :
    slot.b_dslot d ⦃ fun _ => True ⦄ := by
  rw [slot.b_dslot]
  apply spec_ite_cut <;> intro hc <;> step*
  all_goals (repeat (split <;> step*))
  all_goals scalar_tac
@[local step]
theorem pack_m_spec (len : Std.Usize) (d : Std.Usize) :
    slot.b_pack_m len d ⦃ fun _ => True ⦄ := U11! slot.b_pack_m
@[local step]
theorem push_m_spec (v : alloc.vec.Vec Std.U32) (f : Std.Usize) (len : Std.Usize) (d : Std.Usize) :
    slot.b_push_m v f len d ⦃ fun _ => True ⦄ := U10! slot.b_push_m
@[local step]
theorem push_slot1_spec (mc : alloc.vec.Vec Std.U32) (m0 : Std.Usize) (len : Std.Usize) (d : Std.Usize) :
    slot.b_push_slot1 mc m0 len d ⦃ fun _ => True ⦄ := U11! slot.b_push_slot1
@[local step]
theorem push_slot_spec (mc : alloc.vec.Vec Std.U32) (m0 : Std.Usize) (f : Std.Usize) (len : Std.Usize) (d : Std.Usize) :
    slot.b_push_slot mc m0 f len d ⦃ fun _ => True ⦄ := U10! slot.b_push_slot
@[local step]
theorem clamp_step_spec (l room : Std.Usize) :
    slot.b_clamp_step l room ⦃ fun r => 1 ≤ r.val ∧ (r.val = 1 ∨ r.val ≤ room.val) ⦄ := by
  rw [slot.b_clamp_step]
  step*
@[local step]
theorem clamp1_spec (l room : Std.Usize) :
    slot.b_clamp1 l room ⦃ fun r => 1 ≤ r.val ∧ (r.val = 1 ∨ r.val ≤ room.val) ⦄ := by
  rw [slot.b_clamp1]
  step*
@[local step]
theorem nz64_spec (x : Std.U64) : slot.b_nz64 x ⦃ fun r => 0 < r.val ⦄ := by
  rw [slot.b_nz64]
  step*
theorem match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.b_match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := U12! slot.b_match_len_loop slot.b_match_len_loop.body
@[local step]
theorem match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.b_match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := U13!
theorem verified_spec (input : Slice Std.U8) (pos d ch : Std.Usize) :
    slot.b_verified input pos d ch ⦃ fun b => b = true →
      3 ≤ ch.val ∧ ch.val ≤ 258 ∧ 1 ≤ d.val ∧ d.val ≤ 32768 ∧ d.val ≤ pos.val ∧
      pos.val + ch.val ≤ input.length ∧ Matches input (pos.val - d.val) pos.val ch.val ⦄ := by
  rw [slot.b_verified]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  intro hv
  have hv' : ch.val ≤ v.val := by simpa using hv
  refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac,
    by scalar_tac, ?_⟩
  rw [show pos.val - d.val = i1.val by scalar_tac]
  exact Matches.mono v_post2 hv'
theorem emit_all_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (plan : Slice Std.U32) (n k0 ntok0 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ n.val) (hntok : ntok0.val ≤ k0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take k0.val)) :
    slot.b_emit_all_loop input out0 plan n k0 ntok0 ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
      LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.b_emit_all_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.1.val)
    (inv := fun s =>
      s.2.1.val ≤ n.val ∧ s.2.2.val ≤ s.2.1.val ∧ s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.val) = some ((bytes input).take s.2.1.val))
  · rintro ⟨out, k, ntok⟩ ⟨hkn, hnt, hlen, hde⟩
    simp only at hkn hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_emit_all_loop.body]
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
        have htok : i7.val = LZ77.mkMatch d.val ch.val := by
          simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i7_post, i4_post, i3_post]
          scalar_tac
        refine ⟨by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show k1.val = k.val + ch.val by scalar_tac]
        exact emit_match input out ntok k.val d.val ch.val i7 hde hntok_lt hd1 hdpos hdmax
          hch3 hch258 hend hmatch htok
      case isFalse hbf =>
        have hposlen : k.val < input.length := by scalar_tac
        step*
        have hval : i2.val = (bytes input)[k.val]! := by
          rw [bytes_getElem! input k.val hposlen, i2_post, Std.U8.cast_U32_val_eq, i1_post]
        refine ⟨by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          show k1.val = k.val + 1 by scalar_tac]
        exact emit_lit input out ntok k.val i2 hde hposlen hntok_lt hval
    case isFalse hge =>
      have hkn' : k.val = input.length := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      rw [hde, hkn']
      simp
  · exact ⟨hk, hntok, rfl, hdec⟩
@[local step]
theorem emit_all_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (plan : Slice Std.U32) (hout : input.length ≤ out.length) :
    slot.b_emit_all input out plan ⦃ fun r =>
      r.1.val ≤ input.length ∧ r.2.length = out.length ∧
      LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.b_emit_all]
  exact emit_all_loop_spec input out plan _ 0#usize 0#usize
    (by simp) hout (by scalar_tac) (by scalar_tac) (by simp [toks, LZ77.decode])
@[local step]
theorem le64_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.b_le64 input p ⦃ fun _ => True ⦄ := U11! slot.b_le64
@[local step]
theorem first_diff_spec (x : Std.U64) (y : Std.U64) :
    slot.b_first_diff x y ⦃ fun _ => True ⦄ := U11! slot.b_first_diff
@[local step]
theorem hash4_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.b_hash4 input p ⦃ fun _ => True ⦄ := U11! slot.b_hash4
@[local step]
theorem hash3_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.b_hash3 input p ⦃ fun _ => True ⦄ := U11! slot.b_hash3
@[local step]
theorem dextra_spec (s : Std.Usize) :
    slot.b_dextra s ⦃ fun _ => True ⦄ := U11! slot.b_dextra
@[local step]
theorem lcode_spec (l : Std.Usize) :
    slot.b_lcode l ⦃ fun r => r.val ≤ 28 ⦄ := by
  rw [slot.b_lcode]
  simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (split <;> try step*))
  all_goals (try split_ifs)
  all_goals first
    | scalar_tac
    | (simp only [core.num.Usize.wrapping_sub_val_eq, UScalar.size, UScalarTy.numBits]
       cases System.Platform.numBits_eq <;> simp_all <;> scalar_tac)
@[local step]
theorem lextra_spec (c : Std.Usize) :
    slot.b_lextra c ⦃ fun _ => True ⦄ := U11! slot.b_lextra
@[local step]
theorem fixed_len_spec (s : Std.Usize) :
    slot.b_fixed_len s ⦃ fun _ => True ⦄ := U10! slot.b_fixed_len
@[local step]
theorem ext_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (lim : Std.Usize) (l : Std.Usize) (it : Std.Usize) :
    slot.b_ext_len_loop input a b lim l it ⦃ fun _ => True ⦄ := by
  rw [slot.b_ext_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 300 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨l1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_ext_len_loop.body, lift]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem ext_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (from0 : Std.Usize) (cap : Std.Usize) :
    slot.b_ext_len input a b from0 cap ⦃ fun _ => True ⦄ := U11! slot.b_ext_len
@[local step]
theorem ext_if_spec (input : Slice Std.U8) (f : Std.Usize) (a : Std.Usize) (b : Std.Usize) (from0 : Std.Usize) (cap : Std.Usize) (dflt : Std.Usize) :
    slot.b_ext_if input f a b from0 cap dflt ⦃ fun _ => True ⦄ := U10! slot.b_ext_if
@[local step]
theorem le64_tail_loop_spec (input : Slice Std.U8) (p : Std.Usize) (x : Std.U64) (j : Std.Usize) :
    slot.b_le64_tail_loop input p x j ⦃ fun _ => True ⦄ := by
  rw [slot.b_le64_tail_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨x1, j1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_le64_tail_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem le64_tail_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.b_le64_tail input p ⦃ fun _ => True ⦄ := U10! slot.b_le64_tail
@[local step]
theorem le64z_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.b_le64z input p ⦃ fun _ => True ⦄ := U10! slot.b_le64z
@[local step]
theorem byte_lt_spec (x : Std.U64) (y : Std.U64) (k : Std.Usize) :
    slot.b_byte_lt x y k ⦃ fun _ => True ⦄ := U11! slot.b_byte_lt
@[local step]
theorem lcp_words_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (lim : Std.Usize) (l : Std.Usize) (it : Std.Usize) (z : Std.U64) (x : Std.U64) :
    slot.b_lcp_words_loop input a b lim l it z x ⦃ fun _ => True ⦄ := by
  rw [slot.b_lcp_words_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 40 - qq9.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨l1, it1, z1, x1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_lcp_words_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem lcp_words_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (l0 : Std.Usize) (lim : Std.Usize) :
    slot.b_lcp_words input a b l0 lim ⦃ fun _ => True ⦄ := U11! slot.b_lcp_words
@[local step]
theorem ext_words_spec (input : Slice Std.U8) (same : Std.Usize) (a : Std.Usize) (b : Std.Usize) (l0 : Std.Usize) (x : Std.U64) (y : Std.U64) (lim : Std.Usize) :
    slot.b_ext_words input same a b l0 x y lim ⦃ fun _ => True ⦄ := U11! slot.b_ext_words
@[local step]
theorem bt_probe_spec (input : Slice Std.U8) (a b l0 : Std.Usize)
    (first : Std.U64) (lim : Std.Usize) :
    slot.b_bt_probe input a b l0 first lim ⦃ fun _ => True ⦄ := by
  rw [slot.b_bt_probe]
  apply spec_ite_cut <;> intro hc <;> step*
  all_goals (repeat (split <;> step*))
  all_goals scalar_tac
@[local step]
theorem bt_walk_loop_spec (input : Slice Std.U8) (child : Array Std.U32 65536#usize) (pos : Std.Usize) (rec : Std.Usize) (maxd : Std.Usize) (mc : alloc.vec.Vec Std.U32) (m0 : Std.Usize) (first : Std.U64) (plt : Std.Usize) (pgt : Std.Usize) (cur : Std.Usize) (ltl : Std.Usize) (gtl : Std.Usize) (len : Std.Usize) (best : Std.Usize) (wl : Std.Usize) (wd : Std.Usize) (depth : Std.Usize) (lim : Std.Usize) (stop : Std.Usize) (kcur : Std.Usize) (kl : Std.Usize) :
    slot.b_bt_walk_loop input child pos rec maxd mc m0 first plt pgt cur ltl gtl len best wl wd depth lim stop kcur kl ⦃ fun _ => True ⦄ := by
  rw [slot.b_bt_walk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => maxd.val - qq9.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨child1, mc1, plt1, pgt1, cur1, ltl1, gtl1, len1, best1, wl1, wd1, depth1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_bt_walk_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem bt_walk_spec (input : Slice Std.U8) (child : Array Std.U32 65536#usize) (root : Std.Usize) (pos : Std.Usize) (cap : Std.Usize) (best0 : Std.Usize) (rec : Std.Usize) (maxd : Std.Usize) (hint : Std.Usize) (mc : alloc.vec.Vec Std.U32) (m0 : Std.Usize) (first : Std.U64) :
    slot.b_bt_walk input child root pos cap best0 rec maxd hint mc m0 first ⦃ fun _ => True ⦄ := U11! slot.b_bt_walk
@[local step]
theorem sks_rec_spec (gap : Std.Usize) :
    slot.b_sks_rec gap ⦃ fun _ => True ⦄ := U11! slot.b_sks_rec
@[local step]
theorem find_pos_spec (input : Slice Std.U8) (h4 : Array Std.U32 65536#usize) (h3 : Array Std.U32 131072#usize) (child : Array Std.U32 65536#usize) (mc : alloc.vec.Vec Std.U32) (st : Array Std.Usize 4#usize) (pos : Std.Usize) (maxd : Std.Usize) :
    slot.b_find_pos input h4 h3 child mc st pos maxd ⦃ fun _ => True ⦄ := U11! slot.b_find_pos
@[local step]
theorem find_all_loop_spec (input : Slice Std.U8) (mstart : alloc.vec.Vec Std.U32) (mc : alloc.vec.Vec Std.U32) (maxd : Std.Usize) (n : Std.Usize) (h4 : Array Std.U32 65536#usize) (h3 : Array Std.U32 131072#usize) (child : Array Std.U32 65536#usize) (st : Array Std.Usize 4#usize) (pos : Std.Usize) :
    slot.b_find_all_loop input mstart mc maxd n h4 h3 child st pos ⦃ fun _ => True ⦄ := by
  rw [slot.b_find_all_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => n.val - qq9.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨mstart1, mc1, h41, h31, child1, st1, pos1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_find_all_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem find_all_spec (input : Slice Std.U8) (mstart : alloc.vec.Vec Std.U32) (mc : alloc.vec.Vec Std.U32) (maxd : Std.Usize) :
    slot.b_find_all input mstart mc maxd ⦃ fun _ => True ⦄ := U11! slot.b_find_all
@[local step]
theorem find_spare_spec (input : Slice Std.U8) (f : Std.Usize) :
    slot.b_find_spare input f ⦃ fun _ => True ⦄ := U10! slot.b_find_spare
@[local step]
theorem bucket_end_spec (l : Std.Usize) :
    slot.b_bucket_end l ⦃ fun _ => True ⦄ := U11! slot.b_bucket_end
@[local step]
theorem build_bend_loop_spec (bend : Array Std.U32 512#usize) (l : Std.Usize) :
    slot.b_build_bend_loop bend l ⦃ fun _ => True ⦄ := by
  rw [slot.b_build_bend_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 259 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨bend1, l1⟩ _
    simp only [slot.b_build_bend_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem build_bend_spec (bend : Array Std.U32 512#usize) :
    slot.b_build_bend bend ⦃ fun _ => True ⦄ := U10! slot.b_build_bend
@[local step]
theorem lg5_spec (w : Std.Usize) :
    slot.b_lg5 w ⦃ fun _ => True ⦄ := U11! slot.b_lg5
@[local step]
theorem load_ct_loop0_spec (tbl : Slice Std.U32) (toff : Std.Usize) (ct : Array Std.U32 1024#usize) (lam : Std.U32) (x : Std.Usize) :
    slot.b_load_ct_loop0 tbl toff ct lam x ⦃ fun _ => True ⦄ := by
  rw [slot.b_load_ct_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 259 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨ct1, x1⟩ _
    simp only [slot.b_load_ct_loop0.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem load_ct_loop1_spec (tbl : Slice Std.U32) (toff : Std.Usize) (ct : Array Std.U32 1024#usize) (s : Std.Usize) :
    slot.b_load_ct_loop1 tbl toff ct s ⦃ fun _ => True ⦄ := by
  rw [slot.b_load_ct_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 30 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨ct1, s1⟩ _
    simp only [slot.b_load_ct_loop1.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem load_ct_loop2_spec (tbl : Slice Std.U32) (toff : Std.Usize) (ct : Array Std.U32 1024#usize) (lam : Std.U32) (c : Std.Usize) :
    slot.b_load_ct_loop2 tbl toff ct lam c ⦃ fun _ => True ⦄ := by
  rw [slot.b_load_ct_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨ct1, c1⟩ _
    simp only [slot.b_load_ct_loop2.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem load_ct_spec (tbl : Slice Std.U32) (toff : Std.Usize) (ct : Array Std.U32 1024#usize) (lam : Std.U32) :
    slot.b_load_ct tbl toff ct lam ⦃ fun _ => True ⦄ := U10! slot.b_load_ct
@[local step]
theorem rm_update_spec (rm : Array Std.U64 4096#usize) (i : Std.Usize) (c : Std.U64) :
    slot.b_rm_update rm i c ⦃ fun _ => True ⦄ := U11! slot.b_rm_update
@[local step]
theorem rm_update3_spec (rm : Array Std.U64 4096#usize) (i : Std.Usize) (c : Std.U64) :
    slot.b_rm_update3 rm i c ⦃ fun _ => True ⦄ := U11! slot.b_rm_update3
@[local step]
theorem rm_upd_spec (f : Std.Usize) (rm : Array Std.U64 4096#usize) (i : Std.Usize) (c : Std.U64) :
    slot.b_rm_upd f rm i c ⦃ fun _ => True ⦄ := U10! slot.b_rm_upd
@[local step]
theorem bkt_val_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (i : Std.Usize) (x : Std.Usize) (e : Std.Usize) (dcs : Std.U64) :
    slot.b_bkt_val rm ct i x e dcs ⦃ fun _ => True ⦄ := U11! slot.b_bkt_val
@[local step]
theorem query_spec (x : Std.Usize) (y : Std.Usize) (k : Std.Usize) (slot0 : Std.Usize) :
    slot.b_query x y k slot0 ⦃ fun _ => True ⦄ := U11! slot.b_query
@[local step]
theorem prune_short_loop_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (i : Std.Usize) (hi : Std.Usize) (dcs : Std.U64) (slot0 : Std.Usize) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) (best : Std.U64) (x : Std.Usize) :
    slot.b_prune_short_loop rm ct i hi dcs slot0 keep items best x ⦃ fun _ => True ⦄ := by
  rw [slot.b_prune_short_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 11 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨items1, best1, x1⟩ _
    simp only [slot.b_prune_short_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem prune_short_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (i : Std.Usize) (lo : Std.Usize) (hi : Std.Usize) (dcs : Std.U64) (slot0 : Std.Usize) (best0 : Std.U64) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) :
    slot.b_prune_short rm ct i lo hi dcs slot0 best0 keep items ⦃ fun _ => True ⦄ := U10! slot.b_prune_short
@[local step]
theorem prune_bkt_loop_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (i : Std.Usize) (hi : Std.Usize) (dcs : Std.U64) (slot0 : Std.Usize) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) (best : Std.U64) (x : Std.Usize) (it : Std.Usize) :
    slot.b_prune_bkt_loop rm ct bend i hi dcs slot0 keep items best x it ⦃ fun _ => True ⦄ := by
  rw [slot.b_prune_bkt_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32 - qq9.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨items1, best1, x1, it1⟩ _
    simp only [slot.b_prune_bkt_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem prune_bkt_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (i : Std.Usize) (lo : Std.Usize) (hi : Std.Usize) (dcs : Std.U64) (slot0 : Std.Usize) (best0 : Std.U64) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) :
    slot.b_prune_bkt rm ct bend i lo hi dcs slot0 best0 keep items ⦃ fun _ => True ⦄ := U10! slot.b_prune_bkt
@[local step]
theorem prune_single_spec (items : alloc.vec.Vec Std.U32) (keep : Std.Usize)
    (best value : Std.U64) (len slot0 : Std.Usize) :
    slot.b_prune_single items keep best value len slot0 ⦃ fun _ => True ⦄ := U11! slot.b_prune_single
@[local step]
theorem prune_pos_loop_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (mc : Slice Std.U32) (me : Std.Usize) (i : Std.Usize) (chw : Std.Usize) (msub : Std.U32) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) (best : Std.U64) (k : Std.Usize) (lo : Std.Usize) :
    slot.b_prune_pos_loop rm ct bend mc me i chw msub keep items best k lo ⦃ fun _ => True ⦄ := by
  rw [slot.b_prune_pos_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => me.val - qq9.2.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨items1, best1, k1, lo1⟩ _
    simp only [slot.b_prune_pos_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem prune_pos_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (mc : Slice Std.U32) (ms : Std.Usize) (me : Std.Usize) (i : Std.Usize) (lit : Std.U64) (chw : Std.Usize) (msub : Std.U32) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) :
    slot.b_prune_pos rm ct bend mc ms me i lit chw msub keep items ⦃ fun _ => True ⦄ := U11! slot.b_prune_pos
@[local step]
theorem relax_short_loop_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (i : Std.Usize) (hi : Std.Usize) (dcs : Std.U64) (best : Std.U64) (x : Std.Usize) :
    slot.b_relax_short_loop rm ct i hi dcs best x ⦃ fun _ => True ⦄ := by
  rw [slot.b_relax_short_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 11 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨best1, x1⟩ _
    simp only [slot.b_relax_short_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem relax_short_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (i : Std.Usize) (lo : Std.Usize) (hi : Std.Usize) (dcs : Std.U64) (best0 : Std.U64) :
    slot.b_relax_short rm ct i lo hi dcs best0 ⦃ fun _ => True ⦄ := U10! slot.b_relax_short
@[local step]
theorem relax_bkt_loop_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (i : Std.Usize) (hi : Std.Usize) (dcs : Std.U64) (best : Std.U64) (x : Std.Usize) (it : Std.Usize) :
    slot.b_relax_bkt_loop rm ct bend i hi dcs best x it ⦃ fun _ => True ⦄ := by
  rw [slot.b_relax_bkt_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨best1, x1, it1⟩ _
    simp only [slot.b_relax_bkt_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem relax_bkt_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (i : Std.Usize) (lo : Std.Usize) (hi : Std.Usize) (dcs : Std.U64) (best0 : Std.U64) :
    slot.b_relax_bkt rm ct bend i lo hi dcs best0 ⦃ fun _ => True ⦄ := U10! slot.b_relax_bkt
@[local step]
theorem relax_pos_loop_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (mc : Slice Std.U32) (me : Std.Usize) (i : Std.Usize) (chw : Std.Usize) (msub : Std.U32) (best : Std.U64) (k : Std.Usize) (lo : Std.Usize) :
    slot.b_relax_pos_loop rm ct bend mc me i chw msub best k lo ⦃ fun _ => True ⦄ := by
  rw [slot.b_relax_pos_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => me.val - qq9.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨best1, k1, lo1⟩ _
    simp only [slot.b_relax_pos_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem relax_pos_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (mc : Slice Std.U32) (ms : Std.Usize) (me : Std.Usize) (i : Std.Usize) (lit : Std.U64) (chw : Std.Usize) (msub : Std.U32) :
    slot.b_relax_pos rm ct bend mc ms me i lit chw msub ⦃ fun _ => True ⦄ := U10! slot.b_relax_pos
@[local step]
theorem prune_or_relax_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (mc : Slice Std.U32) (ms : Std.Usize) (me : Std.Usize) (i : Std.Usize) (lit : Std.U64) (chw : Std.Usize) (msub : Std.U32) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) :
    slot.b_prune_or_relax rm ct bend mc ms me i lit chw msub keep items ⦃ fun _ => True ⦄ := U10! slot.b_prune_or_relax
@[local step]
theorem relax_items_loop_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (items : Slice Std.U32) (e : Std.Usize) (i : Std.Usize) (best : Std.U64) (t : Std.Usize) :
    slot.b_relax_items_loop rm ct items e i best t ⦃ fun _ => True ⦄ := by
  rw [slot.b_relax_items_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => e.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨best1, t1⟩ _
    simp only [slot.b_relax_items_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem relax_items_spec (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (items : Slice Std.U32) (s : Std.Usize) (e : Std.Usize) (i : Std.Usize) (lit : Std.U64) :
    slot.b_relax_items rm ct items s e i lit ⦃ fun _ => True ⦄ := U10! slot.b_relax_items
@[local step]
theorem dp_prune_loop_spec (input : Slice Std.U8) (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (mstart : Slice Std.U32) (mc : Slice Std.U32) (choice : Slice Std.U32) (chw : Std.Usize) (msub : Std.U32) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32) (lo : Std.Usize) (l4 : Std.Usize) (co : Std.Usize) (i : Std.Usize) :
    slot.b_dp_prune_loop input rm ct bend mstart mc choice chw msub keep items istart lo l4 co i ⦃ fun _ => True ⦄ := by
  rw [slot.b_dp_prune_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨rm1, choice1, items1, istart1, i1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_dp_prune_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem dp_prune_spec (input : Slice Std.U8) (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (bend : Array Std.U32 512#usize) (mstart : Slice Std.U32) (mc : Slice Std.U32) (choice : Slice Std.U32) (chw : Std.Usize) (msub : Std.U32) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32) (lo : Std.Usize) (hi : Std.Usize) (l4 : Std.Usize) (co : Std.Usize) :
    slot.b_dp_prune input rm ct bend mstart mc choice chw msub keep items istart lo hi l4 co ⦃ fun _ => True ⦄ := U10! slot.b_dp_prune
@[local step]
theorem blk_lo_spec (bpos : Slice Std.U32) (b : Std.Usize) (hi : Std.Usize) :
    slot.b_blk_lo bpos b hi ⦃ fun _ => True ⦄ := U11! slot.b_blk_lo
@[local step]
theorem pass_prune_loop_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (tbl : Slice Std.U32) (bend : Array Std.U32 512#usize) (bpos : Slice Std.U32) (nb : Std.Usize) (choice : Slice Std.U32) (chw : Std.Usize) (msub : Std.U32) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32) (co : Std.Usize) (lam : Std.U32) (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (hi : Std.Usize) (k : Std.Usize) :
    slot.b_pass_prune_loop input mstart mc tbl bend bpos nb choice chw msub keep items istart co lam rm ct hi k ⦃ fun _ => True ⦄ := by
  rw [slot.b_pass_prune_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => nb.val - qq9.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨choice1, items1, istart1, rm1, ct1, hi1, k1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_pass_prune_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem pass_prune_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (tbl : Slice Std.U32) (bend : Array Std.U32 512#usize) (bpos : Slice Std.U32) (nb : Std.Usize) (choice : Slice Std.U32) (chw : Std.Usize) (msub : Std.U32) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32) (co : Std.Usize) (lam : Std.U32) :
    slot.b_pass_prune input mstart mc tbl bend bpos nb choice chw msub keep items istart co lam ⦃ fun _ => True ⦄ := U11! slot.b_pass_prune
@[local step]
theorem dp_items_safe_loop_spec (input : Slice Std.U8) (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (choice : Slice Std.U32) (items : Slice Std.U32) (istart : Slice Std.U32) (lo : Std.Usize) (l4 : Std.Usize) (co : Std.Usize) (n : Std.Usize) (e : Std.Usize) (i : Std.Usize) :
    slot.b_dp_items_safe_loop input rm ct choice items istart lo l4 co n e i ⦃ fun _ => True ⦄ := by
  rw [slot.b_dp_items_safe_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => qq9.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨rm1, choice1, e1, i1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_dp_items_safe_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem dp_items_safe_spec (input : Slice Std.U8) (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (choice : Slice Std.U32) (items : Slice Std.U32) (istart : Slice Std.U32) (lo : Std.Usize) (hi : Std.Usize) (l4 : Std.Usize) (co : Std.Usize) :
    slot.b_dp_items_safe input rm ct choice items istart lo hi l4 co ⦃ fun _ => True ⦄ := U11! slot.b_dp_items_safe
@[local step]
theorem dp_items_loop_spec (input : Slice Std.U8) (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (choice : Slice Std.U32) (items : Slice Std.U32) (istart : Slice Std.U32) (lo : Std.Usize) (l4 : Std.Usize) (co : Std.Usize) (n : Std.Usize) (e : Std.Usize) (i : Std.Usize)
    (hn : n.val = input.length) (hlo : lo.val ≤ n.val)
    (hs : n.val - lo.val < istart.length)
    (hi : i.val ≤ input.length) (hc : co.val + i.val ≤ choice.length) :
    slot.b_dp_items_loop input rm ct choice items istart lo l4 co n e i ⦃ fun _ => True ⦄ := by
  rw [slot.b_dp_items_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => qq9.2.2.2.val)
    (inv := fun s => s.2.2.2.val ≤ input.length ∧ co.val + s.2.2.2.val ≤ s.2.1.length)
  · rintro ⟨rm1, choice1, e1, i1⟩ ⟨hi1, hc1⟩
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_dp_items_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · exact ⟨hi, hc⟩
@[local step]
theorem dp_items_spec (input : Slice Std.U8) (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (choice : Slice Std.U32) (items : Slice Std.U32) (istart : Slice Std.U32) (lo : Std.Usize) (hi : Std.Usize) (l4 : Std.Usize) (co : Std.Usize) :
    slot.b_dp_items input rm ct choice items istart lo hi l4 co ⦃ fun _ => True ⦄ := U11! slot.b_dp_items
@[local step]
theorem pass_items_loop_spec (input : Slice Std.U8) (tbl : Slice Std.U32) (bpos : Slice Std.U32) (nb : Std.Usize) (choice : Slice Std.U32) (items : Slice Std.U32) (istart : Slice Std.U32) (l4 : Std.Usize) (co : Std.Usize) (lam : Std.U32) (rm : Array Std.U64 4096#usize) (ct : Array Std.U32 1024#usize) (hi : Std.Usize) (k : Std.Usize) :
    slot.b_pass_items_loop input tbl bpos nb choice items istart l4 co lam rm ct hi k ⦃ fun _ => True ⦄ := by
  rw [slot.b_pass_items_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => nb.val - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨choice1, rm1, ct1, hi1, k1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_pass_items_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem pass_items_spec (input : Slice Std.U8) (tbl : Slice Std.U32) (bpos : Slice Std.U32) (nb : Std.Usize) (choice : Slice Std.U32) (items : Slice Std.U32) (istart : Slice Std.U32) (l4 : Std.Usize) (co : Std.Usize) (lam : Std.U32) :
    slot.b_pass_items input tbl bpos nb choice items istart l4 co lam ⦃ fun _ => True ⦄ := U11! slot.b_pass_items
@[local step]
theorem find_dist_loop_spec (mc : Slice Std.U32) (l : Std.Usize) (me : Std.Usize) (d : Std.Usize) (k : Std.Usize) :
    slot.b_find_dist_loop mc l me d k ⦃ fun _ => True ⦄ := by
  rw [slot.b_find_dist_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => me.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨d1, k1⟩ _
    simp only [slot.b_find_dist_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem find_dist_spec (mstart : Slice Std.U32) (mc : Slice Std.U32) (p : Std.Usize) (l : Std.Usize) :
    slot.b_find_dist mstart mc p l ⦃ fun _ => True ⦄ := U11! slot.b_find_dist
@[local step]
theorem clear_loop_spec (v : Slice Std.U32) (b : Std.Usize) (i : Std.Usize) :
    slot.b_clear_loop v b i ⦃ fun _ => True ⦄ := by
  rw [slot.b_clear_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => b.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨v1, i1⟩ _
    simp only [slot.b_clear_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem clear_spec (v : Slice Std.U32) (a : Std.Usize) (b : Std.Usize) :
    slot.b_clear v a b ⦃ fun _ => True ⦄ := U10! slot.b_clear
@[local step]
theorem dist_of_spec (mstart : Slice Std.U32) (mc : Slice Std.U32) (pos : Std.Usize) (len : Std.Usize) (d0 : Std.Usize) :
    slot.b_dist_of mstart mc pos len d0 ⦃ fun _ => True ⦄ := U10! slot.b_dist_of
@[local step]
theorem walk_bump_spec (fr : Slice Std.U32) (off : Std.Usize) (st : Std.Usize) (d : Std.Usize) (b : Std.Usize) :
    slot.b_walk_bump fr off st d b ⦃ fun _ => True ⦄ := U11! slot.b_walk_bump
@[local step]
theorem walk_loop_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (choice : Slice Std.U32) (co : Std.Usize) (fr : Slice Std.U32) (bpos : Slice Std.U32) (n : Std.Usize) (pos : Std.Usize) (b : Std.Usize) (t : Std.Usize) :
    slot.b_walk_loop input mstart mc choice co fr bpos n pos b t ⦃ fun _ => True ⦄ := by
  rw [slot.b_walk_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => n.val - qq9.2.2.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨choice1, fr1, bpos1, pos1, b1, t1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_walk_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem walk_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (choice : Slice Std.U32) (co : Std.Usize) (fr : Slice Std.U32) (bpos : Slice Std.U32) :
    slot.b_walk input mstart mc choice co fr bpos ⦃ fun _ => True ⦄ := U11! slot.b_walk
@[local step]
theorem insert_sorted_loop_spec (order : Slice Std.U32) (freq : Slice Std.U32) (off : Std.Usize) (fs : Std.U32) (j : Std.Usize) :
    slot.b_insert_sorted_loop order freq off fs j ⦃ fun _ => True ⦄ := by
  rw [slot.b_insert_sorted_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨order1, j1⟩ _
    simp only [slot.b_insert_sorted_loop.body, lift]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem insert_sorted_spec (order : Slice Std.U32) (k : Std.Usize) (s : Std.Usize) (freq : Slice Std.U32) (off : Std.Usize) :
    slot.b_insert_sorted order k s freq off ⦃ fun _ => True ⦄ := U11! slot.b_insert_sorted
set_option hygiene false in
local notation "U14!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨cnt1, i1⟩ _
    simp only [q1__, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem radix_pass_loop0_spec (freq : Slice Std.U32) (off : Std.Usize) (src : Slice Std.U32) (k : Std.Usize) (sh : Std.U32) (cnt : Array Std.U32 256#usize) (i : Std.Usize) :
    slot.b_radix_pass_loop0 freq off src k sh cnt i ⦃ fun _ => True ⦄ := U14! slot.b_radix_pass_loop0 slot.b_radix_pass_loop0.body
@[local step]
theorem radix_pass_loop1_spec (cnt : Array Std.U32 256#usize) (acc : Std.U32) (d : Std.Usize) :
    slot.b_radix_pass_loop1 cnt acc d ⦃ fun _ => True ⦄ := by
  rw [slot.b_radix_pass_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨cnt1, acc1, d1⟩ _
    simp only [slot.b_radix_pass_loop1.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem radix_pass_loop2_spec (freq : Slice Std.U32) (off : Std.Usize) (src : Slice Std.U32) (dst : Slice Std.U32) (k : Std.Usize) (sh : Std.U32) (cnt : Array Std.U32 256#usize) (j : Std.Usize) :
    slot.b_radix_pass_loop2 freq off src dst k sh cnt j ⦃ fun _ => True ⦄ := by
  rw [slot.b_radix_pass_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨dst1, cnt1, j1⟩ _
    simp only [slot.b_radix_pass_loop2.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem radix_pass_spec (freq : Slice Std.U32) (off : Std.Usize) (src : Slice Std.U32) (dst : Slice Std.U32) (k : Std.Usize) (sh : Std.U32) :
    slot.b_radix_pass freq off src dst k sh ⦃ fun _ => True ⦄ := U10! slot.b_radix_pass
@[local step]
theorem copy32_loop_spec (src : Slice Std.U32) (soff : Std.Usize) (dst : Slice Std.U32) (doff : Std.Usize) (m : Std.Usize) (i : Std.Usize) :
    slot.b_copy32_loop src soff dst doff m i ⦃ fun _ => True ⦄ := by
  rw [slot.b_copy32_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => m.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨dst1, i1⟩ _
    simp only [slot.b_copy32_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem copy32_spec (src : Slice Std.U32) (soff : Std.Usize) (dst : Slice Std.U32) (doff : Std.Usize) (m : Std.Usize) :
    slot.b_copy32 src soff dst doff m ⦃ fun _ => True ⦄ := U10! slot.b_copy32
@[local step]
theorem sort_live_loop0_spec (freq : Slice Std.U32) (off : Std.Usize) (nsym : Std.Usize) (tmp : Array Std.U32 288#usize) (k : Std.Usize) (big : Std.Usize) (s : Std.Usize) :
    slot.b_sort_live_loop0 freq off nsym tmp k big s ⦃ fun _ => True ⦄ := by
  rw [slot.b_sort_live_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨tmp1, k1, big1, s1⟩ _
    simp only [slot.b_sort_live_loop0.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem sort_live_loop1_spec (freq : Slice Std.U32) (off : Std.Usize) (order : Slice Std.U32) (tmp : Array Std.U32 288#usize) (kb : Std.Usize) (j : Std.Usize) :
    slot.b_sort_live_loop1 freq off order tmp kb j ⦃ fun _ => True ⦄ := by
  rw [slot.b_sort_live_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨order1, j1⟩ _
    simp only [slot.b_sort_live_loop1.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem sort_live_spec (freq : Slice Std.U32) (off : Std.Usize) (nsym : Std.Usize) (order : Slice Std.U32) :
    slot.b_sort_live freq off nsym order ⦃ fun _ => True ⦄ := U10! slot.b_sort_live
@[local step]
theorem load_w_loop_spec (freq : Slice Std.U32) (off : Std.Usize) (order : Slice Std.U32) (k : Std.Usize) (wa : Slice Std.U64) (i : Std.Usize) :
    slot.b_load_w_loop freq off order k wa i ⦃ fun _ => True ⦄ := by
  rw [slot.b_load_w_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨wa1, i1⟩ _
    simp only [slot.b_load_w_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem load_w_spec (freq : Slice Std.U32) (off : Std.Usize) (order : Slice Std.U32) (k : Std.Usize) (wa : Slice Std.U64) :
    slot.b_load_w freq off order k wa ⦃ fun _ => True ⦄ := U10! slot.b_load_w
@[local step]
theorem pm_level_loop_spec (lw : Array Std.U64 288#usize) (k : Std.Usize) (w : Array Std.U64 1152#usize) (src : Std.Usize) (dst : Std.Usize) (flags : Array Std.U8 9216#usize) (foff : Std.Usize) (npk : Std.Usize) (total : Std.Usize) (a : Std.Usize) (p : Std.Usize) (t : Std.Usize) :
    slot.b_pm_level_loop lw k w src dst flags foff npk total a p t ⦃ fun _ => True ⦄ := by
  rw [slot.b_pm_level_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 576 - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨w1, flags1, a1, p1, t1⟩ _
    simp only [slot.b_pm_level_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem pm_level_spec (lw : Array Std.U64 288#usize) (k : Std.Usize) (w : Array Std.U64 1152#usize) (src : Std.Usize) (curlen : Std.Usize) (dst : Std.Usize) (flags : Array Std.U8 9216#usize) (foff : Std.Usize) :
    slot.b_pm_level lw k w src curlen dst flags foff ⦃ fun _ => True ⦄ := U11! slot.b_pm_level
@[local step]
theorem pm_levels_loop_spec (lw : Array Std.U64 288#usize) (k : Std.Usize) (w : Array Std.U64 1152#usize) (flags : Array Std.U8 9216#usize) (maxbits : Std.Usize) (curlen : Std.Usize) (lev : Std.Usize) :
    slot.b_pm_levels_loop lw k w flags maxbits curlen lev ⦃ fun _ => True ⦄ := by
  rw [slot.b_pm_levels_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 16 - qq9.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨w1, flags1, curlen1, lev1⟩ _
    simp only [slot.b_pm_levels_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem pm_levels_spec (lw : Array Std.U64 288#usize) (k : Std.Usize) (w : Array Std.U64 1152#usize) (flags : Array Std.U8 9216#usize) (maxbits : Std.Usize) :
    slot.b_pm_levels lw k w flags maxbits ⦃ fun _ => True ⦄ := U10! slot.b_pm_levels
@[local step]
theorem count_leaves_loop_spec (flags : Slice Std.U8) (foff : Std.Usize) (s : Std.Usize) (c : Std.Usize) (i : Std.Usize) :
    slot.b_count_leaves_loop flags foff s c i ⦃ fun _ => True ⦄ := by
  rw [slot.b_count_leaves_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 576 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨c1, i1⟩ _
    simp only [slot.b_count_leaves_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem count_leaves_spec (flags : Slice Std.U8) (foff : Std.Usize) (s : Std.Usize) :
    slot.b_count_leaves flags foff s ⦃ fun _ => True ⦄ := U10! slot.b_count_leaves
@[local step]
theorem inc_prefix_loop_spec (cnt : Slice Std.U32) (m : Std.Usize) (i : Std.Usize) :
    slot.b_inc_prefix_loop cnt m i ⦃ fun _ => True ⦄ := U14! slot.b_inc_prefix_loop slot.b_inc_prefix_loop.body
@[local step]
theorem inc_prefix_spec (cnt : Slice Std.U32) (m : Std.Usize) :
    slot.b_inc_prefix cnt m ⦃ fun _ => True ⦄ := U10! slot.b_inc_prefix
@[local step]
theorem count_back_loop_spec (flags : Slice Std.U8) (cnt : Slice Std.U32) (s : Std.Usize) (lv : Std.Usize) :
    slot.b_count_back_loop flags cnt s lv ⦃ fun _ => True ⦄ := by
  rw [slot.b_count_back_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨cnt1, s1, lv1⟩ _
    simp only [slot.b_count_back_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem count_back_spec (flags : Slice Std.U8) (cnt : Slice Std.U32) (k : Std.Usize) (maxbits : Std.Usize) :
    slot.b_count_back flags cnt k maxbits ⦃ fun _ => True ⦄ := U11! slot.b_count_back
@[local step]
theorem assign_lens_loop_spec (order : Slice Std.U32) (cnt : Slice Std.U32) (k : Std.Usize) (lens : Slice Std.U32) (loff : Std.Usize) (r : Std.Usize) :
    slot.b_assign_lens_loop order cnt k lens loff r ⦃ fun _ => True ⦄ := by
  rw [slot.b_assign_lens_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨lens1, r1⟩ _
    simp only [slot.b_assign_lens_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem assign_lens_spec (order : Slice Std.U32) (cnt : Slice Std.U32) (k : Std.Usize) (lens : Slice Std.U32) (loff : Std.Usize) :
    slot.b_assign_lens order cnt k lens loff ⦃ fun _ => True ⦄ := U10! slot.b_assign_lens
@[local step]
theorem pkg_merge_pm_spec (freq : Slice Std.U32) (off : Std.Usize) (nsym : Std.Usize) (maxbits : Std.Usize) (lens : Slice Std.U32) (loff : Std.Usize) :
    slot.b_pkg_merge_pm freq off nsym maxbits lens loff ⦃ fun _ => True ⦄ := U10! slot.b_pkg_merge_pm
@[local step]
theorem pkg_merge_loop0_spec (freq : Slice Std.U32) (off : Std.Usize) (order : Array Std.U32 288#usize) (k : Std.Usize) (weights : Array Std.U64 576#usize) (i : Std.Usize) :
    slot.b_pkg_merge_loop0 freq off order k weights i ⦃ fun _ => True ⦄ := by
  rw [slot.b_pkg_merge_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨weights1, i1⟩ _
    simp only [slot.b_pkg_merge_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem pkg_merge_loop1_loop0_spec (k : Std.Usize) (weights : Array Std.U64 576#usize) (parent : Array Std.U32 576#usize) (leaf : Std.Usize) (pair : Std.Usize) (next : Std.Usize) (sum : Std.U64) (j : Std.Usize) :
    slot.b_pkg_merge_loop1_loop0 k weights parent leaf pair next sum j ⦃ fun _ => True ⦄ := by
  rw [slot.b_pkg_merge_loop1_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 2 - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨parent1, leaf1, pair1, sum1, j1⟩ _
    simp only [slot.b_pkg_merge_loop1_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem pkg_merge_loop1_spec (k : Std.Usize) (weights : Array Std.U64 576#usize) (parent : Array Std.U32 576#usize) (leaf : Std.Usize) (pair : Std.Usize) (next : Std.Usize) :
    slot.b_pkg_merge_loop1 k weights parent leaf pair next ⦃ fun _ => True ⦄ := by
  rw [slot.b_pkg_merge_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 575 - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨weights1, parent1, leaf1, pair1, next1⟩ _
    simp only [slot.b_pkg_merge_loop1.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem pkg_merge_loop2_spec (parent : Array Std.U32 576#usize) (depth : Array Std.U32 576#usize) (mx : Std.Usize) (node : Std.Usize) :
    slot.b_pkg_merge_loop2 parent depth mx node ⦃ fun _ => True ⦄ := by
  rw [slot.b_pkg_merge_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨depth1, mx1, node1⟩ _
    simp only [slot.b_pkg_merge_loop2.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem pkg_merge_loop3_spec (lens : Slice Std.U32) (loff : Std.Usize) (order : Array Std.U32 288#usize) (k : Std.Usize) (depth : Array Std.U32 576#usize) (r : Std.Usize) :
    slot.b_pkg_merge_loop3 lens loff order k depth r ⦃ fun _ => True ⦄ := by
  rw [slot.b_pkg_merge_loop3]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨lens1, r1⟩ _
    simp only [slot.b_pkg_merge_loop3.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem pkg_merge_spec (freq : Slice Std.U32) (off : Std.Usize) (nsym : Std.Usize) (maxbits : Std.Usize) (lens : Slice Std.U32) (loff : Std.Usize) :
    slot.b_pkg_merge freq off nsym maxbits lens loff ⦃ fun _ => True ⦄ := by
  rw [slot.b_pkg_merge]
  step*
  simp only [lift, bind_tc_ok]
  step*
  all_goals (repeat (split <;> try step*))
  all_goals scalar_tac
@[local step]
theorem run_len_loop_spec (all : Slice Std.U32) (i : Std.Usize) (m : Std.Usize) (v : Std.U32) (r : Std.Usize) :
    slot.b_run_len_loop all i m v r ⦃ fun _ => True ⦄ := by
  rw [slot.b_run_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 1000 - qq9.val)
    (inv := fun _ => True)
  · rintro r1 _
    simp only [slot.b_run_len_loop.body, lift]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem run_len_spec (all : Slice Std.U32) (i : Std.Usize) (m : Std.Usize) :
    slot.b_run_len all i m ⦃ fun _ => True ⦄ := U10! slot.b_run_len
@[local step]
theorem rle_stats_loop_spec (all : Slice Std.U32) (m : Std.Usize) (clf : Slice Std.U32) (extra : Std.U64) (i : Std.Usize) :
    slot.b_rle_stats_loop all m clf extra i ⦃ fun _ => True ⦄ := by
  rw [slot.b_rle_stats_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => m.val - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨clf1, extra1, i1⟩ _
    simp only [slot.b_rle_stats_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem rle_stats_spec (all : Slice Std.U32) (m : Std.Usize) (clf : Slice Std.U32) :
    slot.b_rle_stats all m clf ⦃ fun _ => True ⦄ := U10! slot.b_rle_stats
@[local step]
theorem dot_loop_spec (f : Slice Std.U32) (foff : Std.Usize) (l : Slice Std.U32) (loff : Std.Usize) (m : Std.Usize) (s : Std.U64) (i : Std.Usize) :
    slot.b_dot_loop f foff l loff m s i ⦃ fun _ => True ⦄ := by
  rw [slot.b_dot_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => m.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨s1, i1⟩ _
    simp only [slot.b_dot_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem dot_spec (f : Slice Std.U32) (foff : Std.Usize) (l : Slice Std.U32) (loff : Std.Usize) (m : Std.Usize) :
    slot.b_dot f foff l loff m ⦃ fun _ => True ⦄ := U10! slot.b_dot
@[local step]
theorem fixed_dot_loop_spec (f : Slice Std.U32) (foff : Std.Usize) (s : Std.U64) (i : Std.Usize) :
    slot.b_fixed_dot_loop f foff s i ⦃ fun _ => True ⦄ := by
  rw [slot.b_fixed_dot_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 288 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨s1, i1⟩ _
    simp only [slot.b_fixed_dot_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem fixed_dot_spec (f : Slice Std.U32) (foff : Std.Usize) :
    slot.b_fixed_dot f foff ⦃ fun _ => True ⦄ := U10! slot.b_fixed_dot
@[local step]
theorem sum_range_loop_spec (f : Slice Std.U32) (b : Std.Usize) (s : Std.U64) (i : Std.Usize) :
    slot.b_sum_range_loop f b s i ⦃ fun _ => True ⦄ := by
  rw [slot.b_sum_range_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => b.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨s1, i1⟩ _
    simp only [slot.b_sum_range_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem sum_range_spec (f : Slice Std.U32) (a : Std.Usize) (b : Std.Usize) :
    slot.b_sum_range f a b ⦃ fun _ => True ⦄ := U10! slot.b_sum_range
@[local step]
theorem last_nz_loop_spec (l : Slice Std.U32) (off : Std.Usize) (lo : Std.Usize) (k : Std.Usize) :
    slot.b_last_nz_loop l off lo k ⦃ fun _ => True ⦄ := by
  rw [slot.b_last_nz_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => qq9.val)
    (inv := fun _ => True)
  · rintro k1 _
    simp only [slot.b_last_nz_loop.body, lift]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem last_nz_spec (l : Slice Std.U32) (off : Std.Usize) (m : Std.Usize) (lo : Std.Usize) :
    slot.b_last_nz l off m lo ⦃ fun _ => True ⦄ := U10! slot.b_last_nz
@[local step]
theorem hclen_of_loop_spec (cl : Slice Std.U32) (h : Std.Usize) :
    slot.b_hclen_of_loop cl h ⦃ fun _ => True ⦄ := by
  rw [slot.b_hclen_of_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => qq9.val)
    (inv := fun _ => True)
  · rintro h1 _
    simp only [slot.b_hclen_of_loop.body, lift]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem hclen_of_spec (cl : Slice Std.U32) :
    slot.b_hclen_of cl ⦃ fun _ => True ⦄ := U10! slot.b_hclen_of
@[local step]
theorem block_bits_spec (fr : Slice Std.U32) (off : Std.Usize) (lens : Slice Std.U32) :
    slot.b_block_bits fr off lens ⦃ fun _ => True ⦄ := U10! slot.b_block_bits
@[local step]
theorem log2x16_spec (x : Std.U64) :
    slot.b_log2x16 x ⦃ fun _ => True ⦄ := U11! slot.b_log2x16
set_option hygiene false in
local notation "U15!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 318 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨sc1, s1⟩ _
    simp only [q1__, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem sym_costs_loop_spec (fr : Slice Std.U32) (off : Std.Usize) (lens : Slice Std.U32) (kind : Std.U32) (sc : Slice Std.U32) (lt1 : Std.U32) (ld : Std.U32) (s : Std.Usize) :
    slot.b_sym_costs_loop fr off lens kind sc lt1 ld s ⦃ fun _ => True ⦄ := U15! slot.b_sym_costs_loop slot.b_sym_costs_loop.body
@[local step]
theorem sym_costs_spec (fr : Slice Std.U32) (off : Std.Usize) (lens : Slice Std.U32) (kind : Std.U32) (sc : Slice Std.U32) :
    slot.b_sym_costs fr off lens kind sc ⦃ fun _ => True ⦄ := U11! slot.b_sym_costs
@[local step]
theorem blend_spec (old : Std.U32) (new : Std.U32) (damp : Std.U32) :
    slot.b_blend old new damp ⦃ fun _ => True ⦄ := U11! slot.b_blend
set_option hygiene false in
local notation "U16!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, c1⟩ _
    simp only [q1__, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem fill_table_loop0_spec (sc : Slice Std.U32) (tbl : Slice Std.U32) (toff : Std.Usize) (damp : Std.U32) (c : Std.Usize) :
    slot.b_fill_table_loop0 sc tbl toff damp c ⦃ fun _ => True ⦄ := U16! slot.b_fill_table_loop0 slot.b_fill_table_loop0.body
set_option hygiene false in
local notation "U17!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 259 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, len1⟩ _
    simp only [q1__, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem fill_table_loop1_spec (sc : Slice Std.U32) (tbl : Slice Std.U32) (toff : Std.Usize) (damp : Std.U32) (len : Std.Usize) :
    slot.b_fill_table_loop1 sc tbl toff damp len ⦃ fun _ => True ⦄ := U17! slot.b_fill_table_loop1 slot.b_fill_table_loop1.body
set_option hygiene false in
local notation "U18!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 30 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, s1⟩ _
    simp only [q1__, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem fill_table_loop2_spec (sc : Slice Std.U32) (tbl : Slice Std.U32) (toff : Std.Usize) (damp : Std.U32) (s : Std.Usize) :
    slot.b_fill_table_loop2 sc tbl toff damp s ⦃ fun _ => True ⦄ := U18! slot.b_fill_table_loop2 slot.b_fill_table_loop2.body
@[local step]
theorem fill_table_spec (sc : Slice Std.U32) (tbl : Slice Std.U32) (toff : Std.Usize) (damp : Std.U32) :
    slot.b_fill_table sc tbl toff damp ⦃ fun _ => True ⦄ := U10! slot.b_fill_table
@[local step]
theorem longest_spec (mstart : Slice Std.U32) (mc : Slice Std.U32) (p : Std.Usize) :
    slot.b_longest mstart mc p ⦃ fun _ => True ⦄ := U11! slot.b_longest
@[local step]
theorem block_hist_loop_spec (input : Slice Std.U8) (b : Std.Usize) (fr : Slice Std.U32) (i : Std.Usize) :
    slot.b_block_hist_loop input b fr i ⦃ fun _ => True ⦄ := by
  rw [slot.b_block_hist_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => b.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨fr1, i1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_block_hist_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem block_hist_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (fr : Slice Std.U32) :
    slot.b_block_hist input a b fr ⦃ fun _ => True ⦄ := U10! slot.b_block_hist
@[local step]
theorem add_hist_loop_spec (fr : Slice Std.U32) (hist : Array Std.U32 256#usize) (c : Std.Usize) :
    slot.b_add_hist_loop fr hist c ⦃ fun _ => True ⦄ := by
  rw [slot.b_add_hist_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨hist1, c1⟩ _
    simp only [slot.b_add_hist_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem add_hist_spec (fr : Slice Std.U32) (hist : Array Std.U32 256#usize) :
    slot.b_add_hist fr hist ⦃ fun _ => True ⦄ := U10! slot.b_add_hist
@[local step]
theorem block_bits_if_spec (fr : Slice Std.U32) (lens : Slice Std.U32) (f : Std.Usize) :
    slot.b_block_bits_if fr lens f ⦃ fun _ => True ⦄ := U10! slot.b_block_bits_if
@[local step]
theorem st5len_spec (len : Std.Usize) :
    slot.b_st5len len ⦃ fun _ => True ⦄ := U11! slot.b_st5len
@[local step]
theorem ent5_spec (lt1 : Std.U32) (f : Std.U64) :
    slot.b_ent5 lt1 f ⦃ fun _ => True ⦄ := U10! slot.b_ent5
@[local step]
theorem init5_table_loop0_spec (fr : Slice Std.U32) (tbl : Slice Std.U32) (toff : Std.Usize) (lt1 : Std.U32) (c : Std.Usize) :
    slot.b_init5_table_loop0 fr tbl toff lt1 c ⦃ fun _ => True ⦄ := U16! slot.b_init5_table_loop0 slot.b_init5_table_loop0.body
@[local step]
theorem init5_table_loop1_spec (tbl : Slice Std.U32) (toff : Std.Usize) (len : Std.Usize) :
    slot.b_init5_table_loop1 tbl toff len ⦃ fun _ => True ⦄ := U17! slot.b_init5_table_loop1 slot.b_init5_table_loop1.body
@[local step]
theorem init5_table_loop2_spec (tbl : Slice Std.U32) (toff : Std.Usize) (s : Std.Usize) :
    slot.b_init5_table_loop2 tbl toff s ⦃ fun _ => True ⦄ := U18! slot.b_init5_table_loop2 slot.b_init5_table_loop2.body
@[local step]
theorem init5_table_spec (fr : Slice Std.U32) (tbl : Slice Std.U32) (toff : Std.Usize) :
    slot.b_init5_table fr tbl toff ⦃ fun _ => True ⦄ := U11! slot.b_init5_table
@[local step]
theorem literal_bits_loop_spec (input : Slice Std.U8) (fr : Slice Std.U32) (hist : Array Std.U32 256#usize) (tlit : Slice Std.U32) (t5 : Slice Std.U32) (n : Std.Usize) (lens : Array Std.U32 320#usize) (sc : Array Std.U32 320#usize) (total : Std.U64) (nblk : Std.Usize) (b : Std.Usize) :
    slot.b_literal_bits_loop input fr hist tlit t5 n lens sc total nblk b ⦃ fun _ => True ⦄ := by
  rw [slot.b_literal_bits_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => nblk.val - qq9.2.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨fr1, hist1, tlit1, t51, lens1, sc1, total1, b1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_literal_bits_loop.body, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem literal_bits_spec (input : Slice Std.U8) (fr : Slice Std.U32) (hist : Array Std.U32 256#usize) (tlit : Slice Std.U32) (t5 : Slice Std.U32) :
    slot.b_literal_bits input fr hist tlit t5 ⦃ fun _ => True ⦄ := U10! slot.b_literal_bits
@[local step]
theorem avg_lit16_h_spec (hist : Array Std.U32 256#usize) (n : Std.Usize) :
    slot.b_avg_lit16_h hist n ⦃ fun _ => True ⦄ := U10! slot.b_avg_lit16_h
@[local step]
theorem est_match16_spec (l : Std.Usize) (d : Std.Usize) :
    slot.b_est_match16 l d ⦃ fun _ => True ⦄ := U11! slot.b_est_match16
@[local step]
theorem est_if_spec (f : Std.Usize) (l : Std.Usize) (d : Std.Usize) :
    slot.b_est_if f l d ⦃ fun _ => True ⦄ := U10! slot.b_est_if
@[local step]
theorem next_longest_spec (mstart : Slice Std.U32) (mc : Slice Std.U32) (pos : Std.Usize) (st : Std.Usize) (b : Std.Usize) :
    slot.b_next_longest mstart mc pos st b ⦃ fun _ => True ⦄ := U11! slot.b_next_longest
@[local step]
theorem lazy_cost_init_loop_spec (mstart : Slice Std.U32) (mc : Slice Std.U32) (h16 : Std.U32) (choice : Slice Std.U32) (n : Std.Usize) (pos : Std.Usize) (nxt : Std.Usize) (ec : Std.U32) (hv : Std.Usize) :
    slot.b_lazy_cost_init_loop mstart mc h16 choice n pos nxt ec hv ⦃ fun _ => True ⦄ := by
  rw [slot.b_lazy_cost_init_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => n.val - qq9.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨choice1, pos1, nxt1, ec1, hv1⟩ _
    simp only [slot.b_lazy_cost_init_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem lazy_cost_init_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (h16 : Std.U32) (choice : Slice Std.U32) :
    slot.b_lazy_cost_init input mstart mc h16 choice ⦃ fun _ => True ⦄ := U10! slot.b_lazy_cost_init
@[local step]
theorem forbid_block_loop_spec (tbl : Slice Std.U32) (toff : Std.Usize) (len : Std.Usize) :
    slot.b_forbid_block_loop tbl toff len ⦃ fun _ => True ⦄ := U17! slot.b_forbid_block_loop slot.b_forbid_block_loop.body
@[local step]
theorem forbid_block_spec (tbl : Slice Std.U32) (toff : Std.Usize) :
    slot.b_forbid_block tbl toff ⦃ fun _ => True ⦄ := U10! slot.b_forbid_block
@[local step]
theorem forbid_if_spec (tbl : Slice Std.U32) (toff : Std.Usize) (f : Std.Usize) :
    slot.b_forbid_if tbl toff f ⦃ fun _ => True ⦄ := U10! slot.b_forbid_if
set_option hygiene false in
local notation "U19!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => lim.val - qq9.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨fr1, tbl1, lens1, sc1, total1, b1⟩ _
    simp only [q1__, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial)
@[local step]
theorem eval_blocks_loop_spec (fr : Slice Std.U32) (tbl : Slice Std.U32) (damp : Std.U32) (lens : Array Std.U32 320#usize) (sc : Array Std.U32 320#usize) (total : Std.U64) (lim : Std.Usize) (b : Std.Usize) :
    slot.b_eval_blocks_loop fr tbl damp lens sc total lim b ⦃ fun _ => True ⦄ := U19! slot.b_eval_blocks_loop slot.b_eval_blocks_loop.body
@[local step]
theorem eval_blocks_spec (fr : Slice Std.U32) (tbl : Slice Std.U32) (nb2 : Std.Usize) (nbmax : Std.Usize) (damp : Std.U32) :
    slot.b_eval_blocks fr tbl nb2 nbmax damp ⦃ fun _ => True ⦄ := U10! slot.b_eval_blocks
@[local step]
theorem dp_pass_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (tbl : Slice Std.U32) (bend : Array Std.U32 512#usize) (bpos : Slice Std.U32) (nb : Std.Usize) (choice : Slice Std.U32) (chw : Std.Usize) (keep : Std.Usize) (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32) (pr : Std.Usize) (msub : Std.U32) (co : Std.Usize) (lam : Std.U32) :
    slot.b_dp_pass input mstart mc tbl bend bpos nb choice chw keep items istart pr msub co lam ⦃ fun _ => True ⦄ := U10! slot.b_dp_pass
@[local step]
theorem stop_rule_spec (prev : Std.U64) (r : Std.U64) (n : Std.Usize) (it1 : Std.Usize) (gk : Std.U64) (minp : Std.Usize) :
    slot.b_stop_rule prev r n it1 gk minp ⦃ fun _ => True ⦄ := U11! slot.b_stop_rule
@[local step]
theorem one_pass_spec (prev : Std.U64) (n : Std.Usize) (gk : Std.U64) :
    slot.b_one_pass prev n gk ⦃ fun _ => True ⦄ := U11! slot.b_one_pass
@[local step]
theorem cx_sym_loop_spec (fr : Slice Std.U32) (off : Std.Usize) (lens : Slice Std.U32) (kind : Std.U32) (sc : Slice Std.U32) (ew : Std.U32) (lt1 : Std.U32) (ld : Std.U32) (s : Std.Usize) :
    slot.b_cx_sym_loop fr off lens kind sc ew lt1 ld s ⦃ fun _ => True ⦄ := U15! slot.b_cx_sym_loop slot.b_cx_sym_loop.body
@[local step]
theorem cx_sym_spec (fr : Slice Std.U32) (off : Std.Usize) (lens : Slice Std.U32) (kind : Std.U32) (sc : Slice Std.U32) (ew : Std.U32) :
    slot.b_cx_sym fr off lens kind sc ew ⦃ fun _ => True ⦄ := U11! slot.b_cx_sym
@[local step]
theorem cx_eval_loop_spec (fr : Slice Std.U32) (tbl : Slice Std.U32) (damp : Std.U32) (ew : Std.U32) (lens : Array Std.U32 320#usize) (sc : Array Std.U32 320#usize) (total : Std.U64) (lim : Std.Usize) (b : Std.Usize) :
    slot.b_cx_eval_loop fr tbl damp ew lens sc total lim b ⦃ fun _ => True ⦄ := U19! slot.b_cx_eval_loop slot.b_cx_eval_loop.body
@[local step]
theorem cx_eval_spec (fr : Slice Std.U32) (tbl : Slice Std.U32) (nb2 : Std.Usize) (nbmax : Std.Usize) (damp : Std.U32) (ew : Std.U32) :
    slot.b_cx_eval fr tbl nb2 nbmax damp ew ⦃ fun _ => True ⦄ := U10! slot.b_cx_eval
@[local step]
theorem eval_mode_spec (mode : Std.Usize) (fr tbl : Slice Std.U32) (nb nbmax : Std.Usize) (damp ew : Std.U32) :
    slot.b_eval_mode mode fr tbl nb nbmax damp ew ⦃ fun _ => True ⦄ := by
  rw [slot.b_eval_mode]
  split <;> step*
@[local step]
theorem lg8_spec (x : Std.U32) :
    slot.b_lg8 x ⦃ fun _ => True ⦄ := U11! slot.b_lg8
@[local step]
theorem entropy256_loop_spec (h : Array Std.U32 256#usize) (tot : Std.U64) (acc : Std.U64) (i : Std.Usize) :
    slot.b_entropy256_loop h tot acc i ⦃ fun _ => True ⦄ := by
  rw [slot.b_entropy256_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨tot1, acc1, i1⟩ _
    simp only [slot.b_entropy256_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem entropy256_spec (h : Array Std.U32 256#usize) :
    slot.b_entropy256 h ⦃ fun _ => True ⦄ := U10! slot.b_entropy256
@[local step]
theorem hash12_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.b_hash12 input p ⦃ fun _ => True ⦄ := U11! slot.b_hash12
@[local step]
theorem probe_win_loop_spec (input : Slice Std.U8) (ht : Array Std.U32 4096#usize) (s : Std.Usize) (e : Std.Usize) (n : Std.Usize) (i : Std.Usize) (cov : Std.U64) (nm : Std.U64) (it : Std.Usize) :
    slot.b_probe_win_loop input ht s e n i cov nm it ⦃ fun _ => True ⦄ := by
  rw [slot.b_probe_win_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => slot.B_PR_W.val - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨ht1, i1, cov1, nm1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_probe_win_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem probe_win_spec (input : Slice Std.U8) (ht : Array Std.U32 4096#usize) (s : Std.Usize) (e : Std.Usize) :
    slot.b_probe_win input ht s e ⦃ fun _ => True ⦄ := U11! slot.b_probe_win
@[local step]
theorem probe_all_loop_spec (input : Slice Std.U8) (ht : Array Std.U32 4096#usize) (span : Std.Usize) (acc : Std.U64) (k : Std.Usize) :
    slot.b_probe_all_loop input ht span acc k ⦃ fun _ => True ⦄ := by
  rw [slot.b_probe_all_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => slot.B_PR_N.val - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨ht1, acc1, k1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_probe_all_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem probe_all_spec (input : Slice Std.U8) :
    slot.b_probe_all input ⦃ fun _ => True ⦄ := U11! slot.b_probe_all
@[local step]
theorem probe_if_spec (input : Slice Std.U8) (f : Std.Usize) :
    slot.b_probe_if input f ⦃ fun _ => True ⦄ := U10! slot.b_probe_if
@[local step]
theorem odd_sample_loop_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) (n : Std.Usize) (st : Std.Usize) (k : Std.Usize) (c : Std.Usize) :
    slot.b_odd_sample_loop input h n st k c ⦃ fun _ => True ⦄ := by
  rw [slot.b_odd_sample_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨h1, k1, c1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_odd_sample_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem odd_sample_spec (input : Slice Std.U8) (h : Array Std.U32 256#usize) :
    slot.b_odd_sample input h ⦃ fun _ => True ⦄ := U11! slot.b_odd_sample
@[local step]
theorem ge64_spec (a : Std.U64) (b : Std.U64) :
    slot.b_ge64 a b ⦃ fun _ => True ⦄ := U10! slot.b_ge64
@[local step]
theorem byte_classes_loop_spec (h : Array Std.U32 256#usize) (tot : Std.U64) (ctl : Std.U64) (hib : Std.U64) (i : Std.Usize) :
    slot.b_byte_classes_loop h tot ctl hib i ⦃ fun _ => True ⦄ := by
  rw [slot.b_byte_classes_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨tot1, ctl1, hib1, i1⟩ _
    simp only [slot.b_byte_classes_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem byte_classes_spec (h : Array Std.U32 256#usize) :
    slot.b_byte_classes h ⦃ fun _ => True ⦄ := U11! slot.b_byte_classes
@[local step]
theorem byte_classes2_loop_spec (h : Array Std.U32 256#usize) (z0 : Std.U64) (dig : Std.U64) (nz : Std.U64) (i : Std.Usize) :
    slot.b_byte_classes2_loop h z0 dig nz i ⦃ fun _ => True ⦄ := by
  rw [slot.b_byte_classes2_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨z01, dig1, nz1, i1⟩ _
    simp only [slot.b_byte_classes2_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem byte_classes2_spec (h : Array Std.U32 256#usize) :
    slot.b_byte_classes2 h ⦃ fun _ => True ⦄ := U11! slot.b_byte_classes2
@[local step]
theorem classify_spec (input : Slice Std.U8) :
    slot.b_classify input ⦃ fun _ => True ⦄ := U11! slot.b_classify
@[local step]
theorem cx_jitter_loop0_loop0_spec (tbl : Slice Std.U32) (seed : Std.U32) (amp : Std.U32) (off : Std.Usize) (s : Std.Usize) (hamp : amp.val < 33) :
    slot.b_cx_jitter_loop0_loop0 tbl seed amp off s ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_jitter_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 545 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, s1⟩ _
    simp only [slot.b_cx_jitter_loop0_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem cx_jitter_loop0_spec (tbl : Slice Std.U32) (nb : Std.Usize) (seed : Std.U32) (amp : Std.U32) (b : Std.Usize) (hamp : amp.val < 33) :
    slot.b_cx_jitter_loop0 tbl nb seed amp b ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_jitter_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => nb.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, b1⟩ _
    simp only [slot.b_cx_jitter_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
set_option hygiene false in
local notation "U20!" q0__:max => (by
  rw [q0__]
  try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals repeat (first
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac)
@[local step]
theorem cx_jitter_spec (tbl : Slice Std.U32) (nb : Std.Usize) (seed : Std.U32) (amplitude : Std.U32) :
    slot.b_cx_jitter tbl nb seed amplitude ⦃ fun _ => True ⦄ := U20! slot.b_cx_jitter
@[local step]
theorem cx_restarts_loop0_loop0_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32)
  (tbl : Slice Std.U32) (fr : Slice Std.U32) (bpos : Slice Std.U32)
  (bend : Array Std.U32 512#usize) (choice : Slice Std.U32)
  (plan : Slice Std.U32) (nbmax : Std.Usize) (lamh : Std.U32)
  (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32)
  (pr : Std.Usize) (chw : Std.Usize) (n : Std.Usize) (nbc : Std.Usize)
  (bestp : Std.U64) (step : Std.Usize) :
    slot.b_cx_restarts_loop0_loop0 input mstart mc tbl fr bpos bend choice plan nbmax lamh items istart pr chw n nbc bestp step ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_restarts_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 3 - s.2.2.2.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, fr1, bpos1, choice1, plan1, items1, istart1, nbc1, bestp1, step1⟩ _
    simp only [slot.b_cx_restarts_loop0_loop0.body, lift, ite_ok]
    step*
    all_goals (repeat (split <;> step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem cx_restarts_loop0_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32)
  (tbl : Slice Std.U32) (fr : Slice Std.U32) (bpos : Slice Std.U32)
  (bend : Array Std.U32 512#usize) (choice : Slice Std.U32)
  (plan : Slice Std.U32) (nbmax : Std.Usize) (lamh : Std.U32)
  (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32)
  (pr : Std.Usize) (chw : Std.Usize) (restarts : Std.Usize) (n : Std.Usize)
  (jitteron : Std.Usize) (restart : Std.Usize) :
    slot.b_cx_restarts_loop0 input mstart mc tbl fr bpos bend choice plan nbmax lamh items istart pr chw restarts n jitteron restart ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_restarts_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => restarts.val - s.2.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, fr1, bpos1, choice1, plan1, items1, istart1, restart1⟩ _
    simp only [slot.b_cx_restarts_loop0.body, lift, ite_ok]
    step*
    all_goals (repeat (split <;> step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem cx_restarts_spec (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32)
  (tbl : Slice Std.U32) (fr : Slice Std.U32) (bpos : Slice Std.U32)
  (bend : Array Std.U32 512#usize) (choice : Slice Std.U32)
  (plan : Slice Std.U32) (nbmax : Std.Usize) (lamh : Std.U32)
  (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32)
  (pr : Std.Usize) (chw : Std.Usize) (restarts : Std.Usize) :
    slot.b_cx_restarts input mstart mc tbl fr bpos bend choice plan nbmax lamh items istart pr chw restarts ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_restarts]
  try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  all_goals (repeat (split <;> step*))
  all_goals scalar_tac
set_option hygiene false in
local notation "U21!" q0__:max => (by
  rw [q0__]
  simp only [lift, ite_ok, Array.to_slice_mut]
  step*
  all_goals (repeat (split <;> step*))
  all_goals scalar_tac)
@[local step]
theorem w34_kind_spec (input : Slice Std.U8) :
    slot.b_w34_kind input ⦃ fun _ => True ⦄ := U21! slot.b_w34_kind
set_option hygiene false in
local notation "U22!" q0__:max => (by
  rw [q0__]
  step*
  all_goals (repeat (split <;> step*))
  all_goals scalar_tac)
@[local step]
theorem w34_budget_spec (input : Slice Std.U8) :
    slot.b_w34_budget input ⦃ fun _ => True ⦄ := U22! slot.b_w34_budget
@[local step]
theorem w34_next_spec (old : Std.U32) (t : Std.Usize) (k : Std.Usize) :
    slot.b_w34_next old t k ⦃ fun _ => True ⦄ := by
  rw [slot.b_w34_next]
  simp only [lift, ite_ok]
  step*
  all_goals (repeat (split <;> step*))
  all_goals scalar_tac
@[local step]
theorem w34_start_loop0_loop0_spec (tbl : Slice Std.U32) (t : Std.Usize)
    (b : Std.Usize) (k : Std.Usize) :
    slot.b_w34_start_loop0_loop0 tbl t b k ⦃ fun _ => True ⦄ := by
  rw [slot.b_w34_start_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun x => 545 - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, k1⟩ _
    simp only [slot.b_w34_start_loop0_loop0.body, lift, ite_ok]
    step*
    all_goals (repeat (split <;> step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem w34_start_loop0_spec (tbl : Slice Std.U32) (nb : Std.Usize)
    (t : Std.Usize) (b : Std.Usize) :
    slot.b_w34_start_loop0 tbl nb t b ⦃ fun _ => True ⦄ := by
  rw [slot.b_w34_start_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun x => nb.val - x.2.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, b1⟩ _
    simp only [slot.b_w34_start_loop0.body, lift, ite_ok]
    step*
    all_goals (repeat (split <;> step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem w34_start_spec (input : Slice Std.U8) (tbl : Slice Std.U32)
    (nb : Std.Usize) :
    slot.b_w34_start input tbl nb ⦃ fun _ => True ⦄ := U22! slot.b_w34_start
@[local step]
theorem w34_discount_spec (input : Slice Std.U8) (it : Std.Usize) :
    slot.b_w34_discount input it ⦃ fun _ => True ⦄ := U22! slot.b_w34_discount
@[local step]
theorem w34_depth_spec (input : Slice Std.U8) (old : Std.Usize) :
    slot.b_w34_depth input old ⦃ fun _ => True ⦄ := U22! slot.b_w34_depth
@[local step]
theorem w34_tlen_spec (input : Slice Std.U8) (nbmax : Std.Usize) :
    slot.b_w34_tlen input nbmax ⦃ fun _ => True ⦄ := U22! slot.b_w34_tlen
@[local step]
theorem w34_literal_init_spec (input : Slice Std.U8) (fr : Slice Std.U32)
    (hist : Array Std.U32 256#usize) (tlit : Slice Std.U32) (t5 : Slice Std.U32) :
    slot.b_w34_literal_init input fr hist tlit t5 ⦃ fun _ => True ⦄ := U21! slot.b_w34_literal_init
@[local step]
theorem iterate_loop_spec (mode : Std.Usize) (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (tbl : Slice Std.U32) (fr : Slice Std.U32) (bpos : Slice Std.U32) (bend : Array Std.U32 512#usize) (choice : Slice Std.U32) (nbmax : Std.Usize) (gk : Std.U64) (lamh : Std.U32) (minp : Std.Usize) (ew : Std.U32) (n : Std.Usize) (nb : Std.Usize) (best : Std.U64) (prev : Std.U64) (stop : Std.Usize) (it : Std.Usize) (items : alloc.vec.Vec Std.U32) (istart : alloc.vec.Vec Std.U32) (kp0 : Std.Usize) (pr : Std.Usize) (wh : Std.Usize) (bh : Std.Usize) (chw : Std.Usize) :
    slot.b_iterate_loop mode input mstart mc tbl fr bpos bend choice nbmax gk lamh minp ew n nb best prev stop it items istart kp0 pr wh bh chw ⦃ fun _ => True ⦄ := by
  rw [slot.b_iterate_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => slot.B_ITERS.val - qq9.2.2.2.2.2.2.2.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨tbl1, fr1, bpos1, choice1, nb1, best1, prev1, stop1, it1, items1, istart1, pr1, wh1, bh1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_iterate_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem iterate_spec (mode : Std.Usize) (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (tbl : Slice Std.U32) (fr : Slice Std.U32) (bpos : Slice Std.U32) (bend : Array Std.U32 512#usize) (choice : Slice Std.U32) (plan : Slice Std.U32) (nbmax : Std.Usize) (nb0 : Std.Usize) (best0 : Std.U64) (prev0 : Std.U64) (gk : Std.U64) (lamh : Std.U32) (minp : Std.Usize) (ew : Std.U32) :
    slot.b_iterate mode input mstart mc tbl fr bpos bend choice plan nbmax nb0 best0 prev0 gk lamh minp ew ⦃ fun _ => True ⦄ := U11! slot.b_iterate
@[local step]
theorem lit_bpos_loop_spec (bpos : Slice Std.U32) (m : Std.Usize) (b : Std.Usize) :
    slot.b_lit_bpos_loop bpos m b ⦃ fun _ => True ⦄ := by
  rw [slot.b_lit_bpos_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => m.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨bpos1, b1⟩ _
    simp only [slot.b_lit_bpos_loop.body, lift, ite_ok]
    step*
    repeat (split <;> step*)
    all_goals scalar_tac
  · trivial
@[local step]
theorem lit_bpos_spec (bpos : Slice Std.U32) (m : Std.Usize) :
    slot.b_lit_bpos bpos m ⦃ fun _ => True ⦄ := U10! slot.b_lit_bpos
@[local step]
theorem optimize_spec (mode : Std.Usize) (input : Slice Std.U8) (mstart : Slice Std.U32) (mc : Slice Std.U32) (tbl : Slice Std.U32) (fr : Slice Std.U32) (bpos : Slice Std.U32) (bend : Array Std.U32 512#usize) (choice : Slice Std.U32) (plan : Slice Std.U32) (nbmax : Std.Usize) (gk : Std.U64) (i5 : Std.Usize) :
    slot.b_optimize mode input mstart mc tbl fr bpos bend choice plan nbmax gk i5 ⦃ fun _ => True ⦄ := U11! slot.b_optimize
set_option hygiene false in
local notation "U23!" q0__:max => (by
  rw [q0__]
  try simp only [ite_ok]
  step*
  repeat (first
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac)
@[local step]
theorem h_at64_spec (a : Array Std.U64 8192#usize) (i : Std.Usize) :
    slot.b_h_at64 a i ⦃ fun _ => True ⦄ := U23! slot.b_h_at64
@[local step]
theorem h_put64_spec (a : Array Std.U64 8192#usize) (i : Std.Usize) (x : Std.U64) :
    slot.b_h_put64 a i x ⦃ fun _ => True ⦄ := U23! slot.b_h_put64
set_option hygiene false in
local notation "U24!" q0__:max => (by
  rw [q0__]
  simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  repeat (first
    | (split <;> (try step*))
    | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
    | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
    | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
    | (apply spec_ite_cut <;> intro hc <;> try step*)
    | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
    | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
  all_goals scalar_tac)
@[local step]
theorem h_load_le32_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.b_h_load_le32 input p ⦃ fun _ => True ⦄ := U24! slot.b_h_load_le32
@[local step]
theorem h_word_at_spec (input : Slice Std.U8) (p : Std.Usize) :
    slot.b_h_word_at input p ⦃ fun _ => True ⦄ := U24! slot.b_h_word_at
@[local step]
theorem h_tzb_spec (x : Std.U64) :
    slot.b_h_tzb x ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_tzb]
  apply spec_ite_cut <;> intro hc <;> step*
@[local step]
theorem h_hash4_spec (w : Std.U32) :
    slot.b_h_hash4 w ⦃ fun _ => True ⦄ := U24! slot.b_h_hash4
@[local step]
theorem h_byte_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) (n : Std.Usize) (l : Std.Usize) :
    slot.b_h_byte_len_loop input a b cap n l ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_byte_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => cap.val - qq9.val)
    (inv := fun _ => True)
  · rintro l1 _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_byte_len_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_byte_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) :
    slot.b_h_byte_len input a b cap ⦃ fun _ => True ⦄ := U23! slot.b_h_byte_len
@[local step]
theorem h_fast_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) (n : Std.Usize) (l : Std.Usize) (go : Std.Usize) (it : Std.Usize) :
    slot.b_h_fast_len_loop input a b cap n l go it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_fast_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 34 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨l1, go1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_fast_len_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_fast_len_spec (input : Slice Std.U8) (a : Std.Usize) (b : Std.Usize) (cap : Std.Usize) :
    slot.b_h_fast_len input a b cap ⦃ fun _ => True ⦄ := U23! slot.b_h_fast_len
@[local step]
theorem h_back_len_loop_spec (input : Slice Std.U8) (a : Std.Usize) (c : Std.Usize) (cap : Std.Usize) (k : Std.Usize) (go : Std.Usize) (it : Std.Usize) :
    slot.b_h_back_len_loop input a c cap k go it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_back_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 40 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨k1, go1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_back_len_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_back_len_spec (input : Slice Std.U8) (a : Std.Usize) (c : Std.Usize) (cap : Std.Usize) :
    slot.b_h_back_len input a c cap ⦃ fun _ => True ⦄ := U23! slot.b_h_back_len
@[local step]
theorem h_log2_16_spec (v : Std.U32) :
    slot.b_h_log2_16 v ⦃ fun _ => True ⦄ := U24! slot.b_h_log2_16
@[local step]
theorem h_sym_cost_spec (f : Std.U32) (lt1 : Std.U32) :
    slot.b_h_sym_cost f lt1 ⦃ fun _ => True ⦄ := U23! slot.b_h_sym_cost
@[local step]
theorem h_dist_sym_spec (d : Std.Usize) :
    slot.b_h_dist_sym d ⦃ fun _ => True ⦄ := U24! slot.b_h_dist_sym
@[local step]
theorem h_dist_cost_spec (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (d : Std.Usize) :
    slot.b_h_dist_cost dcs dcb d ⦃ fun _ => True ⦄ := U24! slot.b_h_dist_cost
@[local step]
theorem h_sum_arr_loop_spec (a : Array Std.U32 512#usize) (m : Std.Usize) (s : Std.U32) (i : Std.Usize) :
    slot.b_h_sum_arr_loop a m s i ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_sum_arr_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => m.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨s1, i1⟩ _
    simp only [slot.b_h_sum_arr_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_sum_arr_spec (a : Array Std.U32 512#usize) (m : Std.Usize) :
    slot.b_h_sum_arr a m ⦃ fun _ => True ⦄ := U23! slot.b_h_sum_arr
@[local step]
theorem h_sum_df_loop_spec (a : Array Std.U32 32#usize) (s : Std.U32) (i : Std.Usize) :
    slot.b_h_sum_df_loop a s i ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_sum_df_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 30 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨s1, i1⟩ _
    simp only [slot.b_h_sum_df_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_sum_df_spec (a : Array Std.U32 32#usize) :
    slot.b_h_sum_df a ⦃ fun _ => True ⦄ := U23! slot.b_h_sum_df
@[local step]
theorem h_lit_costs_loop_spec (llf : Array Std.U32 512#usize) (lt1 : Std.U32) (litc : Array Std.U32 256#usize) (b : Std.Usize) :
    slot.b_h_lit_costs_loop llf lt1 litc b ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_lit_costs_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨litc1, b1⟩ _
    simp only [slot.b_h_lit_costs_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_lit_costs_spec (llf : Array Std.U32 512#usize) (lt1 : Std.U32) (litc : Array Std.U32 256#usize) :
    slot.b_h_lit_costs llf lt1 litc ⦃ fun _ => True ⦄ := U23! slot.b_h_lit_costs
@[local step]
theorem h_len_costs_loop0_spec (llf : Array Std.U32 512#usize) (lt1 : Std.U32) (scost : Array Std.U32 32#usize) (s : Std.Usize) :
    slot.b_h_len_costs_loop0 llf lt1 scost s ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_len_costs_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 29 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨scost1, s1⟩ _
    simp only [slot.b_h_len_costs_loop0.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_len_costs_loop1_spec (scost : Array Std.U32 32#usize) (lcost : Array Std.U32 512#usize) (l : Std.Usize) :
    slot.b_h_len_costs_loop1 scost lcost l ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_len_costs_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 259 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨lcost1, l1⟩ _
    simp only [slot.b_h_len_costs_loop1.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_len_costs_spec (llf : Array Std.U32 512#usize) (lt1 : Std.U32) (scost : Array Std.U32 32#usize) (lcost : Array Std.U32 512#usize) :
    slot.b_h_len_costs llf lt1 scost lcost ⦃ fun _ => True ⦄ := U23! slot.b_h_len_costs
@[local step]
theorem h_dist_costs_loop0_spec (df : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (lt1 : Std.U32) (s : Std.Usize) :
    slot.b_h_dist_costs_loop0 df scost lt1 s ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_dist_costs_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 30 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨scost1, s1⟩ _
    simp only [slot.b_h_dist_costs_loop0.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_dist_costs_loop1_spec (scost : Array Std.U32 32#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (j : Std.Usize) :
    slot.b_h_dist_costs_loop1 scost dcs dcb j ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_dist_costs_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨dcs1, dcb1, j1⟩ _
    simp only [slot.b_h_dist_costs_loop1.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_dist_costs_spec (df : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) :
    slot.b_h_dist_costs df scost dcs dcb ⦃ fun _ => True ⦄ := U23! slot.b_h_dist_costs
set_option hygiene false in
local notation "U25!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 512 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨dst1, i1⟩ _
    simp only [q1__, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_mix_loop_spec (dst : Array Std.U32 512#usize) (cur : Array Std.U32 512#usize) (prv : Array Std.U32 512#usize) (i : Std.Usize) :
    slot.b_h_mix_loop dst cur prv i ⦃ fun _ => True ⦄ := U25! slot.b_h_mix_loop slot.b_h_mix_loop.body
@[local step]
theorem h_mix_spec (dst : Array Std.U32 512#usize) (cur : Array Std.U32 512#usize) (prv : Array Std.U32 512#usize) :
    slot.b_h_mix dst cur prv ⦃ fun _ => True ⦄ := U23! slot.b_h_mix
set_option hygiene false in
local notation "U26!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨dst1, i1⟩ _
    simp only [q1__, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_mix32_loop_spec (dst : Array Std.U32 32#usize) (cur : Array Std.U32 32#usize) (prv : Array Std.U32 32#usize) (i : Std.Usize) :
    slot.b_h_mix32_loop dst cur prv i ⦃ fun _ => True ⦄ := U26! slot.b_h_mix32_loop slot.b_h_mix32_loop.body
@[local step]
theorem h_mix32_spec (dst : Array Std.U32 32#usize) (cur : Array Std.U32 32#usize) (prv : Array Std.U32 32#usize) :
    slot.b_h_mix32 dst cur prv ⦃ fun _ => True ⦄ := U23! slot.b_h_mix32
@[local step]
theorem h_copy512_loop_spec (dst : Array Std.U32 512#usize) (src : Array Std.U32 512#usize) (i : Std.Usize) :
    slot.b_h_copy512_loop dst src i ⦃ fun _ => True ⦄ := U25! slot.b_h_copy512_loop slot.b_h_copy512_loop.body
@[local step]
theorem h_copy512_spec (dst : Array Std.U32 512#usize) (src : Array Std.U32 512#usize) :
    slot.b_h_copy512 dst src ⦃ fun _ => True ⦄ := U23! slot.b_h_copy512
@[local step]
theorem h_copy32_loop_spec (dst : Array Std.U32 32#usize) (src : Array Std.U32 32#usize) (i : Std.Usize) :
    slot.b_h_copy32_loop dst src i ⦃ fun _ => True ⦄ := U26! slot.b_h_copy32_loop slot.b_h_copy32_loop.body
@[local step]
theorem h_copy32_spec (dst : Array Std.U32 32#usize) (src : Array Std.U32 32#usize) :
    slot.b_h_copy32 dst src ⦃ fun _ => True ⦄ := U23! slot.b_h_copy32
@[local step]
theorem h_clear512_loop_spec (a : Array Std.U32 512#usize) (i : Std.Usize) :
    slot.b_h_clear512_loop a i ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_clear512_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 512 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨a1, i1⟩ _
    simp only [slot.b_h_clear512_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_clear512_spec (a : Array Std.U32 512#usize) :
    slot.b_h_clear512 a ⦃ fun _ => True ⦄ := U23! slot.b_h_clear512
@[local step]
theorem h_clear32_loop_spec (a : Array Std.U32 32#usize) (i : Std.Usize) :
    slot.b_h_clear32_loop a i ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_clear32_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨a1, i1⟩ _
    simp only [slot.b_h_clear32_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_clear32_spec (a : Array Std.U32 32#usize) :
    slot.b_h_clear32 a ⦃ fun _ => True ⦄ := U23! slot.b_h_clear32
@[local step]
theorem h_sample_hist_loop_spec (input : Slice Std.U8) (h0 : Array Std.U32 256#usize) (h1 : Array Std.U32 256#usize) (h2 : Array Std.U32 256#usize) (h3 : Array Std.U32 256#usize) (q : Std.Usize) (k : Std.Usize) :
    slot.b_h_sample_hist_loop input h0 h1 h2 h3 q k ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_sample_hist_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => q.val - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨h01, h11, h21, h31, k1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_sample_hist_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_sample_hist_spec (input : Slice Std.U8) (h0 : Array Std.U32 256#usize) (h1 : Array Std.U32 256#usize) (h2 : Array Std.U32 256#usize) (h3 : Array Std.U32 256#usize) :
    slot.b_h_sample_hist input h0 h1 h2 h3 ⦃ fun _ => True ⦄ := U23! slot.b_h_sample_hist
@[local step]
theorem h_init_stats_loop0_spec (llf : Array Std.U32 512#usize) (h0 : Array Std.U32 256#usize) (h1 : Array Std.U32 256#usize) (h2 : Array Std.U32 256#usize) (h3 : Array Std.U32 256#usize) (sc : Std.U32) (b : Std.Usize) :
    slot.b_h_init_stats_loop0 llf h0 h1 h2 h3 sc b ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_init_stats_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨llf1, b1⟩ _
    simp only [slot.b_h_init_stats_loop0.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_init_stats_loop1_spec (llf : Array Std.U32 512#usize) (pm : Std.U32) (s : Std.Usize) :
    slot.b_h_init_stats_loop1 llf pm s ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_init_stats_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 29 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨llf1, s1⟩ _
    simp only [slot.b_h_init_stats_loop1.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_init_stats_loop2_spec (df : Array Std.U32 32#usize) (pm : Std.U32) (t : Std.Usize) :
    slot.b_h_init_stats_loop2 df pm t ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_init_stats_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 30 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨df1, t1⟩ _
    simp only [slot.b_h_init_stats_loop2.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_init_stats_spec (input : Slice Std.U8) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) :
    slot.b_h_init_stats input llf df ⦃ fun _ => True ⦄ := U24! slot.b_h_init_stats
@[local step]
theorem h_scale_prior_loop0_spec (llf : Array Std.U32 512#usize) (i : Std.Usize) :
    slot.b_h_scale_prior_loop0 llf i ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_scale_prior_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 512 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨llf1, i1⟩ _
    simp only [slot.b_h_scale_prior_loop0.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_scale_prior_loop1_spec (df : Array Std.U32 32#usize) (j : Std.Usize) :
    slot.b_h_scale_prior_loop1 df j ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_scale_prior_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨df1, j1⟩ _
    simp only [slot.b_h_scale_prior_loop1.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_scale_prior_spec (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) :
    slot.b_h_scale_prior llf df ⦃ fun _ => True ⦄ := U23! slot.b_h_scale_prior
@[local step]
theorem h_all_costs_spec (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) :
    slot.b_h_all_costs llf df scost litc lcost dcs dcb ⦃ fun _ => True ⦄ := U23! slot.b_h_all_costs
@[local step]
theorem h_hash3i_spec (input : Slice Std.U8) (i : Std.Usize) :
    slot.b_h_hash3i input i ⦃ fun _ => True ⦄ := U24! slot.b_h_hash3i
@[local step]
theorem h_rec_spec (ed : Array Std.U64 32768#usize) (t : Std.Usize) (s : Std.Usize) (lo : Std.Usize) (hi : Std.Usize) (d : Std.Usize) :
    slot.b_h_rec ed t s lo hi d ⦃ fun _ => True ⦄ := U24! slot.b_h_rec
@[local step]
theorem h_relax_range_loop_spec (arr : Array Std.U64 8192#usize) (lcost : Array Std.U32 512#usize) (cur : Std.Usize) (hi : Std.Usize) (base : Std.U32) (ebits : Std.U64) (l : Std.Usize) (it : Std.Usize) :
    slot.b_h_relax_range_loop arr lcost cur hi base ebits l it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_relax_range_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 260 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨arr1, l1, it1⟩ _
    simp only [slot.b_h_relax_range_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_relax_range_spec (arr : Array Std.U64 8192#usize) (lcost : Array Std.U32 512#usize) (cur : Std.Usize) (lo : Std.Usize) (hi : Std.Usize) (base : Std.U32) (ebits : Std.U64) :
    slot.b_h_relax_range arr lcost cur lo hi base ebits ⦃ fun _ => True ⦄ := U23! slot.b_h_relax_range
@[local step]
theorem h_relax3_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (pos : Std.Usize) (cur : Std.Usize) (price : Std.U32) (s3 : Std.Usize) (cap : Std.Usize) :
    slot.b_h_relax3 input arr ed lcost dcs dcb pos cur price s3 cap ⦃ fun _ => True ⦄ := U24! slot.b_h_relax3
@[local step]
theorem h_insert_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (i : Std.Usize) (on : Bool) :
    slot.b_h_insert input head prev h3 i on ⦃ fun _ => True ⦄ := U24! slot.b_h_insert
@[local step]
theorem h_insert_run_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (start : Std.Usize) (stop : Std.Usize) (cur : Std.Usize) (it : Std.Usize) :
    slot.b_h_insert_run_loop input head prev h3 start stop cur it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_insert_run_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨head1, prev1, h31, cur1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_insert_run_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_insert_run_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (start : Std.Usize) (cur0 : Std.Usize) (stop : Std.Usize) :
    slot.b_h_insert_run input head prev h3 start cur0 stop ⦃ fun _ => True ⦄ := U23! slot.b_h_insert_run
@[local step]
theorem h_interior_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (start : Std.Usize) (s1 : Std.Usize) (cur : Std.Usize) (price : Std.U32) (it : Std.Usize) :
    slot.b_h_interior_loop input head prev h3 arr litc start s1 cur price it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_interior_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => slot.B_H_LITK.val - qq9.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨head1, prev1, h31, arr1, cur1, price1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_interior_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_interior_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (start : Std.Usize) (cur0 : Std.Usize) (stop : Std.Usize) (price0 : Std.U32) :
    slot.b_h_interior input head prev h3 arr litc start cur0 stop price0 ⦃ fun _ => True ⦄ := U24! slot.b_h_interior
@[local step]
theorem h_lit_run_loop_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (start : Std.Usize) (stop : Std.Usize) (cur : Std.Usize) (price : Std.U32) (it : Std.Usize) :
    slot.b_h_lit_run_loop input arr litc start stop cur price it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_lit_run_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨arr1, cur1, price1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_lit_run_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_lit_run_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (start : Std.Usize) (cur0 : Std.Usize) (stop : Std.Usize) (price0 : Std.U32) :
    slot.b_h_lit_run input arr litc start cur0 stop price0 ⦃ fun _ => True ⦄ := U23! slot.b_h_lit_run
@[local step]
theorem h_cand_len_spec (input : Slice Std.U8) (c : Std.Usize) (pos : Std.Usize) (cap : Std.Usize) (x : Std.U64) :
    slot.b_h_cand_len input c pos cap x ⦃ fun _ => True ⦄ := U24! slot.b_h_cand_len
@[local step]
theorem h_back_ext_spec (input : Slice Std.U8) (pos : Std.Usize) (c : Std.Usize) (cap : Std.Usize) (wb : Std.U64) :
    slot.b_h_back_ext input pos c cap wb ⦃ fun _ => True ⦄ := U24! slot.b_h_back_ext
@[local step]
theorem h_relax_cand_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (pos : Std.Usize) (cur : Std.Usize) (price : Std.U32) (c : Std.Usize) (d : Std.Usize) (lo : Std.Usize) (l : Std.Usize) (wb : Std.U64) (bx : Std.Usize) :
    slot.b_h_relax_cand input arr ed lcost dcs dcb pos cur price c d lo l wb bx ⦃ fun _ => True ⦄ := U24! slot.b_h_relax_cand
@[local step]
theorem h_search_relax_loop_spec (input : Slice Std.U8) (prev : Array Std.U16 32768#usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (pos : Std.Usize) (cur : Std.Usize) (cap : Std.Usize) (depth : Std.Usize) (price : Std.U32) (bx : Std.Usize) (wp : Std.U64) (wb : Std.U64) (best : Std.Usize) (d : Std.Usize) (probes : Std.Usize) :
    slot.b_h_search_relax_loop input prev arr ed lcost dcs dcb pos cur cap depth price bx wp wb best d probes ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_search_relax_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => depth.val - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨arr1, ed1, best1, d1, probes1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_search_relax_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_search_relax_spec (input : Slice Std.U8) (prev : Array Std.U16 32768#usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (pos : Std.Usize) (cur : Std.Usize) (cap : Std.Usize) (s4 : Std.Usize) (depth : Std.Usize) (price : Std.U32) (bx : Std.Usize) :
    slot.b_h_search_relax input prev arr ed lcost dcs dcb pos cur cap s4 depth price bx ⦃ fun _ => True ⦄ := U24! slot.b_h_search_relax
@[local step]
theorem h_insert_range_loop_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (to0 : Std.Usize) (lim : Std.Usize) (i : Std.Usize) (it : Std.Usize) :
    slot.b_h_insert_range_loop input head prev h3 to0 lim i it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_insert_range_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 300 - qq9.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨head1, prev1, h31, i1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_insert_range_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_insert_range_spec (input : Slice Std.U8) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (from0 : Std.Usize) (to0 : Std.Usize) :
    slot.b_h_insert_range input head prev h3 from0 to0 ⦃ fun _ => True ⦄ := U23! slot.b_h_insert_range
@[local step]
theorem h_fill_inf_loop_spec (arr : Array Std.U64 8192#usize) (j : Std.Usize) :
    slot.b_h_fill_inf_loop arr j ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_fill_inf_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨arr1, j1⟩ _
    simp only [slot.b_h_fill_inf_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_fill_inf_spec (arr : Array Std.U64 8192#usize) :
    slot.b_h_fill_inf arr ⦃ fun _ => True ⦄ := U23! slot.b_h_fill_inf
@[local step]
theorem h_lit_step_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (litc : Array Std.U32 256#usize) (i : Std.Usize) (cur : Std.Usize) (price : Std.U32) (on : Bool) :
    slot.b_h_lit_step input arr litc i cur price on ⦃ fun _ => True ⦄ := U24! slot.b_h_lit_step
@[local step]
theorem h_go_spec (cur : Std.Usize) (lim : Std.Usize) (reach : Std.Usize) :
    slot.b_h_go cur lim reach ⦃ fun _ => True ⦄ := U23! slot.b_h_go
@[local step]
theorem h_dp_block_loop_spec (input : Slice Std.U8) (start : Std.Usize) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (kend : Std.Usize) (smask : Std.U64) (hdep : Std.Usize) (dbase : Std.Usize) (rem : Std.Usize) (bend : Std.Usize) (lim : Std.Usize) (go : Std.Usize) (price : Std.U32) (cur : Std.Usize) (reach : Std.Usize) (miss : Std.Usize) (sparse : Std.Usize) (acc_next : Std.Usize) (it : Std.Usize) :
    slot.b_h_dp_block_loop input start head prev h3 arr ed litc lcost dcs dcb kend smask hdep dbase rem bend lim go price cur reach miss sparse acc_next it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_dp_block_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨head1, prev1, h31, arr1, ed1, lim1, go1, price1, cur1, reach1, miss1, acc_next1, it1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_dp_block_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_dp_block_spec (input : Slice Std.U8) (start : Std.Usize) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (cl : Array Std.U32 16#usize) (cd : Array Std.U32 16#usize) (cb : Array Std.U32 16#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (st : Array Std.Usize 4#usize) (kcode : Std.Usize) :
    slot.b_h_dp_block input start head prev h3 arr ed cl cd cb litc lcost dcs dcb st kcode ⦃ fun _ => True ⦄ := U24! slot.b_h_dp_block
@[local step]
theorem h_refresh_spec (full : Bool) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (pllf : Array Std.U32 512#usize) (pdf : Array Std.U32 32#usize) (tllf : Array Std.U32 512#usize) (tdf : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) :
    slot.b_h_refresh full llf df pllf pdf tllf tdf scost litc lcost dcs dcb ⦃ fun _ => True ⦄ := U23! slot.b_h_refresh
@[local step]
theorem h_replay_at_loop_spec (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (p : Std.Usize) (cnt : Std.Usize) (q : Std.Usize) (it : Std.Usize) :
    slot.b_h_replay_at_loop arr ed lcost dcs dcb p cnt q it ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_replay_at_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32768 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨arr1, q1, it1⟩ _
    simp only [slot.b_h_replay_at_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_replay_at_spec (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (p : Std.Usize) (q0 : Std.Usize) (cnt : Std.Usize) :
    slot.b_h_replay_at arr ed lcost dcs dcb p q0 cnt ⦃ fun _ => True ⦄ := U23! slot.b_h_replay_at
@[local step]
theorem h_replay_loop_spec (input : Slice Std.U8) (start : Std.Usize) (bend : Std.Usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (cnt : Std.Usize) (q : Std.Usize) (p : Std.Usize) :
    slot.b_h_replay_loop input start bend arr ed litc lcost dcs dcb cnt q p ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_replay_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨arr1, q1, p1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_replay_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_replay_spec (input : Slice Std.U8) (start : Std.Usize) (bend : Std.Usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) :
    slot.b_h_replay input start bend arr ed litc lcost dcs dcb ⦃ fun _ => True ⦄ := U24! slot.b_h_replay
@[local step]
theorem h_mix3_loop_spec (dst : Array Std.U32 512#usize) (blk : Array Std.U32 512#usize) (run : Array Std.U32 512#usize) (prv : Array Std.U32 512#usize) (i : Std.Usize) :
    slot.b_h_mix3_loop dst blk run prv i ⦃ fun _ => True ⦄ := U25! slot.b_h_mix3_loop slot.b_h_mix3_loop.body
@[local step]
theorem h_mix3_spec (dst : Array Std.U32 512#usize) (blk : Array Std.U32 512#usize) (run : Array Std.U32 512#usize) (prv : Array Std.U32 512#usize) :
    slot.b_h_mix3 dst blk run prv ⦃ fun _ => True ⦄ := U23! slot.b_h_mix3
@[local step]
theorem h_mix3s_loop_spec (dst : Array Std.U32 32#usize) (blk : Array Std.U32 32#usize) (run : Array Std.U32 32#usize) (prv : Array Std.U32 32#usize) (i : Std.Usize) :
    slot.b_h_mix3s_loop dst blk run prv i ⦃ fun _ => True ⦄ := U26! slot.b_h_mix3s_loop slot.b_h_mix3s_loop.body
@[local step]
theorem h_mix3s_spec (dst : Array Std.U32 32#usize) (blk : Array Std.U32 32#usize) (run : Array Std.U32 32#usize) (prv : Array Std.U32 32#usize) :
    slot.b_h_mix3s dst blk run prv ⦃ fun _ => True ⦄ := U23! slot.b_h_mix3s
@[local step]
theorem h_add512_loop_spec (dst : Array Std.U32 512#usize) (src : Array Std.U32 512#usize) (i : Std.Usize) :
    slot.b_h_add512_loop dst src i ⦃ fun _ => True ⦄ := U25! slot.b_h_add512_loop slot.b_h_add512_loop.body
@[local step]
theorem h_add512_spec (dst : Array Std.U32 512#usize) (src : Array Std.U32 512#usize) :
    slot.b_h_add512 dst src ⦃ fun _ => True ⦄ := U23! slot.b_h_add512
@[local step]
theorem h_add32_loop_spec (dst : Array Std.U32 32#usize) (src : Array Std.U32 32#usize) (i : Std.Usize) :
    slot.b_h_add32_loop dst src i ⦃ fun _ => True ⦄ := U26! slot.b_h_add32_loop slot.b_h_add32_loop.body
@[local step]
theorem h_add32_spec (dst : Array Std.U32 32#usize) (src : Array Std.U32 32#usize) :
    slot.b_h_add32 dst src ⦃ fun _ => True ⦄ := U23! slot.b_h_add32
@[local step]
theorem h_replay_flag_spec (e0 : Std.U64) (p1 : Std.U64) (c1 : Std.U64) :
    slot.b_h_replay_flag e0 p1 c1 ⦃ fun _ => True ⦄ := U24! slot.b_h_replay_flag
@[local step]
theorem h_model_cost_loop0_spec (llf1 : Array Std.U32 512#usize) (litc : Array Std.U32 256#usize) (c : Std.U64) (b : Std.Usize) :
    slot.b_h_model_cost_loop0 llf1 litc c b ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_model_cost_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨c1, b1⟩ _
    simp only [slot.b_h_model_cost_loop0.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_model_cost_loop1_spec (llf1 : Array Std.U32 512#usize) (lcost : Array Std.U32 512#usize) (c : Std.U64) (s : Std.Usize) :
    slot.b_h_model_cost_loop1 llf1 lcost c s ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_model_cost_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 29 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨c1, s1⟩ _
    simp only [slot.b_h_model_cost_loop1.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_model_cost_loop2_spec (df1 : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (c : Std.U64) (t : Std.Usize) :
    slot.b_h_model_cost_loop2 df1 scost c t ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_model_cost_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 30 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨c1, t1⟩ _
    simp only [slot.b_h_model_cost_loop2.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_model_cost_spec (llf1 : Array Std.U32 512#usize) (df1 : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (scost : Array Std.U32 32#usize) :
    slot.b_h_model_cost llf1 df1 litc lcost scost ⦃ fun _ => True ⦄ := U23! slot.b_h_model_cost
@[local step]
theorem h_count_spec (input : Slice Std.U8) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (ism : Std.Usize) (l : Std.Usize) (d : Std.Usize) (q : Std.Usize) :
    slot.b_h_count input llf df ism l d q ⦃ fun _ => True ⦄ := U24! slot.b_h_count
@[local step]
theorem h_step_len_spec (l0 : Std.Usize) (d : Std.Usize) (e : Std.Usize) :
    slot.b_h_step_len l0 d e ⦃ fun _ => True ⦄ := U23! slot.b_h_step_len
@[local step]
theorem h_backtrack_loop_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (plan : Slice Std.U32) (start : Std.Usize) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (e : Std.Usize) (cnt : Std.Usize) (lits : Std.Usize) (guard : Std.Usize) :
    slot.b_h_backtrack_loop input arr plan start llf df e cnt lits guard ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_backtrack_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨plan1, llf1, df1, e1, cnt1, lits1, guard1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_h_backtrack_loop.body, lift, ite_ok]
    step*
    repeat (first
      | (split <;> (try step*))
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
theorem h_backtrack_spec (input : Slice Std.U8) (arr : Array Std.U64 8192#usize) (plan : Slice Std.U32) (start : Std.Usize) (end0 : Std.Usize) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) :
    slot.b_h_backtrack input arr plan start end0 llf df ⦃ fun _ => True ⦄ := U24! slot.b_h_backtrack
@[local step]
theorem h_redo_spec (input : Slice Std.U8) (pos0 : Std.Usize) (blen : Std.Usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (plan : Slice Std.U32) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (llf1 : Array Std.U32 512#usize) (df1 : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (go : Std.Usize) (t1 : Std.Usize) :
    slot.b_h_redo input pos0 blen arr ed plan llf df llf1 df1 litc lcost dcs dcb go t1 ⦃ fun _ => True ⦄ := U23! slot.b_h_redo
@[local step]
theorem h_second_spec (input : Slice Std.U8) (pos0 : Std.Usize) (blen : Std.Usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (plan : Slice Std.U32) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (llf1 : Array Std.U32 512#usize) (df1 : Array Std.U32 32#usize) (pllf : Array Std.U32 512#usize) (pdf : Array Std.U32 32#usize) (tllf : Array Std.U32 512#usize) (tdf : Array Std.U32 32#usize) (scost : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) :
    slot.b_h_second input pos0 blen arr ed plan llf df llf1 df1 pllf pdf tllf tdf scost litc lcost dcs dcb ⦃ fun _ => True ⦄ := U23! slot.b_h_second
@[local step]
theorem h_clamp_block_spec (e rest : Std.Usize) :
    slot.b_h_clamp_block e rest ⦃ fun r => 1 ≤ r.val ∧ (r.val = 1 ∨ r.val ≤ rest.val) ⦄ := by
  rw [slot.b_h_clamp_block]
  step*
@[local step]
theorem cx_bits_only_loop_spec (fr : Slice Std.U32) (lens : Array Std.U32 320#usize) (b : Std.Usize) (total : Std.U64) (lim : Std.Usize) :
    slot.b_cx_bits_only_loop fr lens b total lim ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_bits_only_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => lim.val - qq9.2.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨fr1, lens1, b1, total1⟩ _
    simp only [slot.b_cx_bits_only_loop.body]
    step*
    all_goals (repeat (split <;> try step*))
    all_goals scalar_tac
  · trivial
@[local step]
theorem cx_bits_only_spec (fr : Slice Std.U32) (nb : Std.Usize) (nbmax : Std.Usize) :
    slot.b_cx_bits_only fr nb nbmax ⦃ fun _ => True ⦄ := U20! slot.b_cx_bits_only
@[local step]
theorem cx_hload_loop0_spec (tbl : Slice Std.U32) (litc : Array Std.U32 256#usize) (off : Std.Usize) (c : Std.Usize) :
    slot.b_cx_hload_loop0 tbl litc off c ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hload_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨litc1, c1⟩ _
    simp only [slot.b_cx_hload_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem cx_hload_loop1_spec (tbl : Slice Std.U32) (lcost : Array Std.U32 512#usize) (off : Std.Usize) (l : Std.Usize) :
    slot.b_cx_hload_loop1 tbl lcost off l ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hload_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 259 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨lcost1, l1⟩ _
    simp only [slot.b_cx_hload_loop1.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem cx_hload_loop2_spec (tbl : Slice Std.U32) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (off : Std.Usize) (j : Std.Usize) :
    slot.b_cx_hload_loop2 tbl dcs dcb off j ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hload_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 256 - qq9.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨dcs1, dcb1, j1⟩ _
    simp only [slot.b_cx_hload_loop2.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem cx_hload_spec (tbl : Slice Std.U32) (b : Std.Usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) :
    slot.b_cx_hload tbl b litc lcost dcs dcb ⦃ fun _ => True ⦄ := U20! slot.b_cx_hload
set_option hygiene false in
local notation "U27!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => nb.val - qq9.val)
    (inv := fun b => b.val < Std.Usize.max)
  · rintro b1 hb1
    simp only [q1__]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals (split_ifs at * <;> simp_all <;> scalar_tac)
  · exact hb)
@[local step]
theorem cx_hreplay_loop0_spec (start : Std.Usize) (bpos : Slice Std.U32) (nb : Std.Usize) (b : Std.Usize) (hb : b.val < Std.Usize.max) :
    slot.b_cx_hreplay_loop0 start bpos nb b ⦃ fun r => r.val < Std.Usize.max ⦄ := U27! slot.b_cx_hreplay_loop0 slot.b_cx_hreplay_loop0.body
@[local step]
theorem cx_hreplay_loop1_spec (ed : Array Std.U64 32768#usize) (inh : Array Std.U32 8192#usize) (ie : Std.Usize) (ic : Std.Usize) :
    slot.b_cx_hreplay_loop1 ed inh ie ic ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hreplay_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32768 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨inh1, ie1⟩ _
    simp only [slot.b_cx_hreplay_loop1.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals first
      | scalar_tac
      | (have hc : (UScalar.cast .Usize i1).val ≤ i1.val := by
           simp only [UScalar.cast_val_eq]
           exact Nat.mod_le _ _
         scalar_tac)
  · trivial
@[local step]
theorem cx_hreplay_loop2_spec (input : Slice Std.U8) (start : Std.Usize) (bend : Std.Usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (tbl : Slice Std.U32) (bpos : Slice Std.U32) (nb : Std.Usize) (b : Std.Usize) (inh : Array Std.U32 8192#usize) (previous : Std.Usize) (cnt : Std.Usize) (q : Std.Usize) (p : Std.Usize) (hb : b.val < Std.Usize.max) :
    slot.b_cx_hreplay_loop2 input start bend arr ed litc lcost dcs dcb tbl bpos nb b inh previous cnt q p ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hreplay_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.2.2.2.2.2.2.2.val)
    (inv := fun s => s.2.2.2.2.2.1.val < Std.Usize.max)
  · rintro ⟨arr1, litc1, lcost1, dcs1, dcb1, b1, previous1, q1, p1⟩ hb1
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_cx_hreplay_loop2.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · exact hb
@[local step]
theorem cx_hreplay_spec (input : Slice Std.U8) (start : Std.Usize) (bend : Std.Usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (tbl : Slice Std.U32) (bpos : Slice Std.U32) (nb : Std.Usize) :
    slot.b_cx_hreplay input start bend arr ed litc lcost dcs dcb tbl bpos nb ⦃ fun _ => True ⦄ := U20! slot.b_cx_hreplay
set_option hygiene false in
local notation "U28!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32768 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨ed1, e1⟩ _
    simp only [q1__]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem cx_hpolish_loop0_loop0_loop0_spec (cache : Slice Std.U64) (ed : Array Std.U64 32768#usize) (off : Std.Usize) (ec : Std.Usize) (e : Std.Usize) :
    slot.b_cx_hpolish_loop0_loop0_loop0 cache ed off ec e ⦃ fun _ => True ⦄ := U28! slot.b_cx_hpolish_loop0_loop0_loop0 slot.b_cx_hpolish_loop0_loop0_loop0.body
@[local step]
theorem cx_hpolish_loop0_loop0_loop1_spec (bpos : alloc.vec.Vec Std.U32) (nb : Std.Usize) (b : Std.Usize) (start : Std.Usize) (hb : b.val < Std.Usize.max) :
    slot.b_cx_hpolish_loop0_loop0_loop1 bpos nb b start ⦃ fun r => r.val < Std.Usize.max ⦄ := U27! slot.b_cx_hpolish_loop0_loop0_loop1 slot.b_cx_hpolish_loop0_loop0_loop1.body
@[local step]
theorem cx_hpolish_loop0_loop0_loop2_spec (plan : Slice Std.U32) (cand : alloc.vec.Vec Std.U32) (p : Std.Usize) («end» : Std.Usize) :
    slot.b_cx_hpolish_loop0_loop0_loop2 plan cand p «end» ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hpolish_loop0_loop0_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => «end».val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨cand1, p1⟩ _
    simp only [slot.b_cx_hpolish_loop0_loop0_loop2.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
set_option hygiene false in
local notation "U29!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => starts.length - qq9.2.2.2.2.2.2.2.2.2.1.val)
    (inv := fun s => s.2.2.2.2.2.2.2.2.2.2.val < Std.Usize.max)
  · rintro ⟨cand1, arr1, ed1, llf1, df1, litc1, lcost1, dcs1, dcb1, j1, b1⟩ hb1
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    have hstarts : starts.length ≤ Std.Usize.max := Std.Slice.length_ineq starts
    simp only [q1__]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · exact hb)
@[local step]
theorem cx_hpolish_loop0_loop0_spec (input : Slice Std.U8) (plan : Slice Std.U32) (cache : Slice Std.U64) (starts : Slice Std.U32) (sizes : Slice Std.U32) (offsets : Slice Std.U32) (n : Std.Usize) (tbl : alloc.vec.Vec Std.U32) (bpos : alloc.vec.Vec Std.U32) (cand : alloc.vec.Vec Std.U32) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (nb : Std.Usize) (j : Std.Usize) (b : Std.Usize) (hb : b.val < Std.Usize.max) :
    slot.b_cx_hpolish_loop0_loop0 input plan cache starts sizes offsets n tbl bpos cand arr ed llf df litc lcost dcs dcb nb j b ⦃ fun _ => True ⦄ := U29! slot.b_cx_hpolish_loop0_loop0 slot.b_cx_hpolish_loop0_loop0.body
@[local step]
theorem cx_hpolish_loop0_loop1_spec (plan : Slice Std.U32) (n : Std.Usize) (cand : alloc.vec.Vec Std.U32) (p : Std.Usize) :
    slot.b_cx_hpolish_loop0_loop1 plan n cand p ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hpolish_loop0_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => n.val - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨plan1, p1⟩ _
    simp only [slot.b_cx_hpolish_loop0_loop1.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · trivial
set_option hygiene false in
local notation "U30!" q0__:max q1__:max q2__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => q1__ - qq9.2.2.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨plan1, tbl1, fr1, bpos1, cand1, arr1, ed1, llf1, df1, litc1, lcost1, dcs1, dcb1, pi1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    have hstarts : starts.length ≤ Std.Usize.max := Std.Slice.length_ineq starts
    simp only [q2__]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem cx_hpolish_loop0_spec (input : Slice Std.U8) (plan : Slice Std.U32) (cache : Slice Std.U64) (starts : Slice Std.U32) (sizes : Slice Std.U32) (offsets : Slice Std.U32) (n : Std.Usize) (nbmax : Std.Usize) (tbl : alloc.vec.Vec Std.U32) (fr : alloc.vec.Vec Std.U32) (bpos : alloc.vec.Vec Std.U32) (cand : alloc.vec.Vec Std.U32) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (pi : Std.Usize) :
    slot.b_cx_hpolish_loop0 input plan cache starts sizes offsets n nbmax tbl fr bpos cand arr ed llf df litc lcost dcs dcb pi ⦃ fun _ => True ⦄ := U30! slot.b_cx_hpolish_loop0 slot.B_CX_HP.val slot.b_cx_hpolish_loop0.body
@[local step]
theorem cx_hpolish_spec (input : Slice Std.U8) (plan : Slice Std.U32) (cache : Slice Std.U64) (starts : Slice Std.U32) (sizes : Slice Std.U32) (offsets : Slice Std.U32) :
    slot.b_cx_hpolish input plan cache starts sizes offsets ⦃ fun _ => True ⦄ := U20! slot.b_cx_hpolish
@[local step]
theorem cx_hreplay_hfi_loop0_spec (start : Std.Usize) (bpos : Slice Std.U32) (nb : Std.Usize) (b : Std.Usize) (hb : b.val < Std.Usize.max) :
    slot.b_cx_hreplay_hfi_loop0 start bpos nb b ⦃ fun r => r.val < Std.Usize.max ⦄ := U27! slot.b_cx_hreplay_hfi_loop0 slot.b_cx_hreplay_hfi_loop0.body
@[local step]
theorem cx_hreplay_hfi_loop1_spec
  (input : Slice Std.U8) (start : Std.Usize) (bend : Std.Usize)
  (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize)
  (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize)
  (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize)
  (tbl : Slice Std.U32) (bpos : Slice Std.U32) (nb : Std.Usize)
  (inh : Slice Std.U32) (b : Std.Usize) (cnt : Std.Usize) (q : Std.Usize)
  (p : Std.Usize) (hb : b.val < Std.Usize.max) :
    slot.b_cx_hreplay_hfi_loop1 input start bend arr ed litc lcost dcs dcb tbl bpos nb inh b cnt q p ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hreplay_hfi_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 8192 - qq9.2.2.2.2.2.2.2.val)
    (inv := fun s => s.2.2.2.2.2.1.val < Std.Usize.max)
  · rintro ⟨arr1, litc1, lcost1, dcs1, dcb1, b1, q1, p1⟩ hb1
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.b_cx_hreplay_hfi_loop1.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals scalar_tac
  · exact hb
@[local step]
theorem cx_hreplay_hfi_spec
  (input : Slice Std.U8) (start : Std.Usize) (bend : Std.Usize)
  (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize)
  (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize)
  (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize)
  (tbl : Slice Std.U32) (bpos : Slice Std.U32) (nb : Std.Usize)
  (inh : Slice Std.U32) :
    slot.b_cx_hreplay_hfi input start bend arr ed litc lcost dcs dcb tbl bpos nb inh ⦃ fun _ => True ⦄ := U20! slot.b_cx_hreplay_hfi
@[local step]
theorem cx_hpolish_hfi_loop0_loop0_spec
  (cache : Slice Std.U64) (inh : alloc.vec.Vec Std.U32) (start : Std.Usize)
  (off : Std.Usize) (ec : Std.Usize) (e : Std.Usize) (hec : ec.val < 32768) :
    slot.b_cx_hpolish_hfi_loop0_loop0 cache inh start off ec e ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hpolish_hfi_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => ec.val + 1 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨inh1, e1⟩ _
    simp only [slot.b_cx_hpolish_hfi_loop0_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem cx_hpolish_hfi_loop0_spec
  (cache : Slice Std.U64) (starts : Slice Std.U32) (offsets : Slice Std.U32)
  (inh : alloc.vec.Vec Std.U32) (j : Std.Usize) :
    slot.b_cx_hpolish_hfi_loop0 cache starts offsets inh j ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hpolish_hfi_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => starts.length - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨inh1, j1⟩ _
    have hstarts : starts.length ≤ Std.Usize.max := Std.Slice.length_ineq starts
    simp only [slot.b_cx_hpolish_hfi_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
      | (guard_hyp x :~ _ × _ × _ × _ × _; obtain ⟨r1, r2, r3, r4, r5⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _ × _; obtain ⟨r1, r2, r3, r4⟩ := x; try step*)
      | (guard_hyp x :~ _ × _ × _; obtain ⟨r1, r2, r3⟩ := x; try step*)
      | (guard_hyp x :~ _ × _; obtain ⟨r1, r2⟩ := x; try step*)
      | (apply spec_ite_cut <;> intro hc <;> try step*)
      | (apply Std.WP.spec_bind (Pₘ := fun _ => True))
      | (intro y _; repeat (obtain ⟨_, y⟩ : _ × _ := y); try step*))
    all_goals first
      | scalar_tac
      | (have hc : (UScalar.cast .Usize x).val ≤ x.val := by
           simp only [UScalar.cast_val_eq]
           exact Nat.mod_le _ _
         scalar_tac)
  · trivial
@[local step]
theorem cx_hpolish_hfi_loop1_spec
  (n : Std.Usize) (inh : alloc.vec.Vec Std.U32) (pos : Std.Usize)
  (prev : Std.Usize) :
    slot.b_cx_hpolish_hfi_loop1 n inh pos prev ⦃ fun _ => True ⦄ := by
  rw [slot.b_cx_hpolish_hfi_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => n.val - qq9.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨inh1, pos1, prev1⟩ _
    simp only [slot.b_cx_hpolish_hfi_loop1.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem cx_hpolish_hfi_loop2_loop0_loop0_spec
  (cache : Slice Std.U64) (ed : Array Std.U64 32768#usize) (off : Std.Usize)
  (ec : Std.Usize) (e : Std.Usize) :
    slot.b_cx_hpolish_hfi_loop2_loop0_loop0 cache ed off ec e ⦃ fun _ => True ⦄ := U28! slot.b_cx_hpolish_hfi_loop2_loop0_loop0 slot.b_cx_hpolish_hfi_loop2_loop0_loop0.body
@[local step]
theorem cx_hpolish_hfi_loop2_loop0_loop1_spec
  (bpos : alloc.vec.Vec Std.U32) (nb : Std.Usize) (b : Std.Usize)
  (start : Std.Usize) (hb : b.val < Std.Usize.max) :
    slot.b_cx_hpolish_hfi_loop2_loop0_loop1 bpos nb b start ⦃ fun r => r.val < Std.Usize.max ⦄ := U27! slot.b_cx_hpolish_hfi_loop2_loop0_loop1 slot.b_cx_hpolish_hfi_loop2_loop0_loop1.body
@[local step]
theorem cx_hpolish_hfi_loop2_loop0_spec
  (input : Slice Std.U8) (cache : Slice Std.U64) (starts : Slice Std.U32)
  (sizes : Slice Std.U32) (offsets : Slice Std.U32)
  (tbl : alloc.vec.Vec Std.U32) (bpos : alloc.vec.Vec Std.U32)
  (cand : alloc.vec.Vec Std.U32) (arr : Array Std.U64 8192#usize)
  (ed : Array Std.U64 32768#usize) (llf : Array Std.U32 512#usize)
  (df : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize)
  (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize)
  (dcb : Array Std.U32 256#usize) (inh : alloc.vec.Vec Std.U32)
  (nb : Std.Usize) (j : Std.Usize) (b : Std.Usize) (hb : b.val < Std.Usize.max) :
    slot.b_cx_hpolish_hfi_loop2_loop0 input cache starts sizes offsets tbl bpos cand arr ed llf df litc lcost dcs dcb inh nb j b ⦃ fun _ => True ⦄ := U29! slot.b_cx_hpolish_hfi_loop2_loop0 slot.b_cx_hpolish_hfi_loop2_loop0.body
@[local step]
theorem cx_hpolish_hfi_loop2_spec
  (input : Slice Std.U8) (plan : Slice Std.U32) (cache : Slice Std.U64)
  (starts : Slice Std.U32) (sizes : Slice Std.U32) (offsets : Slice Std.U32)
  (n : Std.Usize) (nbmax : Std.Usize) (tbl : alloc.vec.Vec Std.U32)
  (fr : alloc.vec.Vec Std.U32) (bpos : alloc.vec.Vec Std.U32)
  (cand : alloc.vec.Vec Std.U32) (arr : Array Std.U64 8192#usize)
  (ed : Array Std.U64 32768#usize) (llf : Array Std.U32 512#usize)
  (df : Array Std.U32 32#usize) (litc : Array Std.U32 256#usize)
  (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize)
  (dcb : Array Std.U32 256#usize) (inh : alloc.vec.Vec Std.U32)
  (pi : Std.Usize) :
    slot.b_cx_hpolish_hfi_loop2 input plan cache starts sizes offsets n nbmax tbl fr bpos cand arr ed llf df litc lcost dcs dcb inh pi ⦃ fun _ => True ⦄ := U30! slot.b_cx_hpolish_hfi_loop2 slot.B_CX_HP.val slot.b_cx_hpolish_hfi_loop2.body
@[local step]
theorem cx_hpolish_hfi_spec
  (input : Slice Std.U8) (plan : Slice Std.U32) (cache : Slice Std.U64)
  (starts : Slice Std.U32) (sizes : Slice Std.U32) (offsets : Slice Std.U32) :
    slot.b_cx_hpolish_hfi input plan cache starts sizes offsets ⦃ fun _ => True ⦄ := U20! slot.b_cx_hpolish_hfi
@[local step]
theorem h_dp_plan_loop0_loop0_spec (cache : alloc.vec.Vec Std.U64) (ed : Array Std.U64 32768#usize) (ec : Std.Usize) (ei : Std.Usize) :
    slot.b_h_dp_plan_loop0_loop0 cache ed ec ei ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_dp_plan_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => 32768 - qq9.2.val)
    (inv := fun _ => True)
  · rintro ⟨cache1, ei1⟩ _
    simp only [slot.b_h_dp_plan_loop0_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem h_dp_plan_loop0_spec (input : Slice Std.U8) (plan : Slice Std.U32) (kend : Std.Usize) (n : Std.Usize) (polish : Bool) (cache : alloc.vec.Vec Std.U64) (starts : alloc.vec.Vec Std.U32) (sizes : alloc.vec.Vec Std.U32) (offsets : alloc.vec.Vec Std.U32) (head : Array Std.U32 65536#usize) (prev : Array Std.U16 32768#usize) (h3 : Array Std.U32 131072#usize) (arr : Array Std.U64 8192#usize) (ed : Array Std.U64 32768#usize) (llf1 : Array Std.U32 512#usize) (df1 : Array Std.U32 32#usize) (cl : Array Std.U32 16#usize) (cd : Array Std.U32 16#usize) (cb : Array Std.U32 16#usize) (litc : Array Std.U32 256#usize) (lcost : Array Std.U32 512#usize) (dcs : Array Std.U32 256#usize) (dcb : Array Std.U32 256#usize) (scost : Array Std.U32 32#usize) (llf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (pllf : Array Std.U32 512#usize) (pdf : Array Std.U32 32#usize) (tllf : Array Std.U32 512#usize) (tdf : Array Std.U32 32#usize) (st : Array Std.Usize 4#usize) (pos0 : Std.Usize) (blk : Std.Usize) :
    slot.b_h_dp_plan_loop0 input plan kend n polish cache starts sizes offsets head prev h3 arr ed llf1 df1 cl cd cb litc lcost dcs dcb scost llf df pllf pdf tllf tdf st pos0 blk ⦃ fun _ => True ⦄ := by
  rw [slot.b_h_dp_plan_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun qq9 => n.val - qq9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨plan1, polish1, cache1, starts1, sizes1, offsets1, head1, prev1, h31, arr1, ed1, llf11, df11, cl1, cd1, cb1, litc1, lcost1, dcs1, dcb1, scost1, llf2, df2, pllf1, pdf1, tllf1, tdf1, st1, pos01, blk1⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    have hstarts : starts.length ≤ Std.Usize.max := Std.Slice.length_ineq starts
    simp only [slot.b_h_dp_plan_loop0.body]
    try simp only [lift, ite_ok, alloc.vec.Vec.deref_mut, bind_tc_ok]
    step*
    all_goals repeat (first
      | (split <;> (try step*))
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
theorem h_dp_plan_spec (mode : Std.Usize) (input : Slice Std.U8) (plan : Slice Std.U32) (kend : Std.Usize) :
    slot.b_h_dp_plan mode input plan kend ⦃ fun _ => True ⦄ := U23! slot.b_h_dp_plan
@[local step]
theorem hdp_if_spec (mode : Std.Usize) (input : Slice Std.U8) (plan : Slice Std.U32) (on : Std.Usize) (kend : Std.Usize) :
    slot.b_hdp_if mode input plan on kend ⦃ fun _ => True ⦄ := U10! slot.b_hdp_if
@[local step]
theorem mode_gk_spec (mode : Std.Usize) (base : Std.U64) :
    slot.b_mode_gk mode base ⦃ fun _ => True ⦄ := U22! slot.b_mode_gk
@[local step]
theorem champ_spec (mode : Std.Usize) (input : Slice Std.U8) (plan : Slice Std.U32) (gk : Std.U64) (i5 : Std.Usize) :
    slot.b_champ mode input plan gk i5 ⦃ fun _ => True ⦄ := U11! slot.b_champ
@[local step]
theorem champ_if_spec (mode : Std.Usize) (input : Slice Std.U8) (plan : Slice Std.U32) (on : Std.Usize) (gk : Std.U64) (i5 : Std.Usize) :
    slot.b_champ_if mode input plan on gk i5 ⦃ fun _ => True ⦄ := U10! slot.b_champ_if
@[local step]
theorem parse_mode_spec (input : Slice Std.U8) (out : Slice Std.U32) (mode : Std.Usize)
    (hlen : input.length ≤ out.length) :
    slot.b_parse_mode input out mode ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_parse_mode]
  simp only [lift, alloc.vec.Vec.deref_mut, bind_tc_ok]
  step*
  exact ⟨r_post1, r_post2, r_post3⟩
theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.b_parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.b_parse]
  exact parse_mode_spec input out 0#usize hlen
end EB
namespace ED
open Aeneas Aeneas.Std Result ControlFlow
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr Matches ite_ok)
theorem match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.d_match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := U12! slot.d_match_len_loop slot.d_match_len_loop.body
@[local step]
theorem match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.d_match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := U13!
theorem lz64_le (x : Std.U64) : (core.num.U64.leading_zeros x).val ≤ 64 := by
  rw [core.num.U64.leading_zeros]
  simp only [UScalar.val, BitVec.leadingZeros]
  refine le_trans (Nat.mod_le _ _) ?_
  split <;> omega
theorem lz_div8_le (x : Std.U64) (i6 : Std.U32) (i7 : Std.Usize)
    (h6 : i6.val = (core.num.U64.leading_zeros x).val / 8)
    (h7 : i7 = UScalar.cast .Usize i6) : i7.val ≤ 8 := by
  have := lz64_le x
  subst h7
  simp only [U32.cast_Usize_val_eq]
  omega
@[local step]
theorem load64_spec (input : Slice Std.U8) (p : Std.Usize) (hp : p.val + 8 ≤ input.length) :
    slot.d_load64 input p ⦃ fun _ => True ⦄ := by
  rw [slot.d_load64]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  simp only [lift]
  step*
theorem ext_len_loop0_spec (input : Slice Std.U8) (a b cap l0 go0 : Std.Usize)
    (ha : a.val < b.val) (hb : b.val + cap.val ≤ input.length) (hl0 : l0.val ≤ cap.val) :
    slot.d_ext_len_loop0 input a b cap l0 go0 ⦃ fun r => r.1.val ≤ cap.val ⦄ := by
  rw [slot.d_ext_len_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => cap.val - s.1.val + s.2.val)
    (inv := fun s => s.1.val ≤ cap.val)
  · rintro ⟨l, go⟩ hle
    simp only at hle
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_ext_len_loop0.body]
    by_cases hg : go = 1#usize
    · rw [if_pos hg]
      by_cases hlc : l < cap
      · rw [if_pos hlc]
        step*
        all_goals first
          | scalar_tac
          | (have h7 := lz_div8_le x i6 i7 (by rw [i6_post, i5_post]) i7_post
             scalar_tac)
      · rw [if_neg hlc]
        simp
        exact hle
    · rw [if_neg hg]
      simp
      exact hle
  · exact hl0
theorem ext_len_loop1_spec (input : Slice Std.U8) (a b cap l0 go : Std.Usize)
    (ha : a.val < b.val) (hb : b.val + cap.val ≤ input.length) (hl0 : l0.val ≤ cap.val) :
    slot.d_ext_len_loop1 input a b cap l0 go ⦃ fun l => l.val ≤ cap.val ⦄ := by
  rw [slot.d_ext_len_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val)
  · intro l hle
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_ext_len_loop1.body]
    split
    · split
      · step*
      · exact hle
    · exact hle
  · exact hl0
@[local step]
theorem ext_len_spec (input : Slice Std.U8) (a b cap : Std.Usize) :
    slot.d_ext_len input a b cap ⦃ fun l => l.val ≤ cap.val ⦄ := by
  rw [slot.d_ext_len]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  split
  · split
    · step*
      apply Std.WP.spec_bind (ext_len_loop0_spec input a b cap 0#usize 1#usize
        (by scalar_tac) (by scalar_tac) (by simp))
      rintro ⟨l, go⟩ hl
      exact ext_len_loop1_spec input a b cap l go (by scalar_tac) (by scalar_tac) hl
    · simp
  · simp
theorem mem_bound_set {α : Type} {n : Std.Usize} (a : Array α n) (i : Std.Usize) (v : α)
    (P : α → Prop) (ha : ∀ x ∈ a.val, P x) (hv : P v) : ∀ x ∈ (a.set i v).val, P x := by
  intro x hx
  rw [Aeneas.Std.Array.set_val_eq] at hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · exact ha x h
  · exact h ▸ hv
theorem mem_bound_repeat {α : Type} (n : Std.Usize) (v : α) (P : α → Prop) (hv : P v) :
    ∀ x ∈ (Array.repeat n v).val, P x := by
  intro x hx
  rw [Aeneas.Std.Array.repeat_val] at hx
  rw [List.eq_of_mem_replicate hx]
  exact hv
theorem mem_bound_get {α : Type} {n : Std.Usize} (a : Array α n) (P : α → Prop)
    (ha : ∀ x ∈ a.val, P x) (i : Nat) (h : i < a.val.length) : P (a.val[i]) :=
  ha _ (List.getElem_mem h)
theorem cost16_loop_spec (t f : Std.U64) (c : Std.U32) (k : Std.Usize)
    (hc : c.val ≤ 1024 + k.val) (hk : k.val ≤ 16) :
    slot.d_cost16_loop t f c k ⦃ fun r => r.val ≤ 1040 ⦄ := by
  rw [slot.d_cost16_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 16 - s.2.2.val)
    (inv := fun s => s.2.1.val ≤ 1024 + s.2.2.val ∧ s.2.2.val ≤ 16)
  · rintro ⟨f1, c1, k1⟩ ⟨hc1, hk1⟩
    simp only at hc1 hk1
    simp only [slot.d_cost16_loop.body, lift]
    step*
  · exact ⟨hc, hk⟩
@[local step]
theorem cost16_spec (freq total : Std.U32) :
    slot.d_cost16 freq total ⦃ fun r => r.val ≤ 1040 + slot.D_MISS_COST.val ⦄ := by
  rw [slot.d_cost16]
  split
  · step*
  · step*
    have hlz := lz64_le f
    rw [← lzf_post] at hlz
    apply Std.WP.spec_bind (Pₘ := fun (x : Std.U64 × Std.U32) => x.2.val ≤ 1024)
    · split
      · step*
        apply Std.WP.spec_bind (Pₘ := fun (s : Std.U32) => s.val ≤ s0.val)
        · split <;> step*
        · intro s hs
          step*
      · simp
    · rintro ⟨f1, c⟩ hc
      simp only at hc
      apply Std.WP.spec_bind (cost16_loop_spec _ f1 c 0#usize (by simp; omega) (by simp))
      intro c1 hc1
      split <;> step*
@[local step]
theorem dcode_spec (dlo dhi : Array Std.U8 256#usize) (d : Std.Usize) :
    slot.d_dcode dlo dhi d ⦃ fun _ => True ⦄ := by
  rw [slot.d_dcode]
  split
  · apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
    · split <;> step*
    · intro k _
      step*
  · step*
@[local step]
theorem gain_spec (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize) (i l d : Std.Usize)
    (hil : i.val + l.val ≤ Std.Usize.max) :
    slot.d_gain pref lenc dcost dlo dhi i l d ⦃ fun _ => True ⦄ := by
  rw [slot.d_gain]
  simp only [lift]
  step*
@[local step]
theorem push_x_spec (xs : Array Std.U32 131072#usize) (xn : Array Std.U8 32768#usize)
    (dlo dhi : Array Std.U8 256#usize) (i l d : Std.Usize) (hi : i.val ≤ 32768)
    (hl : l.val ≤ 65536) (hd : d.val ≤ 32768) :
    slot.d_push_x xs xn dlo dhi i l d ⦃ fun _ => True ⦄ := by
  rw [slot.d_push_x]
  step*
  apply Std.WP.spec_bind (Pₘ := fun (s : Std.Usize) => s.val ≤ 255)
  · split <;> step*
  · intro s hs
    apply Std.WP.spec_bind (Pₘ := fun (s1 : Std.Usize) => s1.val ≤ 255)
    · split <;> step*
    · intro s1 hs1
      step*
theorem find_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (p i cap pcap : Std.Usize) (xs0 : Array Std.U32 131072#usize) (xn0 : Array Std.U8 32768#usize)
    (bl0 bd0 : Std.Usize) (bg0 : Std.U32) (sl0 sd0 need0 ok1 low cur0 nc0 probes0 : Std.Usize)
    (hok : ok1 = 1#usize → p.val + cap.val ≤ input.length) (hip : i.val ≤ p.val)
    (hi : i.val ≤ 32768) (hcap : cap.val ≤ 258)
    (hlow1 : 1 ≤ low.val) (hlow2 : p.val + 1 ≤ low.val + 32768)
    (hbl : bl0.val ≤ cap.val) (hbd : bd0.val ≤ 32768) :
    slot.d_find_loop input prev pref lenc dcost dlo dhi p i cap pcap xs0 xn0 bl0 bd0 bg0 sl0 sd0
      need0 ok1 low cur0 nc0 probes0 ⦃ fun r => r.2.2.1.val ≤ cap.val ∧ r.2.2.2.1.val ≤ 32768 ⦄ := by
  rw [slot.d_find_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => pcap.val - s.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s => s.2.2.1.val ≤ cap.val ∧ s.2.2.2.1.val ≤ 32768)
  · rintro ⟨xs, xn, bl, bd, bg, sl, sd, need, cur, nc, probes⟩ ⟨hb1, hb2⟩
    simp only at hb1 hb2
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    dsimp only
    delta slot.d_find_loop.body
    by_cases hok1 : ok1 = 1#usize
    · rw [if_pos hok1]
      have hpc := hok hok1
      by_cases hpr : probes < pcap
      · rw [if_pos hpr]
        by_cases hcl : cur ≥ low
        · rw [if_pos hcl]
          by_cases hcp : cur ≤ p
          · rw [if_pos hcp]
            by_cases hnc : need < cap
            · rw [if_pos hnc]
              step*
              apply Std.WP.spec_bind
                (Pₘ := fun (x : (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize) ×
                  Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize ×
                  Std.Usize) => x.2.2.1.val ≤ cap.val ∧ x.2.2.2.1.val ≤ 32768)
              · split
                case isTrue =>
                  step*
                  apply Std.WP.spec_bind
                    (Pₘ := fun (_ : (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize)) => True)
                  · repeat' split
                    all_goals step*
                  · rintro ⟨x3, n3⟩ _
                    simp only [ite_ok]
                    step*
                    refine ⟨?_, ?_⟩ <;> split <;> scalar_tac
                case isFalse => exact ⟨hb1, hb2⟩
              · rintro ⟨x2, n2, b2, d2, g2, s2, e2, m2⟩ ⟨h1, h2⟩
                simp only at h1 h2
                step*
            · rw [if_neg hnc]; simp; exact ⟨hb1, hb2⟩
          · rw [if_neg hcp]; simp; exact ⟨hb1, hb2⟩
        · rw [if_neg hcl]; simp; exact ⟨hb1, hb2⟩
      · rw [if_neg hpr]; simp; exact ⟨hb1, hb2⟩
    · rw [if_neg hok1]; simp; exact ⟨hb1, hb2⟩
  · exact ⟨hbl, hbd⟩
@[local step]
theorem find_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (p i cap start c3 floor pcap : Std.Usize) (xs : Array Std.U32 131072#usize)
    (xn : Array Std.U8 32768#usize) (hip : i.val ≤ p.val) (hi : i.val ≤ 32768)
    (hcap : cap.val ≤ 258) :
    slot.d_find input prev pref lenc dcost dlo dhi p i cap start c3 floor pcap xs xn
      ⦃ fun r => r.1.1.val ≤ cap.val ∧ r.1.2.1.val ≤ 32768 ⦄ := by
  rw [slot.d_find]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind
    (Pₘ := fun (o : Std.Usize) => o = 1#usize → p.val + cap.val ≤ input.length)
  · split
    · step*
    · intro h; simp at h
  · intro ok1 hok
    apply Std.WP.spec_bind
      (Pₘ := fun (x : (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize) ×
        Std.Usize × Std.Usize × Std.U32 × Std.Usize) =>
        x.2.2.1.val ≤ cap.val ∧ x.2.2.2.1.val ≤ 32768)
    · split
      case isTrue hok1 =>
        have hpc := hok hok1
        split
        · split
          · step*
            all_goals
              apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U32 131072#usize) ×
                (Array Std.U8 32768#usize)) => True)
              · repeat' split
                all_goals step*
              · rintro ⟨a, b⟩ _
                step*
          · simp
        · simp
      case isFalse => simp
    · rintro ⟨x1, n1, bl, bd, bg, need⟩ ⟨h1, h2⟩
      apply Std.WP.spec_bind
        (Pₘ := fun (low : Std.Usize) => 1 ≤ low.val ∧ p.val + 1 ≤ low.val + 32768)
      · split <;> step*
      · intro low ⟨hlow1, hlow2⟩
        step*
        apply Std.WP.spec_bind (find_loop_spec input prev pref lenc dcost dlo dhi p i cap pcap
          x1 n1 bl bd bg 0#usize 0#usize need ok1 low start _ 0#usize hok hip hi hcap hlow1 hlow2 h1 h2)
        rintro ⟨x2, n2, b2, d2, g2, s2, e2⟩ ⟨h3, h4⟩
        simp only at h3 h4
        step*
theorem find_in_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (p i cap : Std.Usize) (xs0 : Array Std.U32 131072#usize) (xn0 : Array Std.U8 32768#usize)
    (bl0 bd0 : Std.Usize) (bg0 : Std.U32) (sl0 sd0 need0 ok1 low cur0 nc0 probes0 : Std.Usize)
    (hok : ok1 = 1#usize → p.val + cap.val ≤ input.length) (hip : i.val ≤ p.val)
    (hi : i.val ≤ 32768) (hcap : cap.val ≤ 258)
    (hlow1 : 1 ≤ low.val) (hlow2 : p.val + 1 ≤ low.val + 32768)
    (hbl : bl0.val ≤ cap.val) (hbd : bd0.val ≤ 32768) :
    slot.d_find_in_loop input prev pref lenc dcost dlo dhi p i cap xs0 xn0 bl0 bd0 bg0 sl0 sd0
      need0 ok1 low cur0 nc0 probes0 ⦃ fun r => r.2.2.1.val ≤ cap.val ∧ r.2.2.2.1.val ≤ 32768 ⦄ := by
  rw [slot.d_find_in_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.D_INNER_D.val - s.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s => s.2.2.1.val ≤ cap.val ∧ s.2.2.2.1.val ≤ 32768)
  · rintro ⟨xs, xn, bl, bd, bg, sl, sd, need, cur, nc, probes⟩ ⟨hb1, hb2⟩
    simp only at hb1 hb2
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    dsimp only
    delta slot.d_find_in_loop.body
    by_cases hok1 : ok1 = 1#usize
    · rw [if_pos hok1]
      have hpc := hok hok1
      by_cases hpr : probes < slot.D_INNER_D
      · rw [if_pos hpr]
        by_cases hcl : cur ≥ low
        · rw [if_pos hcl]
          by_cases hcp : cur ≤ p
          · rw [if_pos hcp]
            by_cases hnc : need < cap
            · rw [if_pos hnc]
              step*
              apply Std.WP.spec_bind
                (Pₘ := fun (x : (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize) ×
                  Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize ×
                  Std.Usize) => x.2.2.1.val ≤ cap.val ∧ x.2.2.2.1.val ≤ 32768)
              · split
                case isTrue =>
                  step*
                  apply Std.WP.spec_bind
                    (Pₘ := fun (_ : (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize)) => True)
                  · repeat' split
                    all_goals step*
                  · rintro ⟨x3, n3⟩ _
                    simp only [ite_ok]
                    step*
                    refine ⟨?_, ?_⟩ <;> split <;> scalar_tac
                case isFalse => exact ⟨hb1, hb2⟩
              · rintro ⟨x2, n2, b2, d2, g2, s2, e2, m2⟩ ⟨h1, h2⟩
                simp only at h1 h2
                step*
            · rw [if_neg hnc]; simp; exact ⟨hb1, hb2⟩
          · rw [if_neg hcp]; simp; exact ⟨hb1, hb2⟩
        · rw [if_neg hcl]; simp; exact ⟨hb1, hb2⟩
      · rw [if_neg hpr]; simp; exact ⟨hb1, hb2⟩
    · rw [if_neg hok1]; simp; exact ⟨hb1, hb2⟩
  · exact ⟨hbl, hbd⟩
@[local step]
theorem find_in_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (p i cap start c3 floor : Std.Usize) (xs : Array Std.U32 131072#usize)
    (xn : Array Std.U8 32768#usize) (hip : i.val ≤ p.val) (hi : i.val ≤ 32768)
    (hcap : cap.val ≤ 258) :
    slot.d_find_in input prev pref lenc dcost dlo dhi p i cap start c3 floor xs xn
      ⦃ fun r => r.1.1.val ≤ cap.val ∧ r.1.2.1.val ≤ 32768 ⦄ := by
  rw [slot.d_find_in]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind
    (Pₘ := fun (o : Std.Usize) => o = 1#usize → p.val + cap.val ≤ input.length)
  · split
    · step*
    · intro h; simp at h
  · intro ok1 hok
    apply Std.WP.spec_bind
      (Pₘ := fun (x : (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize) ×
        Std.Usize × Std.Usize × Std.U32 × Std.Usize) =>
        x.2.2.1.val ≤ cap.val ∧ x.2.2.2.1.val ≤ 32768)
    · split
      case isTrue hok1 =>
        have hpc := hok hok1
        split
        · split
          · step*
            all_goals
              apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U32 131072#usize) ×
                (Array Std.U8 32768#usize)) => True)
              · repeat' split
                all_goals step*
              · rintro ⟨a, b⟩ _
                step*
          · simp
        · simp
      case isFalse => simp
    · rintro ⟨x1, n1, bl, bd, bg, need⟩ ⟨h1, h2⟩
      apply Std.WP.spec_bind
        (Pₘ := fun (low : Std.Usize) => 1 ≤ low.val ∧ p.val + 1 ≤ low.val + 32768)
      · split <;> step*
      · intro low ⟨hlow1, hlow2⟩
        step*
        apply Std.WP.spec_bind (find_in_loop_spec input prev pref lenc dcost dlo dhi p i cap
          x1 n1 bl bd bg 0#usize 0#usize need ok1 low start _ 0#usize hok hip hi hcap hlow1 hlow2 h1 h2)
        rintro ⟨x2, n2, b2, d2, g2, s2, e2⟩ ⟨h3, h4⟩
        simp only at h3 h4
        step*
@[local step]
theorem insert_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize) (p : Std.Usize)
    (hp : p.val + 4 ≤ input.length) :
    slot.d_insert input head4 prev near p ⦃ fun _ => True ⦄ := by
  rw [slot.d_insert]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  simp only [lift]
  step*
theorem prefix_loop_spec (input : Slice Std.U8) (litc : Array Std.U32 256#usize)
    (pref : Array Std.U32 65536#usize) (p0 blen n k : Std.Usize) (acc : Std.U32)
    (hn : n.val = input.length) :
    slot.d_prefix_loop input litc pref p0 blen n k acc ⦃ fun _ => True ⦄ := by
  rw [slot.d_prefix_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => blen.val - s.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨pf, kk, ac⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_prefix_loop.body, lift]
    step*
  · trivial
@[local step]
theorem prefix_spec (input : Slice Std.U8) (litc : Array Std.U32 256#usize)
    (pref : Array Std.U32 65536#usize) (p0 blen : Std.Usize) :
    slot.d_prefix input litc pref p0 blen ⦃ fun _ => True ⦄ := by
  rw [slot.d_prefix]
  step*
  exact prefix_loop_spec input litc _ p0 blen _ 0#usize 0#u32 (by simp)
theorem min258_le (rest : Std.Usize) : (if rest < 258#usize then rest else 258#usize).val ≤ 258 := by
  split <;> scalar_tac
theorem commit_loop_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (c1l c1d c2l c2d : Array Std.U16 32768#usize) (xs : Array Std.U32 131072#usize)
    (xn : Array Std.U8 32768#usize) (pref : Array Std.U32 65536#usize)
    (lenc : Array Std.U32 512#usize) (dcost : Array Std.U32 32#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 q l d blen n : Std.Usize) (has4 : Bool)
    (lim4 k : Std.Usize) (hn : n.val = input.length)
    (hq : p0.val + q.val + l.val ≤ input.length) (hb : blen.val ≤ 32768)
    (hlim : has4 = true → lim4.val + 4 ≤ input.length) :
    slot.d_commit_loop input head4 prev near c1l c1d c2l c2d xs xn pref lenc dcost dlo dhi p0 q l d
      blen n has4 lim4 k ⦃ fun _ => True ⦄ := by
  rw [slot.d_commit_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => l.val - s.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s => s.2.2.2.2.2.2.2.2.2.1 = true → lim4.val + 4 ≤ input.length)
  · rintro ⟨hd, pv, nr, a1, a2, a3, a4, xs1, xn1, h4, kk⟩ hinv
    simp only at hinv
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_commit_loop.body]
    by_cases hkl : kk < l
    · rw [if_pos hkl]
      by_cases hl : l ≤ 258#usize
      · rw [if_pos hl]
        step*
        apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 65536#usize) ×
          (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) ×
          (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
          (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
          (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize) × Bool) =>
            x.2.2.2.2.2.2.2.2.2 = h4)
        · by_cases hk2 : kk ≥ 2#usize
          · rw [if_pos hk2]
            step*
            apply Std.WP.spec_bind (Pₘ := fun (kp : Std.Usize) =>
              kp = 1#usize → p.val + 4 ≤ input.length)
            · split
              · have h4l := hinv (by assumption)
                split
                · step*
                · simp
              · simp
            · intro keep hkp
              apply Std.WP.spec_bind (Pₘ := fun _ => True)
              · by_cases hkeep : keep = 1#usize
                · rw [if_pos hkeep]
                  have hp4 := hkp hkeep
                  step*
                  all_goals first
                  | (obtain ⟨r0, c3⟩ := r
                     have hcap := min258_le rest
                     simp only [ite_ok]
                     step*
                     apply Std.WP.spec_bind (Pₘ := fun _ => True)
                     · repeat' split
                       all_goals step*
                     · rintro ⟨x, y, z, w, u, v⟩ _
                       step*)
                  | (obtain ⟨r0, c3⟩ := r
                     apply Std.WP.spec_bind (Pₘ := fun _ => True)
                     · simp only [ite_ok]
                       repeat' split
                       all_goals step*
                       all_goals
                         apply Std.WP.spec_bind (Pₘ := fun _ => True)
                         · repeat' split
                           all_goals step*
                         · rintro ⟨x, y⟩ _
                           step*
                     · rintro ⟨x, y, z, w, u, v, t⟩ _
                       step*)
                · rw [if_neg hkeep]
                  step*
              · rintro ⟨x, y, z, u, v, w, t, a, b⟩ _
                step*
          · rw [if_neg hk2]
            step*
        · rintro ⟨hd1, pv1, nr1, c11, c12, c21, c22, x1, n1, h41⟩ hh
          simp only at hh
          step*
      · rw [if_neg hl]; simp
    · rw [if_neg hkl]; simp
  · exact hlim
@[local step]
theorem commit_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (c1l c1d c2l c2d : Array Std.U16 32768#usize) (xs : Array Std.U32 131072#usize)
    (xn : Array Std.U8 32768#usize) (pref : Array Std.U32 65536#usize)
    (lenc : Array Std.U32 512#usize) (dcost : Array Std.U32 32#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 q l d blen : Std.Usize)
    (hq : p0.val + q.val + l.val ≤ input.length) (hb : blen.val ≤ 32768) :
    slot.d_commit input head4 prev near c1l c1d c2l c2d xs xn pref lenc dcost dlo dhi p0 q l d blen
      ⦃ fun _ => True ⦄ := by
  rw [slot.d_commit]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (Pₘ := fun (r : Bool × Std.Usize) =>
    r.1 = true → r.2.val + 4 ≤ input.length)
  · split
    · step*
    · simp
  · rintro ⟨h4, l4⟩ hl
    step*
    exact commit_loop_spec input head4 prev near _ _ c2l c2d xs xn pref lenc dcost dlo dhi p0 q l d
      blen (Slice.len input) h4 l4 1#usize (by simp) hq hb hl
theorem extend_back_loop_spec (input : Slice Std.U8) (c2l c2d : Array Std.U16 32768#usize)
    (q l d n p j go : Std.Usize) (hn : n.val = input.length) (hq : q.val ≤ p.val)
    (hl : l.val ≤ 258) (hd : d.val ≤ 32768) :
    slot.d_extend_back_loop input c2l c2d q l d n p j go ⦃ fun _ => True ⦄ := by
  rw [slot.d_extend_back_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.D_BK.val + 1 - s.2.2.1.val + s.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨a, b, jj, gg⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_extend_back_loop.body, lift]
    step*
  · trivial
@[local step]
theorem extend_back_spec (input : Slice Std.U8) (c2l c2d : Array Std.U16 32768#usize)
    (p0 q l d : Std.Usize) (hq : p0.val + q.val ≤ input.length) (hl : l.val ≤ 258)
    (hd : d.val ≤ 32768) :
    slot.d_extend_back input c2l c2d p0 q l d ⦃ fun _ => True ⦄ := by
  rw [slot.d_extend_back]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  exact extend_back_loop_spec input c2l c2d q l d _ _ 1#usize 1#usize (by simp)
    (by scalar_tac) hl hd
theorem skip_loop_spec (c1l c2l : Array Std.U16 32768#usize) (xn : Array Std.U8 32768#usize)
    (blen i s : Std.Usize) :
    slot.d_skip_loop c1l c2l xn blen i s ⦃ fun _ => True ⦄ := by
  rw [slot.d_skip_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun st => slot.D_SKIPN.val - st.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨a, b, c, ii, ss⟩ _
    simp only [slot.d_skip_loop.body]
    step*
  · trivial
@[local step]
theorem skip_spec (c1l c2l : Array Std.U16 32768#usize) (xn : Array Std.U8 32768#usize)
    (i0 blen : Std.Usize) :
    slot.d_skip c1l c2l xn i0 blen ⦃ fun _ => True ⦄ :=
  skip_loop_spec c1l c2l xn blen i0 0#usize
theorem lazy_loop_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (c1l c1d c2l c2d : Array Std.U16 32768#usize) (xs : Array Std.U32 131072#usize)
    (xn : Array Std.U8 32768#usize) (p0 blen long n : Std.Usize) (has4 : Bool)
    (lim4 pl pd : Std.Usize) (pg : Std.U32) (psl psd miss i steps : Std.Usize)
    (hn : n.val = input.length) (hlim : has4 = true → lim4.val + 4 ≤ input.length)
    (hpl : pl.val ≤ 258) (hpd : pd.val ≤ 32768)
    (hpi : 3 ≤ pl.val → 1 ≤ i.val ∧ pl.val + i.val ≤ blen.val + 1) :
    slot.d_lazy_loop input head4 prev near pref lenc dcost dlo dhi c1l c1d c2l c2d xs xn p0 blen
      long n has4 lim4 pl pd pg psl psd miss i steps ⦃ fun _ => True ⦄ := by
  rw [slot.d_lazy_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 32768 - s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s => s.2.2.2.2.2.2.2.2.2.1.val ≤ 258 ∧ s.2.2.2.2.2.2.2.2.2.2.1.val ≤ 32768 ∧
      (3 ≤ s.2.2.2.2.2.2.2.2.2.1.val → 1 ≤ s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ∧
        s.2.2.2.2.2.2.2.2.2.1.val + s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ≤ blen.val + 1))
  · rintro ⟨hd, pv, nr, a1, a2, a3, a4, xs0, xn0, l0, d0, g0, sl0, sd0, ms, ii, st⟩
      ⟨hl0, hd0, hli⟩
    simp only at hl0 hd0 hli
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    dsimp only
    rw [slot.d_lazy_loop.body]
    by_cases hib : ii < blen
    · rw [if_pos hib]
      step*
      apply Std.WP.spec_bind (Pₘ := fun (cap : Std.Usize) => cap.val ≤ rest.val ∧ cap.val ≤ 258)
      · split <;> step*
      intro cap ⟨hcr, hc258⟩
      step*
      apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 65536#usize) ×
        (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) ×
        (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize) × Std.Usize × Std.Usize ×
        Std.U32 × Std.Usize × Std.Usize) =>
          x.2.2.2.2.2.1.val ≤ cap.val ∧ x.2.2.2.2.2.2.1.val ≤ 32768)
      · split
        · split
          · have h4l := hlim (by assumption)
            step*
            apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
            · split <;> step*
            intro floor _
            simp only [ite_ok]
            obtain ⟨i3, i4⟩ := r
            step*
            apply Std.WP.spec_bind (Pₘ := fun _ => True)
            · split <;> step*
            · intro a _
              step*
              all_goals first | (constructor <;> assumption) | scalar_tac
          · simp
        · simp
      rintro ⟨hd1, pv1, nr1, xs1, xn1, cl, cd, cg, csl, csd⟩ ⟨hcl, hcd⟩
      simp only at hcl hcd
      step*
      apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 65536#usize) ×
          (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) × (Array Std.U16 32768#usize) ×
          (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
          (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize) ×
          Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize × Std.Usize × Std.Usize) =>
        x.2.2.2.2.2.2.2.2.2.1.val ≤ 258 ∧ x.2.2.2.2.2.2.2.2.2.2.1.val ≤ 32768 ∧
        (3 ≤ x.2.2.2.2.2.2.2.2.2.1.val → 1 ≤ x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ∧
          x.2.2.2.2.2.2.2.2.2.1.val + x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ≤ blen.val + 1))
      · by_cases hl3 : l0 ≥ 3#usize
        · rw [if_pos hl3]
          by_cases hi1 : ii ≥ 1#usize
          · rw [if_pos hi1]
            apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 65536#usize) ×
                (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) ×
                (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
                (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
                (Array Std.U32 131072#usize) × (Array Std.U8 32768#usize) ×
                Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize × Std.Usize) =>
              x.2.2.2.2.2.2.2.2.2.1.val ≤ 258 ∧ x.2.2.2.2.2.2.2.2.2.2.1.val ≤ 32768 ∧
              (3 ≤ x.2.2.2.2.2.2.2.2.2.1.val → 1 ≤ x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ∧
                x.2.2.2.2.2.2.2.2.2.1.val + x.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ≤ blen.val + 1))
            · by_cases hc3 : cl ≥ 3#usize
              · rw [if_pos hc3]
                by_cases hg : cg > g0
                · rw [if_pos hg]
                  apply Std.WP.spec_bind (Pₘ := fun _ => True)
                  · split <;> step*
                  · rintro ⟨x, y⟩ _
                    step*
                · rw [if_neg hg]
                  step*
                  apply Std.WP.spec_bind (Pₘ := fun _ => True)
                  · repeat' split
                    all_goals step*
                  rintro ⟨x, y⟩ _
                  apply Std.WP.spec_bind (Pₘ := fun _ => True)
                  · repeat' split
                    all_goals step*
                  rintro ⟨x2, y2⟩ _
                  apply Std.WP.spec_bind (Pₘ := fun _ => True)
                  · repeat' split
                    all_goals step*
                  rintro ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ _
                  step*
              · rw [if_neg hc3]
                step*
                apply Std.WP.spec_bind (Pₘ := fun _ => True)
                · repeat' split
                  all_goals step*
                rintro ⟨x, y⟩ _
                apply Std.WP.spec_bind (Pₘ := fun _ => True)
                · repeat' split
                  all_goals step*
                rintro ⟨x2, y2⟩ _
                apply Std.WP.spec_bind (Pₘ := fun _ => True)
                · repeat' split
                  all_goals step*
                rintro ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ _
                step*
            · rintro ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩
                ⟨h1, h2, h3⟩
              simp only at h1 h2 h3
              step*
          · rw [if_neg hi1]
            exfalso
            have := hli (by scalar_tac)
            scalar_tac
        · rw [if_neg hl3]
          apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U16 32768#usize) ×
            (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
            (Array Std.U8 32768#usize) × Std.Usize × Std.Usize × Std.U32 × Std.Usize ×
            Std.Usize × Std.Usize × Std.Usize) =>
            x.2.2.2.2.1.val ≤ 258 ∧ x.2.2.2.2.2.1.val ≤ 32768 ∧
            (3 ≤ x.2.2.2.2.1.val → 1 ≤ x.2.2.2.2.2.2.2.2.2.2.val ∧
              x.2.2.2.2.1.val + x.2.2.2.2.2.2.2.2.2.2.val ≤ blen.val + 1))
          · split
            · step*
              refine ⟨by scalar_tac, by scalar_tac, fun _ => ⟨by scalar_tac, by scalar_tac⟩⟩
            · apply Std.WP.spec_bind (Pₘ := fun _ => True)
              · repeat' split
                all_goals step*
              rintro ⟨x0, y0⟩ _
              step*
              apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
              · split <;> step*
              intro miss2 _
              apply Std.WP.spec_bind (Pₘ := fun _ => True)
              · repeat' split
                all_goals step*
              rintro ⟨x, y, z, w⟩ _
              step*
          · rintro ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ ⟨h1, h2, h3⟩
            simp only at h1 h2 h3
            step*
      · rintro ⟨hd2, pv2, nr2, b1, b2, b3, b4, xs2, xn2, pl1, pd1, pg1, psl1, psd1, ms1, i1⟩
          ⟨h1, h2, h3⟩
        simp only at h1 h2 h3
        step*
    · rw [if_neg hib]
      step*
  · exact ⟨hpl, hpd, hpi⟩
@[local step]
theorem lazy_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (c1l c1d c2l c2d : Array Std.U16 32768#usize) (xs : Array Std.U32 131072#usize)
    (xn : Array Std.U8 32768#usize) (p0 blen long : Std.Usize) :
    slot.d_lazy input head4 prev near pref lenc dcost dlo dhi c1l c1d c2l c2d xs xn p0 blen long
      ⦃ fun _ => True ⦄ := by
  rw [slot.d_lazy]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (Pₘ := fun (r : Bool × Std.Usize) =>
    r.1 = true → r.2.val + 4 ≤ input.length)
  · split
    · step*
    · simp
  · rintro ⟨h4, l4⟩ hl
    exact lazy_loop_spec input head4 prev near pref lenc dcost dlo dhi c1l c1d c2l c2d xs xn p0
      blen long _ h4 l4 0#usize 0#usize 0#u32 0#usize 0#usize 0#usize 0#usize 0#usize (by simp)
      hl (by simp) (by simp) (by simp)
theorem relax_run_loop_spec (cost : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (bend : Array Std.U16 512#usize) (j hi : Std.Usize) (dcs best0 : Std.U32)
    (bl0 l0 : Std.Usize) (hj : j.val ≤ 32768) :
    slot.d_relax_run_loop cost lenc bend j hi dcs best0 bl0 l0 ⦃ fun _ => True ⦄ := by
  rw [slot.d_relax_run_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 259 - s.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨best, bl, l⟩ _
    simp only [slot.d_relax_run_loop.body, lift, ite_ok]
    step*
    all_goals first
      | scalar_tac
      | (repeat' split <;> step*)
  · trivial
@[local step]
theorem relax_run_spec (cost : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (bend : Array Std.U16 512#usize) (j lo hi : Std.Usize) (dcs best0 : Std.U32)
    (bl0 : Std.Usize) (hj : j.val ≤ 32768) :
    slot.d_relax_run cost lenc bend j lo hi dcs best0 bl0 ⦃ fun _ => True ⦄ :=
  relax_run_loop_spec cost lenc bend j hi dcs best0 bl0 lo hj
set_option hygiene false in
local notation "U31!" q0__:max q1__:max q2__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat
    (measure := fun st => q1__ - st.2.2.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨b0, l0, d0, s0, o0⟩ _
    simp only [q2__, lift, ite_ok]
    step*
    all_goals
      apply Std.WP.spec_bind (Pₘ := fun _ => True)
      · repeat' split
        all_goals step*
      · rintro ⟨b1, l1, d1⟩ _
        step*
  · trivial)
@[local step]
theorem backward_loop0_loop0_spec (xs : Array Std.U32 131072#usize)
    (cost : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (cheap j xc rest : Std.Usize) (best : Std.U32)
    (bl bdd s lo : Std.Usize) (hj : j.val ≤ 32768) :
    slot.d_backward_loop0_loop0 xs cost lenc dcost bend dlo dhi cheap j xc rest best bl bdd s lo
      ⦃ fun _ => True ⦄ := U31! slot.d_backward_loop0_loop0 slot.D_NX.val slot.d_backward_loop0_loop0.body
@[local step]
theorem backward_loop0_loop1_spec (xs : Array Std.U32 131072#usize)
    (cost : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (cheap j xc rest : Std.Usize) (best : Std.U32)
    (bl bdd s lo : Std.Usize) (hj : j.val ≤ 32768) :
    slot.d_backward_loop0_loop1 xs cost lenc dcost bend dlo dhi cheap j xc rest best bl bdd s lo
      ⦃ fun _ => True ⦄ := U31! slot.d_backward_loop0_loop1 slot.D_NX.val slot.d_backward_loop0_loop1.body
@[local step]
theorem backward_loop0_loop2_spec (xs : Array Std.U32 131072#usize)
    (cost : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (cheap j xc rest : Std.Usize) (best : Std.U32)
    (bl bdd s lo : Std.Usize) (hj : j.val ≤ 32768) :
    slot.d_backward_loop0_loop2 xs cost lenc dcost bend dlo dhi cheap j xc rest best bl bdd s lo
      ⦃ fun _ => True ⦄ := U31! slot.d_backward_loop0_loop2 slot.D_NX.val slot.d_backward_loop0_loop2.body
theorem backward_loop0_spec (input : Slice Std.U8) (c1l c1d c2l c2d : Array Std.U16 32768#usize)
    (xs : Array Std.U32 131072#usize) (xn : Array Std.U8 32768#usize)
    (cost : Array Std.U32 65536#usize)
    (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 blen cheap : Std.Usize) (cn : Std.U32) (j : Std.Usize)
    (hb : blen.val ≤ 32768) (hpb : p0.val + blen.val ≤ input.length) (hj : j.val ≤ blen.val) :
    slot.d_backward_loop0 input c1l c1d c2l c2d xs xn cost litc lenc dcost bend dlo dhi
      p0 blen cheap cn j ⦃ fun _ => True ⦄ := by
  rw [slot.d_backward_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => s.2.2.2.2.val)
    (inv := fun s => s.2.2.2.2.val ≤ blen.val)
  · rintro ⟨cl, cd, cs, cc, jj⟩ hjj
    simp only at hjj
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_backward_loop0.body, lift, ite_ok]
    step*
    all_goals
      apply Std.WP.spec_bind (Pₘ := fun (_ : Std.U32 × Std.Usize × Std.Usize) => True)
      · repeat' split
        all_goals step*
        all_goals
          apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
          · split <;> step*
          intro f _
          step*
      rintro ⟨b, l, d⟩ _
      step*
      apply Std.WP.spec_bind (Pₘ := fun (_ : Std.U32 × Std.Usize × Std.Usize) => True)
      · repeat' split
        all_goals step*
        all_goals
          apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
          · split <;> step*
          intro f _
          step*
      rintro ⟨b, l, d⟩ _
      step*
      split <;> step*
  · exact hj
@[local step]
theorem backward_spec (input : Slice Std.U8) (c1l c1d c2l c2d : Array Std.U16 32768#usize)
    (xs : Array Std.U32 131072#usize) (xn : Array Std.U8 32768#usize)
    (cost : Array Std.U32 65536#usize)
    (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 blen cheap : Std.Usize) :
    slot.d_backward input c1l c1d c2l c2d xs xn cost litc lenc dcost bend dlo dhi p0 blen cheap
      ⦃ fun _ => True ⦄ := by
  rw [slot.d_backward]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  exact backward_loop0_spec input c1l c1d c2l c2d xs xn _ litc lenc dcost bend dlo dhi
    p0 blen cheap 0#u32 blen (by scalar_tac) (by scalar_tac) (le_refl _)
theorem count_loop0_spec (lf olf : Array Std.U32 512#usize) (half s : Std.Usize) :
    slot.d_count_loop0 lf olf half s ⦃ fun _ => True ⦄ := by
  rw [slot.d_count_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 512 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_count_loop0.body]
    split
    · apply Std.WP.spec_bind (Pₘ := fun (_ : Std.U32) => True)
      · split <;> step*
      · intro v _
        step*
    · step*
  · trivial
theorem count_loop1_spec (df odf : Array Std.U32 32#usize) (half s : Std.Usize) :
    slot.d_count_loop1 df odf half s ⦃ fun _ => True ⦄ := by
  rw [slot.d_count_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 32 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_count_loop1.body]
    split
    · apply Std.WP.spec_bind (Pₘ := fun (_ : Std.U32) => True)
      · split <;> step*
      · intro v _
        step*
    · step*
  · trivial
theorem count_loop2_spec (input : Slice Std.U8) (chl chd : Array Std.U16 32768#usize)
    (lf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (lcode : Array Std.U8 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 blen n k : Std.Usize)
    (hn : n.val = input.length) (hb : blen.val ≤ 32768) :
    slot.d_count_loop2 input chl chd lf df lcode dlo dhi p0 blen n k ⦃ fun _ => True ⦄ := by
  rw [slot.d_count_loop2]
  apply Std.loop.spec_decr_nat (measure := fun s => blen.val - s.2.2.val) (inv := fun _ => True)
  · rintro ⟨a, b, kk⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_count_loop2.body, lift]
    step*
    all_goals scalar_tac
  · trivial
@[local step]
theorem count_spec (input : Slice Std.U8) (chl chd : Array Std.U16 32768#usize)
    (lf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (lcode : Array Std.U8 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (olf : Array Std.U32 512#usize)
    (odf : Array Std.U32 32#usize) (half p0 blen : Std.Usize) (hb : blen.val ≤ 32768) :
    slot.d_count input chl chd lf df lcode dlo dhi olf odf half p0 blen ⦃ fun _ => True ⦄ := by
  rw [slot.d_count]
  apply Std.WP.spec_bind (count_loop0_spec lf olf half 0#usize)
  intro lf1 _
  apply Std.WP.spec_bind (count_loop1_spec df odf half 0#usize)
  intro df1 _
  apply Std.WP.spec_bind (count_loop2_spec input chl chd lf1 df1 lcode dlo dhi p0 blen _
    0#usize (by simp) hb)
  rintro ⟨lf2, df2⟩ _
  simp only [lift]
  step*
theorem keep_loop0_spec (lf olf : Array Std.U32 512#usize) (s : Std.Usize) :
    slot.d_keep_loop0 lf olf s ⦃ fun _ => True ⦄ := by
  rw [slot.d_keep_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 512 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_keep_loop0.body]
    step*
  · trivial
theorem keep_loop1_spec (df odf : Array Std.U32 32#usize) (s : Std.Usize) :
    slot.d_keep_loop1 df odf s ⦃ fun _ => True ⦄ := by
  rw [slot.d_keep_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 32 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_keep_loop1.body]
    step*
  · trivial
@[local step]
theorem keep_spec (lf olf : Array Std.U32 512#usize) (df odf : Array Std.U32 32#usize) :
    slot.d_keep lf df olf odf ⦃ fun _ => True ⦄ := by
  rw [slot.d_keep]
  apply Std.WP.spec_bind (keep_loop0_spec lf olf 0#usize)
  intro a _
  apply Std.WP.spec_bind (keep_loop1_spec df odf 0#usize)
  intro b _
  step*
theorem mix_loop0_spec (olf lz pdp plz lf : Array Std.U32 512#usize) (s : Std.Usize) :
    slot.d_mix_loop0 olf lz pdp plz lf s ⦃ fun _ => True ⦄ := by
  rw [slot.d_mix_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 512 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_mix_loop0.body, lift, ite_ok]
    step*
  · trivial
theorem mix_loop1_spec (odf lzd pdpd plzd df : Array Std.U32 32#usize) (s : Std.Usize) :
    slot.d_mix_loop1 odf lzd pdpd plzd df s ⦃ fun _ => True ⦄ := by
  rw [slot.d_mix_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 32 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_mix_loop1.body, lift, ite_ok]
    step*
  · trivial
@[local step]
theorem mix_spec (olf : Array Std.U32 512#usize) (odf : Array Std.U32 32#usize)
    (lz : Array Std.U32 512#usize) (lzd : Array Std.U32 32#usize)
    (pdp : Array Std.U32 512#usize) (pdpd : Array Std.U32 32#usize)
    (plz : Array Std.U32 512#usize) (plzd : Array Std.U32 32#usize)
    (lf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) :
    slot.d_mix olf odf lz lzd pdp pdpd plz plzd lf df ⦃ fun _ => True ⦄ := by
  rw [slot.d_mix]
  apply Std.WP.spec_bind (mix_loop0_spec olf lz pdp plz lf 0#usize)
  intro a _
  apply Std.WP.spec_bind (mix_loop1_spec odf lzd pdpd plzd df 0#usize)
  intro b _
  step*
theorem ravg_loop0_spec (al bl : Array Std.U32 512#usize) (s : Std.Usize) :
    slot.d_ravg_loop0 al bl s ⦃ fun _ => True ⦄ := by
  rw [slot.d_ravg_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 512 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_ravg_loop0.body, lift]
    step*
  · trivial
theorem ravg_loop1_spec (ad bd : Array Std.U32 32#usize) (s : Std.Usize) :
    slot.d_ravg_loop1 ad bd s ⦃ fun _ => True ⦄ := by
  rw [slot.d_ravg_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 32 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_ravg_loop1.body, lift]
    step*
  · trivial
@[local step]
theorem ravg_spec (al : Array Std.U32 512#usize) (ad : Array Std.U32 32#usize)
    (bl : Array Std.U32 512#usize) (bd : Array Std.U32 32#usize) :
    slot.d_ravg al ad bl bd ⦃ fun _ => True ⦄ := by
  rw [slot.d_ravg]
  apply Std.WP.spec_bind (ravg_loop0_spec al bl 0#usize)
  intro a _
  apply Std.WP.spec_bind (ravg_loop1_spec ad bd 0#usize)
  intro b _
  step*
theorem copy16_loop_spec (al ad bl bd : Array Std.U16 32768#usize) (blen k : Std.Usize) :
    slot.d_copy16_loop al ad bl bd blen k ⦃ fun _ => True ⦄ := by
  rw [slot.d_copy16_loop]
  apply Std.loop.spec_decr_nat (measure := fun s => 32768 - s.2.2.val) (inv := fun _ => True)
  · rintro ⟨a, b, kk⟩ _
    simp only [slot.d_copy16_loop.body]
    step*
  · trivial
@[local step]
theorem copy16_spec (al ad bl bd : Array Std.U16 32768#usize) (blen : Std.Usize) :
    slot.d_copy16 al ad bl bd blen ⦃ fun _ => True ⦄ :=
  copy16_loop_spec al ad bl bd blen 0#usize
theorem hins_loop_spec (w : Array Std.U32 512#usize) (sym : Array Std.U16 512#usize)
    (x : Std.U32) (j : Std.Usize) :
    slot.d_hins_loop w sym x j ⦃ fun _ => True ⦄ := by
  rw [slot.d_hins_loop]
  apply Std.loop.spec_decr_nat (measure := fun s => s.2.2.val) (inv := fun _ => True)
  · rintro ⟨a, b, jj⟩ _
    simp only [slot.d_hins_loop.body]
    step*
  · trivial
@[local step]
theorem hins_spec (w : Array Std.U32 512#usize) (sym : Array Std.U16 512#usize)
    (m : Std.Usize) (x : Std.U32) (sy : Std.Usize) :
    slot.d_hins w sym m x sy ⦃ fun _ => True ⦄ := by
  rw [slot.d_hins]
  apply Std.WP.spec_bind (hins_loop_spec w sym x m)
  rintro ⟨a, b, j⟩ _
  simp only [lift]
  step*
theorem hbuild_loop0_spec (w : Array Std.U32 512#usize) (m : Std.Usize)
    (nw : Array Std.U32 1024#usize) (k : Std.Usize) :
    slot.d_hbuild_loop0 w m nw k ⦃ fun _ => True ⦄ := by
  rw [slot.d_hbuild_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 512 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, kk⟩ _
    simp only [slot.d_hbuild_loop0.body]
    step*
  · trivial
theorem hbuild_loop1_loop0_spec (m : Std.Usize) (nw : Array Std.U32 1024#usize)
    (i1 i2 top pick a b : Std.Usize) (B : Nat) (hB : B ≤ 4096) (h1 : i1.val ≤ m.val)
    (h2 : i2.val + (2 - pick.val) ≤ B) (hp : pick.val ≤ 2) :
    slot.d_hbuild_loop1_loop0 m nw i1 i2 top pick a b ⦃ fun r =>
      r.1.val ≤ m.val ∧ r.2.1.val ≤ B ⦄ := by
  rw [slot.d_hbuild_loop1_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 2 - s.2.2.1.val)
    (inv := fun s => s.1.val ≤ m.val ∧ s.2.1.val + (2 - s.2.2.1.val) ≤ B ∧ s.2.2.1.val ≤ 2)
  · rintro ⟨j1, j2, pk, aa, bb⟩ ⟨hj1, hj2, hpk⟩
    simp only at hj1 hj2 hpk
    simp only [slot.d_hbuild_loop1_loop0.body]
    split
    case isTrue hlt =>
      apply Std.WP.spec_bind (Pₘ := fun (t : Std.Usize) => t = 1#usize → j1.val < m.val)
      · split
        · split
          · step*
          · step*
        · step*
      · intro take1 ht
        simp only [ite_ok]
        apply Std.WP.spec_bind (Pₘ := fun (r : Std.Usize × Std.Usize) =>
          r.1.val ≤ m.val ∧ r.2.val + (2 - (pk.val + 1)) ≤ B)
        · split
          case isTrue h =>
            have := ht h
            step*
          case isFalse => step*
        · rintro ⟨k1, k2⟩ ⟨hk1, hk2⟩
          simp only at hk1 hk2
          split <;> step*
    case isFalse hge =>
      simp only [WP.spec_ok]
      refine ⟨hj1, by scalar_tac⟩
  · exact ⟨h1, h2, hp⟩
theorem hbuild_loop1_spec (m : Std.Usize) (nw : Array Std.U32 1024#usize)
    (par : Array Std.U16 1024#usize) (i1 i2 t : Std.Usize) (h1 : i1.val ≤ m.val)
    (h2 : i2.val ≤ m.val + 2 * t.val) (ht : t.val ≤ 512) :
    slot.d_hbuild_loop1 m nw par i1 i2 t ⦃ fun _ => True ⦄ := by
  rw [slot.d_hbuild_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 513 - s.2.2.2.2.val)
    (inv := fun s => s.2.2.1.val ≤ m.val ∧ s.2.2.2.1.val ≤ m.val + 2 * s.2.2.2.2.val ∧
      s.2.2.2.2.val ≤ 512)
  · rintro ⟨a, b, j1, j2, tt⟩ ⟨hj1, hj2, htt⟩
    simp only at hj1 hj2 htt
    simp only [slot.d_hbuild_loop1.body]
    step*
    apply Std.WP.spec_bind (hbuild_loop1_loop0_spec m a j1 j2 top 0#usize 0#usize 0#usize
      (m.val + 2 * tt.val + 2) (by scalar_tac) hj1 (by simp; scalar_tac) (by simp))
    rintro ⟨k1, k2, x, y⟩ ⟨hk1, hk2⟩
    simp only at hk1 hk2
    simp only [lift]
    step*
    all_goals refine ⟨?_, ?_, ?_, ?_⟩ <;> scalar_tac
  · exact ⟨h1, h2, ht⟩
theorem hbuild_loop2_spec (par : Array Std.U16 1024#usize) (dep : Array Std.U32 1024#usize)
    (root r : Std.Usize) (hd : ∀ x ∈ dep.val, x.val ≤ r.val) :
    slot.d_hbuild_loop2 par dep root r ⦃ fun _ => True ⦄ := by
  rw [slot.d_hbuild_loop2]
  apply Std.loop.spec_decr_nat (measure := fun s => 1025 - s.2.val)
    (inv := fun s => ∀ x ∈ s.1.val, x.val ≤ s.2.val)
  · rintro ⟨dd, rr⟩ hinv
    simp only at hinv
    simp only [slot.d_hbuild_loop2.body, lift]
    split
    · split
      · step*
        all_goals
          have hpd : pd.val ≤ rr.val := by
            rw [pd_post]; exact mem_bound_get dd (fun x => x.val ≤ rr.val) hinv _ _
          first
            | scalar_tac
            | (refine ⟨?_, by scalar_tac⟩
               rw [a_post]
               exact mem_bound_set dd _ _ _ (fun x hx => by have := hinv x hx; scalar_tac)
                 (by scalar_tac))
      · step*
    · step*
  · exact hd
theorem hbuild_loop3_spec (sym : Array Std.U16 512#usize) (m : Std.Usize)
    (out : Array Std.U32 512#usize) (dep : Array Std.U32 1024#usize) (k : Std.Usize)
    (ho : ∀ x ∈ out.val, x.val ≤ 15) :
    slot.d_hbuild_loop3 sym m out dep k ⦃ fun r => ∀ x ∈ r.val, x.val ≤ 15 ⦄ := by
  rw [slot.d_hbuild_loop3]
  apply Std.loop.spec_decr_nat (measure := fun s => 512 - s.2.val)
    (inv := fun s => ∀ x ∈ s.1.val, x.val ≤ 15)
  · rintro ⟨oo, kk⟩ hinv
    simp only at hinv
    simp only [slot.d_hbuild_loop3.body, lift, ite_ok]
    split
    · split
      · step*
        refine ⟨?_, by scalar_tac⟩
        rw [a_post]
        exact mem_bound_set oo _ _ _ hinv (by split <;> scalar_tac)
      · simpa using hinv
    · simpa using hinv
  · exact ho
@[local step]
theorem hbuild_spec (w : Array Std.U32 512#usize) (sym : Array Std.U16 512#usize)
    (m : Std.Usize) (out : Array Std.U32 512#usize) (hm : m.val ≤ 512)
    (ho : ∀ x ∈ out.val, x.val ≤ 15) :
    slot.d_hbuild w sym m out ⦃ fun r => ∀ x ∈ r.val, x.val ≤ 15 ⦄ := by
  rw [slot.d_hbuild]
  apply Std.WP.spec_bind (hbuild_loop0_spec w m _ 0#usize)
  intro nw1 _
  apply Std.WP.spec_bind (hbuild_loop1_spec m nw1 _ 0#usize m 0#usize (by simp) (by simp)
    (by simp))
  intro par1 _
  apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
  · split <;> step*
  intro root _
  step*
  apply Std.WP.spec_bind (hbuild_loop2_spec par1 _ root 1#usize ?_)
  · intro dep1 _
    exact hbuild_loop3_spec sym m out dep1 0#usize ho
  · rw [a_post]
    exact mem_bound_set _ _ _ _ (mem_bound_repeat _ _ _ (by simp)) (by simp)
theorem hlens_loop_spec (f : Array Std.U32 512#usize) (ns : Std.Usize)
    (out w : Array Std.U32 512#usize) (sym : Array Std.U16 512#usize) (m s : Std.Usize)
    (hms : m.val ≤ s.val) (hs : s.val ≤ 512) (ho : ∀ x ∈ out.val, x.val ≤ 15) :
    slot.d_hlens_loop f ns out w sym m s ⦃ fun r =>
      (∀ x ∈ r.1.val, x.val ≤ 15) ∧ r.2.2.2.val ≤ 512 ⦄ := by
  rw [slot.d_hlens_loop]
  apply Std.loop.spec_decr_nat (measure := fun st => 512 - st.2.2.2.2.val)
    (inv := fun st => st.2.2.2.1.val ≤ st.2.2.2.2.val ∧ st.2.2.2.2.val ≤ 512 ∧
      ∀ x ∈ st.1.val, x.val ≤ 15)
  · rintro ⟨oo, ww, sy, mm, ss⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    simp only [slot.d_hlens_loop.body]
    split
    · split
      · step*
        apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 512#usize) ×
          (Array Std.U16 512#usize) × Std.Usize) => x.2.2.val ≤ mm.val + 1)
        · split <;> step*
        · rintro ⟨w1, s1, m1⟩ hm1
          simp only at hm1
          step*
          refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
          rw [a_post]
          exact mem_bound_set oo _ _ _ h3 (by simp)
      · simp only [WP.spec_ok]
        exact ⟨h3, by scalar_tac⟩
    · simp only [WP.spec_ok]
      exact ⟨h3, by scalar_tac⟩
  · exact ⟨hms, hs, ho⟩
@[local step]
theorem hlens_spec (f : Array Std.U32 512#usize) (ns : Std.Usize)
    (out : Array Std.U32 512#usize) (ho : ∀ x ∈ out.val, x.val ≤ 15) :
    slot.d_hlens f ns out ⦃ fun r => ∀ x ∈ r.val, x.val ≤ 15 ⦄ := by
  rw [slot.d_hlens]
  apply Std.WP.spec_bind (hlens_loop_spec f ns out _ _ 0#usize 0#usize (by simp) (by simp) ho)
  rintro ⟨o1, w1, s1, m⟩ ⟨h1, h2⟩
  simp only at h1 h2
  apply Std.WP.spec_bind (Pₘ := fun (o : Array Std.U32 512#usize) => ∀ x ∈ o.val, x.val ≤ 15)
  · split
    · simp only [lift]
      step*
      all_goals (subst_vars; exact mem_bound_set o1 _ 1#u32 (fun (x : Std.U32) => x.val ≤ 15) h1 (by simp) _ ‹_›)
    · simpa using h1
  · intro o2 ho2
    split
    · step*
    · simpa using ho2
@[local step]
theorem hcost_spec (e h hw : Std.U32) (he : e.val ≤ 1048576) (hh : h.val ≤ 15) :
    slot.d_hcost e h hw ⦃ fun _ => True ⦄ := by
  rw [slot.d_hcost]
  split
  · simp
  · split
    · simp
    · step*
      all_goals
        have h1 := Nat.mul_le_mul he (show i.val ≤ 16 by scalar_tac)
        first
          | scalar_tac
          | (have h2 := Nat.mul_le_mul (show i2.val ≤ 240 by scalar_tac)
               (show hw.val ≤ 16 by scalar_tac)
             scalar_tac)
theorem learn_loop0_spec (lf : Array Std.U32 512#usize) (tot : Std.U32) (s : Std.Usize) :
    slot.d_learn_loop0 lf tot s ⦃ fun _ => True ⦄ := by
  rw [slot.d_learn_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 286 - s.2.val) (inv := fun _ => True)
  · rintro ⟨t, k⟩ _
    simp only [slot.d_learn_loop0.body, lift]
    step*
  · trivial
theorem learn_loop1_spec (lf : Array Std.U32 512#usize) (litc : Array Std.U32 256#usize)
    (bias hw : Std.U32) (hl : Array Std.U32 512#usize) (tot : Std.U32) (s : Std.Usize)
    (hhl : ∀ x ∈ hl.val, x.val ≤ 15) :
    slot.d_learn_loop1 lf litc bias hw hl tot s ⦃ fun _ => True ⦄ := by
  rw [slot.d_learn_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 256 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_learn_loop1.body, lift]
    step*
    all_goals first
      | (rw [i2_post]; exact mem_bound_get hl (fun (x : Std.U32) => x.val ≤ 15) hhl _ _)
      | scalar_tac
  · trivial
theorem learn_loop2_spec (lf : Array Std.U32 512#usize) (bias hw : Std.U32)
    (hl : Array Std.U32 512#usize) (tot : Std.U32) (cc : Array Std.U32 32#usize) (c : Std.Usize)
    (hhl : ∀ x ∈ hl.val, x.val ≤ 15) :
    slot.d_learn_loop2 lf bias hw hl tot cc c ⦃ fun _ => True ⦄ := by
  rw [slot.d_learn_loop2]
  apply Std.loop.spec_decr_nat (measure := fun s => 29 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_learn_loop2.body, lift]
    step*
    all_goals first
      | (rw [i5_post]; exact mem_bound_get hl (fun (x : Std.U32) => x.val ≤ 15) hhl _ _)
      | scalar_tac
  · trivial
set_option hygiene false in
local notation "U32!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat (measure := fun s => 259 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [q1__, lift]
    step*
  · trivial)
theorem learn_loop3_spec (lenc : Array Std.U32 512#usize) (lcode lextra : Array Std.U8 512#usize)
    (cc : Array Std.U32 32#usize) (l : Std.Usize) :
    slot.d_learn_loop3 lenc lcode lextra cc l ⦃ fun _ => True ⦄ := U32! slot.d_learn_loop3 slot.d_learn_loop3.body
theorem learn_loop4_spec (df : Array Std.U32 32#usize) (c : Std.Usize) (dt : Std.U32) :
    slot.d_learn_loop4 df c dt ⦃ fun _ => True ⦄ := by
  rw [slot.d_learn_loop4]
  apply Std.loop.spec_decr_nat (measure := fun s => 30 - s.1.val) (inv := fun _ => True)
  · rintro ⟨k, t⟩ _
    simp only [slot.d_learn_loop4.body, lift]
    step*
  · trivial
set_option hygiene false in
local notation "U33!" q0__:max q1__:max => (by
  rw [q0__]
  apply Std.loop.spec_decr_nat (measure := fun s => 30 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [q1__, lift]
    step*
  · trivial)
theorem learn_loop5_spec (df dcost : Array Std.U32 32#usize) (dext : Array Std.U8 32#usize)
    (c : Std.Usize) (dt : Std.U32) :
    slot.d_learn_loop5 df dcost dext c dt ⦃ fun _ => True ⦄ := U33! slot.d_learn_loop5 slot.d_learn_loop5.body
@[local step]
theorem learn_spec (lf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize)
    (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (lcode lextra : Array Std.U8 512#usize)
    (dext : Array Std.U8 32#usize) (bias hw : Std.U32) :
    slot.d_learn lf df litc lenc dcost lcode lextra dext bias hw ⦃ fun _ => True ⦄ := by
  rw [slot.d_learn]
  apply Std.WP.spec_bind (Pₘ := fun (h : Array Std.U32 512#usize) => ∀ x ∈ h.val, x.val ≤ 15)
  · split
    · exact hlens_spec lf 286#usize _ (mem_bound_repeat _ _ _ (by simp))
    · simp only [WP.spec_ok]
      exact mem_bound_repeat _ _ _ (by simp)
  intro hl hhl
  apply Std.WP.spec_bind (learn_loop0_spec lf 1#u32 0#usize)
  intro t _
  apply Std.WP.spec_bind (learn_loop1_spec lf litc bias hw hl t 0#usize hhl)
  intro a _
  apply Std.WP.spec_bind (learn_loop2_spec lf bias hw hl t _ 0#usize hhl)
  intro cc _
  apply Std.WP.spec_bind (learn_loop3_spec lenc lcode lextra cc 3#usize)
  intro b _
  apply Std.WP.spec_bind (learn_loop4_spec df 0#usize 1#u32)
  intro u _
  apply Std.WP.spec_bind (learn_loop5_spec df dcost dext 0#usize u)
  intro c _
  step*
theorem len_tables_loop_spec (lbase : Array Std.U16 32#usize) (lext : Array Std.U8 32#usize)
    (lcode lextra : Array Std.U8 512#usize) (bend : Array Std.U16 512#usize) (c l : Std.Usize)
    (hc0 : c.val ≤ 28) :
    slot.d_len_tables_loop lbase lext lcode lextra bend c l ⦃ fun _ => True ⦄ := by
  rw [slot.d_len_tables_loop]
  apply Std.loop.spec_decr_nat (measure := fun s => 259 - s.2.2.2.2.val)
    (inv := fun s => s.2.2.2.1.val ≤ 28)
  · rintro ⟨a, b, e, cc, ll⟩ hc
    simp only at hc
    simp only [slot.d_len_tables_loop.body, lift]
    split
    case isTrue hl =>
      apply Std.WP.spec_bind (Pₘ := fun (c1 : Std.Usize) => c1.val ≤ 28)
      · split
        · step*
        · step*
      · intro c1 hc1
        step*
        apply Std.WP.spec_bind (Pₘ := fun (_ : Std.U16) => True)
        · split <;> step*
        · intro t _
          step*
    case isFalse => step*
  · exact hc0
theorem code_from_loop_spec (dbase : Array Std.U16 32#usize) (d c : Std.Usize) :
    slot.d_code_from_loop dbase d c ⦃ fun _ => True ⦄ := by
  rw [slot.d_code_from_loop]
  apply Std.loop.spec_decr_nat (measure := fun s => 29 - s.val) (inv := fun _ => True)
  · intro cc _
    simp only [slot.d_code_from_loop.body]
    step*
  · trivial
@[local step]
theorem code_from_spec (dbase : Array Std.U16 32#usize) (d c0 : Std.Usize) :
    slot.d_code_from dbase d c0 ⦃ fun _ => True ⦄ :=
  code_from_loop_spec dbase d c0
theorem dist_tables_loop0_spec (dbase : Array Std.U16 32#usize) (dlo : Array Std.U8 256#usize)
    (c d : Std.Usize) (hd : 1 ≤ d.val) :
    slot.d_dist_tables_loop0 dbase dlo c d ⦃ fun _ => True ⦄ := by
  rw [slot.d_dist_tables_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 257 - s.2.2.val)
    (inv := fun s => 1 ≤ s.2.2.val)
  · rintro ⟨a, cc, dd⟩ h
    simp only at h
    simp only [slot.d_dist_tables_loop0.body]
    step*
    all_goals scalar_tac
  · exact hd
theorem dist_tables_loop1_spec (dbase : Array Std.U16 32#usize) (dhi : Array Std.U8 256#usize)
    (c k : Std.Usize) :
    slot.d_dist_tables_loop1 dbase dhi c k ⦃ fun _ => True ⦄ := by
  rw [slot.d_dist_tables_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 256 - s.2.2.val) (inv := fun _ => True)
  · rintro ⟨a, cc, kk⟩ _
    simp only [slot.d_dist_tables_loop1.body]
    step*
  · trivial
@[local step]
theorem dist_tables_spec (dbase : Array Std.U16 32#usize) (dlo dhi : Array Std.U8 256#usize) :
    slot.d_dist_tables dbase dlo dhi ⦃ fun _ => True ⦄ := by
  rw [slot.d_dist_tables]
  apply Std.WP.spec_bind (dist_tables_loop0_spec dbase dlo 0#usize 1#usize (by simp))
  intro a _
  apply Std.WP.spec_bind (dist_tables_loop1_spec dbase dhi 0#usize 0#usize)
  intro b _
  step*
@[local step]
theorem len_tables_spec (lbase : Array Std.U16 32#usize) (lext : Array Std.U8 32#usize)
    (lcode lextra : Array Std.U8 512#usize) (bend : Array Std.U16 512#usize) :
    slot.d_len_tables lbase lext lcode lextra bend ⦃ fun _ => True ⦄ :=
  len_tables_loop_spec lbase lext lcode lextra bend 0#usize 3#usize (by simp)
@[local step]
theorem tables_spec (lcode lextra : Array Std.U8 512#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (dext : Array Std.U8 32#usize) :
    slot.d_tables lcode lextra bend dlo dhi dext ⦃ fun _ => True ⦄ := by
  rw [slot.d_tables]
  step*
theorem seed_loop0_spec (input : Slice Std.U8) (lim : Std.Usize) (hist : Array Std.U32 256#usize)
    (i : Std.Usize) (hl : lim.val ≤ input.length) :
    slot.d_seed_loop0 input lim hist i ⦃ fun _ => True ⦄ := by
  rw [slot.d_seed_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => lim.val - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_seed_loop0.body, lift]
    step*
  · trivial
theorem seed_loop1_spec (litc hist : Array Std.U32 256#usize) (tot : Std.U32) (s : Std.Usize)
    (sum : Std.U64) :
    slot.d_seed_loop1 litc hist tot s sum ⦃ fun _ => True ⦄ := by
  rw [slot.d_seed_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 256 - s.2.1.val) (inv := fun _ => True)
  · rintro ⟨a, k, m⟩ _
    simp only [slot.d_seed_loop1.body, lift]
    step*
  · trivial
theorem seed_loop2_spec (lenc : Array Std.U32 512#usize) (lextra : Array Std.U8 512#usize)
    (l : Std.Usize) :
    slot.d_seed_loop2 lenc lextra l ⦃ fun _ => True ⦄ := U32! slot.d_seed_loop2 slot.d_seed_loop2.body
theorem seed_loop3_spec (dcost : Array Std.U32 32#usize) (dext : Array Std.U8 32#usize)
    (c : Std.Usize) :
    slot.d_seed_loop3 dcost dext c ⦃ fun _ => True ⦄ := U33! slot.d_seed_loop3 slot.d_seed_loop3.body
@[local step]
theorem seed_spec (input : Slice Std.U8) (litc : Array Std.U32 256#usize)
    (lenc : Array Std.U32 512#usize) (dcost : Array Std.U32 32#usize)
    (lextra : Array Std.U8 512#usize) (dext : Array Std.U8 32#usize) :
    slot.d_seed input litc lenc dcost lextra dext ⦃ fun _ => True ⦄ := by
  rw [slot.d_seed]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  simp only [ite_ok]
  have hl : (if Slice.len input < 32768#usize then Slice.len input else 32768#usize).val
      ≤ input.length ∧
      (if Slice.len input < 32768#usize then Slice.len input else 32768#usize).val ≤ 32768 := by
    constructor <;> split <;> scalar_tac
  generalize (if Slice.len input < 32768#usize then Slice.len input else 32768#usize) = lim at hl ⊢
  obtain ⟨hl1, hl2⟩ := hl
  apply Std.WP.spec_bind (seed_loop0_spec input lim _ 0#usize hl1)
  intro h _
  step*
  apply Std.WP.spec_bind (seed_loop1_spec litc h _ 0#usize 0#u64)
  rintro ⟨a, sm⟩ _
  apply Std.WP.spec_bind (seed_loop2_spec lenc lextra 3#usize)
  intro b _
  apply Std.WP.spec_bind (seed_loop3_spec dcost dext 0#usize)
  intro c _
  simp only [lift]
  step*
theorem add_bias_loop0_spec (litc : Array Std.U32 256#usize) (bias : Std.U32) (s : Std.Usize) :
    slot.d_add_bias_loop0 litc bias s ⦃ fun _ => True ⦄ := by
  rw [slot.d_add_bias_loop0]
  apply Std.loop.spec_decr_nat (measure := fun st => 256 - st.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_add_bias_loop0.body, lift]
    step*
  · trivial
theorem add_bias_loop1_spec (lenc : Array Std.U32 512#usize) (bias : Std.U32) (l : Std.Usize) :
    slot.d_add_bias_loop1 lenc bias l ⦃ fun _ => True ⦄ := by
  rw [slot.d_add_bias_loop1]
  apply Std.loop.spec_decr_nat (measure := fun st => 259 - st.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.d_add_bias_loop1.body, lift]
    step*
  · trivial
@[local step]
theorem add_bias_spec (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (bias : Std.U32) :
    slot.d_add_bias litc lenc bias ⦃ fun _ => True ⦄ := by
  rw [slot.d_add_bias]
  apply Std.WP.spec_bind (add_bias_loop0_spec litc bias 0#usize)
  intro a _
  apply Std.WP.spec_bind (add_bias_loop1_spec lenc bias 3#usize)
  intro b _
  step*
theorem verified_spec (input : Slice Std.U8) (pos d ch k blen : Std.Usize)
    (hlen : pos.val + (blen.val - k.val) ≤ input.length) (hk : k.val ≤ blen.val)
    (hb : blen.val ≤ 32768) :
    slot.d_verified input pos d ch k blen ⦃ fun b => b = true →
      3 ≤ ch.val ∧ ch.val ≤ 258 ∧ 1 ≤ d.val ∧ d.val ≤ 32768 ∧ d.val ≤ pos.val ∧
      k.val + ch.val ≤ blen.val ∧ Matches input (pos.val - d.val) pos.val ch.val ⦄ := by
  rw [slot.d_verified]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
theorem emit_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (chl chd : Array Std.U16 32768#usize) (p0 blen ntok0 k0 : Std.Usize)
    (hblen : p0.val + blen.val ≤ input.length) (hb : blen.val ≤ 32768)
    (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ blen.val) (hntok : ntok0.val ≤ p0.val + k0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take (p0.val + k0.val))) :
    slot.d_emit_loop input out0 chl chd p0 blen ntok0 k0 ⦃ fun r =>
      r.1.val ≤ p0.val + blen.val ∧ r.2.length = out0.length ∧
      LZ77.decode (toks r.2 r.1.val) = some ((bytes input).take (p0.val + blen.val)) ⦄ := by
  rw [slot.d_emit_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => blen.val - s.2.2.val)
    (inv := fun s =>
      s.2.2.val ≤ blen.val ∧ s.2.1.val ≤ p0.val + s.2.2.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.1.val) = some ((bytes input).take (p0.val + s.2.2.val)))
  · rintro ⟨out, ntok, k⟩ ⟨hkb, hnt, hlen, hde⟩
    simp only at hkb hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_emit_loop.body]
    split
    case isTrue hklt =>
      have hntok_lt : ntok.val < out.length := by scalar_tac
      step*
      apply Std.WP.spec_bind (verified_spec input pos d ch k blen (by scalar_tac) (by scalar_tac) hb)
      intro b hbv
      split
      case isTrue hbt =>
        obtain ⟨hch3, hch258, hd1, hdmax, hdpos, hend, hmatch⟩ := hbv hbt
        step*
        have htok : i9.val = LZ77.mkMatch d.val ch.val := by
          simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i9_post, i6_post, i5_post, i4_post,
            i3_post1, i8_post, i7_post1, Std.UScalar.cast_val_eq] at *
          scalar_tac
        refine ⟨by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          toks_update out ntok i9 hntok_lt, htok,
          show p0.val + k1.val = pos.val + ch.val by scalar_tac]
        refine LZ77.valid_match (bytes input) (toks out ntok.val) pos.val d.val ch.val
          (by rw [show pos.val = p0.val + k.val by scalar_tac]; exact hde)
          hd1 hdpos (by simpa [LZ77.MAX_DIST] using hdmax) hch3
          (by simpa [LZ77.MAX_LEN] using hch258) (by rw [bytes_length]; scalar_tac) ?_
        intro j hj
        exact (bytes_congr input _ _ (by scalar_tac) (by scalar_tac) (hmatch j hj)).symm
      case isFalse hbf =>
        have hposlen : pos.val < input.length := by scalar_tac
        step*
        have hval : i4.val = (bytes input)[pos.val]! := by
          rw [bytes_getElem! input pos.val hposlen, i4_post, Std.U8.cast_U32_val_eq, i3_post]
        refine ⟨by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          toks_update out ntok i4 hntok_lt, hval,
          show p0.val + k1.val = pos.val + 1 by scalar_tac]
        exact LZ77.valid_lit (bytes input) (toks out ntok.val) pos.val
          (by rw [show pos.val = p0.val + k.val by scalar_tac]; exact hde)
          (by rw [bytes_length]; scalar_tac) (by rw [← hval]; scalar_tac)
    case isFalse hge =>
      have hkb' : k.val = blen.val := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      rw [hde, hkb']
  · exact ⟨hk, hntok, rfl, hdec⟩
theorem parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize)
    (lcode lextra : Array Std.U8 512#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (dext : Array Std.U8 32#usize)
    (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (long : Std.Usize) (bias hw : Std.U32)
    (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (c1l c1d c2l c2d bkl bkd : Array Std.U16 32768#usize)
    (cost : Array Std.U32 65536#usize) (xs : Array Std.U32 131072#usize)
    (xn : Array Std.U8 32768#usize)
    (lf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize)
    (olf : Array Std.U32 512#usize) (odf : Array Std.U32 32#usize)
    (lz : Array Std.U32 512#usize) (lzd : Array Std.U32 32#usize)
    (plz : Array Std.U32 512#usize) (plzd : Array Std.U32 32#usize)
    (pdp : Array Std.U32 512#usize) (pdpd : Array Std.U32 32#usize)
    (tdp : Array Std.U32 512#usize) (tdpd : Array Std.U32 32#usize)
    (zl : Array Std.U32 512#usize) (zd : Array Std.U32 32#usize) (ntok0 p00 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hpos : p00.val ≤ n.val) (hntok : ntok0.val ≤ p00.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take p00.val)) :
    slot.d_parse_loop input out0 n lcode lextra bend dlo dhi dext litc lenc dcost long bias hw head4
      prev near c1l c1d c2l c2d bkl bkd cost xs xn lf df olf odf lz lzd plz plzd pdp pdpd tdp tdpd
      zl zd ntok0 p00 ⦃ fun r =>
        r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
        LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.d_parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s =>
      s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ≤ n.val ∧
      s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ≤ s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val) =
        some ((bytes input).take s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val))
  · rintro ⟨out, lc, le, dc, hd, pv, nr, a1, a2, a3, a4, bk1, bk2, cs, xs0, xn0, l1, d1, ol1, od1, z1, z2, z3, z4, z5, z6, z7, z8, ntok, p0⟩
      ⟨hp, hnt, hlen, hde⟩
    simp only at hp hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.d_parse_loop.body]
    split
    case isTrue hlt =>
      step*
      simp only [ite_ok]
      have hbl : (if rest > slot.D_BLOCK then slot.D_BLOCK else rest).val ≤ 32768 ∧
          (if rest > slot.D_BLOCK then slot.D_BLOCK else rest).val ≤ rest.val ∧
          1 ≤ (if rest > slot.D_BLOCK then slot.D_BLOCK else rest).val := by
        split <;> scalar_tac
      generalize (if rest > slot.D_BLOCK then slot.D_BLOCK else rest) = blen at hbl ⊢
      obtain ⟨hb1, hb2, hb3⟩ := hbl
      step*
      apply Std.WP.spec_bind (Pₘ := fun _ => True)
      · split <;> step*
      intro rf _
      apply Std.WP.spec_bind (Pₘ := fun _ => True)
      · split <;> step*
      rintro ⟨bkl1, bkd1⟩ _
      step*
      apply Std.WP.spec_bind (Pₘ := fun _ => True)
      · split <;> step*
      rintro ⟨litc2, lenc2, dcost2, c1l3, c1d3, cost3, lf2, df2⟩ _
      apply Std.WP.spec_bind (Pₘ := fun _ => True)
      · split <;> step*
      rintro ⟨litc3, lenc3, dcost3, lf3, df3, olf1, odf1, plz1, plzd1, pdp1, pdpd1, tdp1,
        tdpd1⟩ _
      apply Std.WP.spec_bind (emit_loop_spec input out _ _ p0 blen ntok 0#usize
        (by scalar_tac) hb1 (by scalar_tac) (by simp) (by simpa using hnt) (by simpa using hde))
      rintro ⟨ntok1, out1⟩ ⟨hnt1, hlen1, hde1⟩
      simp only at hnt1 hlen1 hde1
      step*
      refine ⟨by scalar_tac, by scalar_tac, hlen1.trans hlen, ?_, by scalar_tac⟩
      rw [hde1, show p01.val = p0.val + blen.val by scalar_tac]
    case isFalse hge =>
      have hpn : p0.val = n.val := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      rw [hde, hpn, hn]
      simp
  · exact ⟨hpos, hntok, rfl, hdec⟩
theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.d_parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.d_parse]
  simp only [ite_ok]
  step*
  exact parse_loop_spec input out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ 0#usize 0#usize
    (by simp) hlen (by scalar_tac) (by scalar_tac) (by simp [toks, LZ77.decode])
end ED
theorem r_len_loop_spec (input : Slice Std.U8) (a b cap l : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl : l.val ≤ cap.val) :
    slot.r_len_loop input a b cap l ⦃ fun r => r.val ≤ cap.val ⦄ := by
  rw [slot.r_len_loop]
  apply Std.loop.spec_decr_nat (measure := fun l => cap.val - l.val) (inv := fun l => l.val ≤ cap.val)
  · intro l1 hl1
    simp only [slot.r_len_loop.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    step*
    all_goals repeat' (first | (split <;> step*) | scalar_tac)
  · exact hl
@[local step]
theorem r_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.r_len input a b cap ⦃ fun r => r.val ≤ cap.val ⦄ := by
  rw [slot.r_len]
  exact r_len_loop_spec input a b cap 0#usize ha hb (by scalar_tac)
@[local step]
theorem r_hash_spec (input : Slice Std.U8) (p : Std.Usize) (h : p.val + 4 ≤ input.length) :
    slot.r_hash input p ⦃ fun r => r.val < 65536 ⦄ := by
  rw [slot.r_hash]
  step*
@[local step]
theorem r_cover_loop0_loop0_spec (input : Slice Std.U8) (start : Std.Usize)
    (head : Array Std.U32 65536#usize) (lim q e : Std.Usize)
    (hlim : start.val + lim.val + 4 ≤ input.length) :
    slot.r_cover_loop0_loop0 input start head lim q e ⦃ fun _ => True ⦄ := by
  rw [slot.r_cover_loop0_loop0]
  apply Std.loop.spec_decr_nat (measure := fun st => e.val - st.2.val) (inv := fun _ => True)
  · rintro ⟨h1, q1⟩ _
    simp only [slot.r_cover_loop0_loop0.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    step*
    all_goals repeat' (first | (split <;> step*) | scalar_tac)
  · trivial
theorem r_cover_loop0_spec (input : Slice Std.U8) (start s : Std.Usize)
    (head : Array Std.U32 65536#usize) (cov long i lim : Std.Usize)
    (hs : start.val + s.val ≤ input.length) (hlim : lim.val + 4 = s.val) (hi : i.val ≤ s.val) :
    slot.r_cover_loop0 input start s head cov long i lim ⦃ fun _ => True ⦄ := by
  rw [slot.r_cover_loop0]
  apply Std.loop.spec_decr_nat (measure := fun st => s.val - st.2.2.2.val)
    (inv := fun st => st.2.2.2.val ≤ s.val)
  · rintro ⟨h1, c1, l1, i1⟩ hinv
    simp only at hinv
    simp only [slot.r_cover_loop0.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    step*
    all_goals repeat' (first | (split <;> step*) | scalar_tac)
  · exact hi
@[local step]
theorem r_cover_spec (input : Slice Std.U8) (start s : Std.Usize) (hs4 : 4 ≤ s.val)
    (hs : start.val + s.val ≤ input.length) :
    slot.r_cover input start s ⦃ fun _ => True ⦄ := by
  rw [slot.r_cover]
  step*
  exact r_cover_loop0_spec input start s _ 0#usize 0#usize 0#usize lim hs (by scalar_tac)
    (by scalar_tac)
@[local step]
theorem r_hist_loop_spec (input : Slice Std.U8) (s : Std.Usize) (hist : Array Std.U32 256#usize)
    (i : Std.Usize) (hs : s.val ≤ input.length) :
    slot.r_hist_loop input s hist i ⦃ fun _ => True ⦄ := by
  rw [slot.r_hist_loop]
  apply Std.loop.spec_decr_nat (measure := fun st => s.val - st.2.val) (inv := fun _ => True)
  · rintro ⟨h1, i1⟩ _
    simp only [slot.r_hist_loop.body]
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    step*
    all_goals repeat' (first | (split <;> step*) | scalar_tac)
  · trivial
@[local step]
theorem r_hist_spec (input : Slice Std.U8) (s : Std.Usize) (hist : Array Std.U32 256#usize)
    (hs : s.val ≤ input.length) :
    slot.r_hist input s hist ⦃ fun _ => True ⦄ := by
  rw [slot.r_hist]
  step*
@[local step]
theorem r_sum_loop_spec (hist : Array Std.U32 256#usize) (b : Std.Usize) (t : Std.U64)
    (k : Std.Usize) (hb : b.val ≤ 256) :
    slot.r_sum_loop hist b t k ⦃ fun _ => True ⦄ := by
  rw [slot.r_sum_loop]
  apply Std.loop.spec_decr_nat (measure := fun st => b.val - st.2.val) (inv := fun _ => True)
  · rintro ⟨t1, k1⟩ _
    simp only [slot.r_sum_loop.body]
    step*
    all_goals repeat' (first | (split <;> step*) | scalar_tac)
  · trivial
@[local step]
theorem r_sum_spec (hist : Array Std.U32 256#usize) (a b : Std.Usize) (hb : b.val ≤ 256) :
    slot.r_sum hist a b ⦃ fun _ => True ⦄ := by
  rw [slot.r_sum]
  step*
@[local step]
theorem r_alpha_loop_spec (hist : Array Std.U32 256#usize) (c k : Std.Usize) (hc : c.val ≤ k.val)
    (hk : k.val ≤ 256) :
    slot.r_alpha_loop hist c k ⦃ fun _ => True ⦄ := by
  rw [slot.r_alpha_loop]
  apply Std.loop.spec_decr_nat (measure := fun st => 256 - st.2.val)
    (inv := fun st => st.1.val ≤ st.2.val ∧ st.2.val ≤ 256)
  · rintro ⟨c1, k1⟩ ⟨h1, h2⟩
    simp only [slot.r_alpha_loop.body]
    step*
    all_goals repeat' (first | (split <;> step*) | scalar_tac)
  · exact ⟨hc, hk⟩
@[local step]
theorem r_alpha_spec (hist : Array Std.U32 256#usize) : slot.r_alpha hist ⦃ fun _ => True ⦄ := by
  rw [slot.r_alpha]
  step*
@[local step]
theorem route_spec (input : Slice Std.U8) : slot.route input ⦃ fun _ => True ⦄ := by
  rw [slot.route]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  all_goals repeat' (first | (split <;> step*) | scalar_tac)
theorem parse_c0_spec (input : Slice Std.U8) (out : Slice Std.U32) (r : Std.Usize)
    (hlen : input.length ≤ out.length) :
    slot.parse_c0 input out r ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.parse_c0]
  split
  · exact EA.parse_mode_spec input out 0#usize hlen
  · split
    · exact EA.parse_mode_spec input out 1#usize hlen
    · split
      · exact EA.parse_mode_spec input out 2#usize hlen
      · split
        · exact EA.parse_mode_spec input out 3#usize hlen
        · split
          · exact EA.parse_mode_spec input out 4#usize hlen
          · split
            · exact EA.parse_mode_spec input out 5#usize hlen
            · split
              · exact EA.parse_mode_spec input out 6#usize hlen
              · exact EA.parse_mode_spec input out 7#usize hlen
theorem parse_c1_spec (input : Slice Std.U8) (out : Slice Std.U32) (r : Std.Usize)
    (hlen : input.length ≤ out.length) :
    slot.parse_c1 input out r ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.parse_c1]
  split
  · exact EA.parse_mode_spec input out 8#usize hlen
  · split
    · exact EA.parse_mode_spec input out 9#usize hlen
    · split
      · exact EA.parse_mode_spec input out 10#usize hlen
      · split
        · exact EA.parse_mode_spec input out 11#usize hlen
        · split
          · exact EA.parse_mode_spec input out 12#usize hlen
          · split
            · exact EB.parse_mode_spec input out 3#usize hlen
            · split
              · exact EB.parse_mode_spec input out 4#usize hlen
              · exact EB.parse_mode_spec input out 2#usize hlen
theorem parse_c2_spec (input : Slice Std.U8) (out : Slice Std.U32) (r : Std.Usize)
    (hlen : input.length ≤ out.length) :
    slot.parse_c2 input out r ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.parse_c2]
  split
  · exact EB.parse_mode_spec input out 0#usize hlen
  · exact ED.parse_spec input out hlen
theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.parse]
  apply Std.WP.spec_bind (route_spec input)
  intro r _
  split
  · exact parse_c0_spec input out r hlen
  · split
    · exact parse_c1_spec input out r hlen
    · exact parse_c2_spec input out r hlen
end Submission

