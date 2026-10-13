import Lz77
import Slot

/-!
The lazy-then-optimal block parse. The lazy pass, the candidate search, the cost model,
the backward dynamic program and the symbol counts are search: postcondition `True` (or a
bound), only termination and indices in range. The bounds the lazy pass carries are the
ones its callees rely on: a pending match fits in the block and its distance is in range.
The emission re-verifies every chosen match with `match_len`, so its invariant is the
template's: the tokens written so far decode to the input consumed so far.
-/

namespace Submission
open Aeneas Aeneas.Std Result ControlFlow

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr Matches ite_ok)

/-! ## The match-length loop: the one load-bearing function -/

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

/-! ## The guarded match length of the search: a bound only -/

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
    slot.load64 input p ⦃ fun _ => True ⦄ := by
  rw [slot.load64]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  simp only [lift]
  step*

theorem ext_len_loop0_spec (input : Slice Std.U8) (a b cap l0 go0 : Std.Usize)
    (ha : a.val < b.val) (hb : b.val + cap.val ≤ input.length) (hl0 : l0.val ≤ cap.val) :
    slot.ext_len_loop0 input a b cap l0 go0 ⦃ fun r => r.1.val ≤ cap.val ⦄ := by
  rw [slot.ext_len_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => cap.val - s.1.val + s.2.val)
    (inv := fun s => s.1.val ≤ cap.val)
  · rintro ⟨l, go⟩ hle
    simp only at hle
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.ext_len_loop0.body]
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
    slot.ext_len_loop1 input a b cap l0 go ⦃ fun l => l.val ≤ cap.val ⦄ := by
  rw [slot.ext_len_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val)
  · intro l hle
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.ext_len_loop1.body]
    split
    · split
      · step*
      · exact hle
    · exact hle
  · exact hl0

@[local step]
theorem ext_len_spec (input : Slice Std.U8) (a b cap : Std.Usize) :
    slot.ext_len input a b cap ⦃ fun l => l.val ≤ cap.val ⦄ := by
  rw [slot.ext_len]
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

/-! ## Bit costs -/

theorem cost16_loop_spec (t f : Std.U64) (c : Std.U32) (k : Std.Usize)
    (hc : c.val ≤ 1024 + k.val) (hk : k.val ≤ 16) :
    slot.cost16_loop t f c k ⦃ fun _ => True ⦄ := by
  rw [slot.cost16_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 16 - s.2.2.val)
    (inv := fun s => s.2.1.val ≤ 1024 + s.2.2.val ∧ s.2.2.val ≤ 16)
  · rintro ⟨f1, c1, k1⟩ ⟨hc1, hk1⟩
    simp only at hc1 hk1
    simp only [slot.cost16_loop.body, lift]
    step*
  · exact ⟨hc, hk⟩

@[local step]
theorem cost16_spec (freq total : Std.U32) : slot.cost16 freq total ⦃ fun _ => True ⦄ := by
  rw [slot.cost16]
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
      intro c1 _
      split <;> step*

@[local step]
theorem dcode_spec (dlo dhi : Array Std.U8 256#usize) (d : Std.Usize) :
    slot.dcode dlo dhi d ⦃ fun _ => True ⦄ := by
  rw [slot.dcode]
  split
  · apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
    · split <;> step*
    · intro k _
      step*
  · step*


/-! ## Candidate search: search only, with the bounds the lazy pass carries -/

@[local step]
theorem gain_spec (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize) (i l d : Std.Usize)
    (hil : i.val + l.val ≤ Std.Usize.max) :
    slot.gain pref lenc dcost dlo dhi i l d ⦃ fun _ => True ⦄ := by
  rw [slot.gain]
  simp only [lift]
  step*

theorem find_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (p i cap pcap bl0 bd0 : Std.Usize) (bg0 : Std.U32) (sl0 sd0 need0 ok1 cur0 probes0 : Std.Usize)
    (hok : ok1 = 1#usize → p.val + cap.val ≤ input.length) (hip : i.val ≤ p.val)
    (hbl : bl0.val ≤ cap.val) (hbd : bd0.val ≤ 32768) :
    slot.find_loop input prev pref lenc dcost dlo dhi p i cap pcap bl0 bd0 bg0 sl0 sd0 need0
      ok1 cur0 probes0 ⦃ fun r => r.1.val ≤ cap.val ∧ r.2.1.val ≤ 32768 ⦄ := by
  rw [slot.find_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => pcap.val - s.2.2.2.2.2.2.2.val)
    (inv := fun s => s.1.val ≤ cap.val ∧ s.2.1.val ≤ 32768)
  · rintro ⟨bl, bd, bg, sl, sd, need, cur, probes⟩ ⟨hb1, hb2⟩
    simp only at hb1 hb2
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.find_loop.body]
    by_cases hok1 : ok1 = 1#usize
    · rw [if_pos hok1]
      have hpc := hok hok1
      by_cases hpr : probes < pcap
      · rw [if_pos hpr]
        by_cases hc0 : cur > 0#usize
        · rw [if_pos hc0]
          by_cases hcp : cur ≤ p
          · rw [if_pos hcp]
            step*
            apply Std.WP.spec_bind
              (Pₘ := fun (x : Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize ×
                Std.Usize × Std.Usize) => x.1.val ≤ cap.val ∧ x.2.1.val ≤ 32768)
            · split
              case isTrue hw =>
                split
                case isTrue hlt =>
                  step*
                  apply Std.WP.spec_bind
                    (Pₘ := fun (x : Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize ×
                      Std.Usize) => x.1.val ≤ cap.val ∧ x.2.1.val ≤ 32768)
                  · split
                    case isTrue =>
                      step*
                      simp only [ite_ok]
                      step*
                      refine ⟨?_, ?_⟩ <;> split <;> scalar_tac
                    case isFalse => exact ⟨hb1, hb2⟩
                  · rintro ⟨b2, d2, g2, s2, e2, n2⟩ ⟨h1, h2⟩
                    simp only at h1 h2
                    step*
                    split <;> step*
                case isFalse => simp; exact ⟨hb1, hb2⟩
              case isFalse => simp; exact ⟨hb1, hb2⟩
            · rintro ⟨b1, d1, g1, s1, e1, n1, c1⟩ ⟨h1, h2⟩
              simp only at h1 h2
              step*
          · rw [if_neg hcp]; simp; exact ⟨hb1, hb2⟩
        · rw [if_neg hc0]; simp; exact ⟨hb1, hb2⟩
      · rw [if_neg hpr]; simp; exact ⟨hb1, hb2⟩
    · rw [if_neg hok1]; simp; exact ⟨hb1, hb2⟩
  · exact ⟨hbl, hbd⟩

@[local step]
theorem find_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (p i cap start c3 floor pcap : Std.Usize) (hip : i.val ≤ p.val) :
    slot.find input prev pref lenc dcost dlo dhi p i cap start c3 floor pcap
      ⦃ fun r => r.1.val ≤ cap.val ∧ r.2.1.val ≤ 32768 ⦄ := by
  rw [slot.find]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind
    (Pₘ := fun (o : Std.Usize) => o = 1#usize → p.val + cap.val ≤ input.length)
  · split
    · step*
    · intro h; simp at h
  · intro ok1 hok
    apply Std.WP.spec_bind
      (Pₘ := fun (x : Std.Usize × Std.Usize × Std.U32 × Std.Usize) =>
        x.1.val ≤ cap.val ∧ x.2.1.val ≤ 32768)
    · split
      case isTrue hok1 =>
        have hpc := hok hok1
        split
        · split
          · step*
          · simp
        · simp
      case isFalse => simp
    · rintro ⟨bl, bd, bg, need⟩ ⟨h1, h2⟩
      exact find_loop_spec input prev pref lenc dcost dlo dhi p i cap pcap bl bd bg 0#usize
        0#usize need ok1 start 0#usize hok hip h1 h2

theorem find_in_loop_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (p i cap bl0 bd0 : Std.Usize) (bg0 : Std.U32) (sl0 sd0 need0 ok1 cur0 probes0 : Std.Usize)
    (hok : ok1 = 1#usize → p.val + cap.val ≤ input.length) (hip : i.val ≤ p.val)
    (hbl : bl0.val ≤ cap.val) (hbd : bd0.val ≤ 32768) :
    slot.find_in_loop input prev pref lenc dcost dlo dhi p i cap bl0 bd0 bg0 sl0 sd0 need0
      ok1 cur0 probes0 ⦃ fun r => r.1.val ≤ cap.val ∧ r.2.1.val ≤ 32768 ⦄ := by
  rw [slot.find_in_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.INNER_D.val - s.2.2.2.2.2.2.2.val)
    (inv := fun s => s.1.val ≤ cap.val ∧ s.2.1.val ≤ 32768)
  · rintro ⟨bl, bd, bg, sl, sd, need, cur, probes⟩ ⟨hb1, hb2⟩
    simp only at hb1 hb2
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.find_in_loop.body]
    by_cases hok1 : ok1 = 1#usize
    · rw [if_pos hok1]
      have hpc := hok hok1
      by_cases hpr : probes < slot.INNER_D
      · rw [if_pos hpr]
        by_cases hc0 : cur > 0#usize
        · rw [if_pos hc0]
          by_cases hcp : cur ≤ p
          · rw [if_pos hcp]
            step*
            apply Std.WP.spec_bind
              (Pₘ := fun (x : Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize ×
                Std.Usize × Std.Usize) => x.1.val ≤ cap.val ∧ x.2.1.val ≤ 32768)
            · split
              case isTrue hw =>
                split
                case isTrue hlt =>
                  step*
                  apply Std.WP.spec_bind
                    (Pₘ := fun (x : Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize ×
                      Std.Usize) => x.1.val ≤ cap.val ∧ x.2.1.val ≤ 32768)
                  · split
                    case isTrue =>
                      step*
                      simp only [ite_ok]
                      step*
                      refine ⟨?_, ?_⟩ <;> split <;> scalar_tac
                    case isFalse => exact ⟨hb1, hb2⟩
                  · rintro ⟨b2, d2, g2, s2, e2, n2⟩ ⟨h1, h2⟩
                    simp only at h1 h2
                    step*
                    split <;> step*
                case isFalse => simp; exact ⟨hb1, hb2⟩
              case isFalse => simp; exact ⟨hb1, hb2⟩
            · rintro ⟨b1, d1, g1, s1, e1, n1, c1⟩ ⟨h1, h2⟩
              simp only at h1 h2
              step*
          · rw [if_neg hcp]; simp; exact ⟨hb1, hb2⟩
        · rw [if_neg hc0]; simp; exact ⟨hb1, hb2⟩
      · rw [if_neg hpr]; simp; exact ⟨hb1, hb2⟩
    · rw [if_neg hok1]; simp; exact ⟨hb1, hb2⟩
  · exact ⟨hbl, hbd⟩

@[local step]
theorem find_in_spec (input : Slice Std.U8) (prev : Array Std.U32 32768#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (p i cap start c3 floor : Std.Usize) (hip : i.val ≤ p.val) :
    slot.find_in input prev pref lenc dcost dlo dhi p i cap start c3 floor
      ⦃ fun r => r.1.val ≤ cap.val ∧ r.2.1.val ≤ 32768 ⦄ := by
  rw [slot.find_in]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind
    (Pₘ := fun (o : Std.Usize) => o = 1#usize → p.val + cap.val ≤ input.length)
  · split
    · step*
    · intro h; simp at h
  · intro ok1 hok
    apply Std.WP.spec_bind
      (Pₘ := fun (x : Std.Usize × Std.Usize × Std.U32 × Std.Usize) =>
        x.1.val ≤ cap.val ∧ x.2.1.val ≤ 32768)
    · split
      case isTrue hok1 =>
        have hpc := hok hok1
        split
        · split
          · step*
          · simp
        · simp
      case isFalse => simp
    · rintro ⟨bl, bd, bg, need⟩ ⟨h1, h2⟩
      exact find_in_loop_spec input prev pref lenc dcost dlo dhi p i cap bl bd bg 0#usize
        0#usize need ok1 start 0#usize hok hip h1 h2

@[local step]
theorem insert_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize) (p : Std.Usize)
    (hp : p.val + 4 ≤ input.length) :
    slot.insert input head4 prev near p ⦃ fun _ => True ⦄ := by
  rw [slot.insert]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  simp only [lift]
  step*

/-! ## Block bookkeeping of the lazy pass: search only -/

theorem prefix_loop_spec (input : Slice Std.U8) (litc : Array Std.U32 256#usize)
    (pref : Array Std.U32 65536#usize) (p0 blen n k : Std.Usize) (acc : Std.U32)
    (hn : n.val = input.length) :
    slot.prefix_loop input litc pref p0 blen n k acc ⦃ fun _ => True ⦄ := by
  rw [slot.prefix_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => blen.val - s.2.1.val)
    (inv := fun _ => True)
  · rintro ⟨pf, kk, ac⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.prefix_loop.body, lift]
    step*
  · trivial

@[local step]
theorem prefix_spec (input : Slice Std.U8) (litc : Array Std.U32 256#usize)
    (pref : Array Std.U32 65536#usize) (p0 blen : Std.Usize) :
    slot.«prefix» input litc pref p0 blen ⦃ fun _ => True ⦄ := by
  rw [slot.«prefix»]
  step*
  exact prefix_loop_spec input litc _ p0 blen _ 0#usize 0#u32 (by simp)

theorem commit_loop_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (c1l c1d c2l c2d : Array Std.U16 32768#usize) (pref : Array Std.U32 65536#usize)
    (lenc : Array Std.U32 512#usize) (dcost : Array Std.U32 32#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 q l d blen n : Std.Usize) (has4 : Bool)
    (lim4 k : Std.Usize) (hn : n.val = input.length)
    (hq : p0.val + q.val + l.val ≤ input.length)
    (hlim : has4 = true → lim4.val + 4 ≤ input.length) :
    slot.commit_loop input head4 prev near c1l c1d c2l c2d pref lenc dcost dlo dhi p0 q l d
      blen n has4 lim4 k ⦃ fun _ => True ⦄ := by
  rw [slot.commit_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => l.val - s.2.2.2.2.2.2.2.2.val)
    (inv := fun s => s.2.2.2.2.2.2.2.1 = true → lim4.val + 4 ≤ input.length)
  · rintro ⟨hd, pv, nr, a1, a2, a3, a4, h4, kk⟩ hinv
    simp only at hinv
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.commit_loop.body]
    by_cases hkl : kk < l
    · rw [if_pos hkl]
      by_cases hl : l ≤ 258#usize
      · rw [if_pos hl]
        step*
        apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 65536#usize) ×
          (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) ×
          (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
          (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) × Bool) =>
            x.2.2.2.2.2.2.2 = h4)
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
              apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U32 65536#usize) ×
                (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) ×
                (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
                (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize)) => True)
              · by_cases hkeep : keep = 1#usize
                · rw [if_pos hkeep]
                  have hp4 := hkp hkeep
                  step*
                  · obtain ⟨r0, c3⟩ := r
                    simp only [ite_ok]
                    step*
                    apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U16 32768#usize) ×
                      (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
                      (Array Std.U16 32768#usize)) => True)
                    · repeat' split
                      all_goals step*
                    · rintro ⟨x, y, z, w⟩ _
                      step*
                  · apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U32 65536#usize) ×
                      (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) ×
                      (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize)) => True)
                    · split
                      · obtain ⟨r0, c3⟩ := r
                        simp only [ite_ok]
                        step*
                        apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U16 32768#usize) ×
                          (Array Std.U16 32768#usize)) => True)
                        · repeat' split
                          all_goals step*
                        · rintro ⟨x, y⟩ _
                          step*
                      · step*
                    · rintro ⟨x, y, z, w, v⟩ _
                      step*
                · rw [if_neg hkeep]
                  step*
              · rintro ⟨x, y, z, u, v, w, t⟩ _
                step*
          · rw [if_neg hk2]
            step*
        · rintro ⟨hd1, pv1, nr1, c11, c12, c21, c22, h41⟩ hh
          simp only at hh
          step*
      · rw [if_neg hl]; simp
    · rw [if_neg hkl]; simp
  · exact hlim

@[local step]
theorem commit_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (c1l c1d c2l c2d : Array Std.U16 32768#usize) (pref : Array Std.U32 65536#usize)
    (lenc : Array Std.U32 512#usize) (dcost : Array Std.U32 32#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 q l d blen : Std.Usize)
    (hq : p0.val + q.val + l.val ≤ input.length) :
    slot.commit input head4 prev near c1l c1d c2l c2d pref lenc dcost dlo dhi p0 q l d blen
      ⦃ fun _ => True ⦄ := by
  rw [slot.commit]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (Pₘ := fun (r : Bool × Std.Usize) =>
    r.1 = true → r.2.val + 4 ≤ input.length)
  · split
    · step*
    · simp
  · rintro ⟨h4, l4⟩ hl
    step*
    exact commit_loop_spec input head4 prev near _ _ c2l c2d pref lenc dcost dlo dhi p0 q l d
      blen (Slice.len input) h4 l4 1#usize (by simp) hq hl

theorem extend_back_loop_spec (input : Slice Std.U8) (c2l c2d : Array Std.U16 32768#usize)
    (q l d n p j go : Std.Usize) (hn : n.val = input.length) (hq : q.val ≤ p.val)
    (hl : l.val ≤ 258) (hd : d.val ≤ 32768) :
    slot.extend_back_loop input c2l c2d q l d n p j go ⦃ fun _ => True ⦄ := by
  rw [slot.extend_back_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => slot.BK.val + 1 - s.2.2.1.val + s.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨a, b, jj, gg⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.extend_back_loop.body, lift]
    step*
  · trivial

@[local step]
theorem extend_back_spec (input : Slice Std.U8) (c2l c2d : Array Std.U16 32768#usize)
    (p0 q l d : Std.Usize) (hq : p0.val + q.val ≤ input.length) (hl : l.val ≤ 258)
    (hd : d.val ≤ 32768) :
    slot.extend_back input c2l c2d p0 q l d ⦃ fun _ => True ⦄ := by
  rw [slot.extend_back]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  exact extend_back_loop_spec input c2l c2d q l d _ _ 1#usize 1#usize (by simp)
    (by scalar_tac) hl hd

theorem skip_loop_spec (c1l c2l : Array Std.U16 32768#usize) (blen i s : Std.Usize) :
    slot.skip_loop c1l c2l blen i s ⦃ fun _ => True ⦄ := by
  rw [slot.skip_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun st => slot.SKIPN.val - st.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨a, b, ii, ss⟩ _
    simp only [slot.skip_loop.body]
    step*
  · trivial

@[local step]
theorem skip_spec (c1l c2l : Array Std.U16 32768#usize) (i0 blen : Std.Usize) :
    slot.skip c1l c2l i0 blen ⦃ fun _ => True ⦄ :=
  skip_loop_spec c1l c2l blen i0 0#usize

/-! ## The lazy pass: search only; a pending match fits in the block -/

theorem lazy_loop_spec (input : Slice Std.U8) (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (pref : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (dlo dhi : Array Std.U8 256#usize)
    (c1l c1d c2l c2d : Array Std.U16 32768#usize) (p0 blen long n : Std.Usize) (has4 : Bool)
    (lim4 pl pd : Std.Usize) (pg : Std.U32) (psl psd miss i steps : Std.Usize)
    (hn : n.val = input.length) (hlim : has4 = true → lim4.val + 4 ≤ input.length)
    (hpl : pl.val ≤ 258) (hpd : pd.val ≤ 32768)
    (hpi : 3 ≤ pl.val → 1 ≤ i.val ∧ pl.val + i.val ≤ blen.val + 1) :
    slot.lazy_loop input head4 prev near pref lenc dcost dlo dhi c1l c1d c2l c2d p0 blen long
      n has4 lim4 pl pd pg psl psd miss i steps ⦃ fun _ => True ⦄ := by
  rw [slot.lazy_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 32768 - s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s => s.2.2.2.2.2.2.2.1.val ≤ 258 ∧ s.2.2.2.2.2.2.2.2.1.val ≤ 32768 ∧
      (3 ≤ s.2.2.2.2.2.2.2.1.val → 1 ≤ s.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ∧
        s.2.2.2.2.2.2.2.1.val + s.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ≤ blen.val + 1))
  · rintro ⟨hd, pv, nr, a1, a2, a3, a4, l0, d0, g0, sl0, sd0, ms, ii, st⟩ ⟨hl0, hd0, hli⟩
    simp only at hl0 hd0 hli
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    dsimp only
    rw [slot.lazy_loop.body]
    by_cases hib : ii < blen
    · rw [if_pos hib]
      step*
      apply Std.WP.spec_bind (Pₘ := fun (cap : Std.Usize) => cap.val ≤ rest.val ∧ cap.val ≤ 258)
      · split <;> step*
      intro cap ⟨hcr, hc258⟩
      step*
      apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 65536#usize) ×
        (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) × Std.Usize × Std.Usize ×
        Std.U32 × Std.Usize × Std.Usize) => x.2.2.2.1.val ≤ cap.val ∧ x.2.2.2.2.1.val ≤ 32768)
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
          · simp
        · simp
      rintro ⟨hd1, pv1, nr1, cl, cd, cg, csl, csd⟩ ⟨hcl, hcd⟩
      simp only at hcl hcd
      step*
      apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 65536#usize) ×
          (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) × (Array Std.U16 32768#usize) ×
          (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
          Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize × Std.Usize × Std.Usize) =>
        x.2.2.2.2.2.2.2.1.val ≤ 258 ∧ x.2.2.2.2.2.2.2.2.1.val ≤ 32768 ∧
        (3 ≤ x.2.2.2.2.2.2.2.1.val → 1 ≤ x.2.2.2.2.2.2.2.2.2.2.2.2.2.val ∧
          x.2.2.2.2.2.2.2.1.val + x.2.2.2.2.2.2.2.2.2.2.2.2.2.val ≤ blen.val + 1))
      · by_cases hl3 : l0 ≥ 3#usize
        · rw [if_pos hl3]
          by_cases hi1 : ii ≥ 1#usize
          · rw [if_pos hi1]
            apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U32 65536#usize) ×
                (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) ×
                (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
                (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) ×
                Std.Usize × Std.Usize × Std.U32 × Std.Usize × Std.Usize × Std.Usize) =>
              x.2.2.2.2.2.2.2.1.val ≤ 258 ∧ x.2.2.2.2.2.2.2.2.1.val ≤ 32768 ∧
              (3 ≤ x.2.2.2.2.2.2.2.1.val → 1 ≤ x.2.2.2.2.2.2.2.2.2.2.2.2.val ∧
                x.2.2.2.2.2.2.2.1.val + x.2.2.2.2.2.2.2.2.2.2.2.2.val ≤ blen.val + 1))
            · by_cases hc3 : cl ≥ 3#usize
              · rw [if_pos hc3]
                by_cases hg : cg > g0
                · rw [if_pos hg]
                  apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U16 32768#usize) ×
                    (Array Std.U16 32768#usize)) => True)
                  · split <;> step*
                  · rintro ⟨x, y⟩ _
                    step*
                · rw [if_neg hg]
                  step*
                  apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U16 32768#usize) ×
                    (Array Std.U16 32768#usize)) => True)
                  · split
                    · split <;> step*
                    · step*
                  rintro ⟨x, y⟩ _
                  apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U16 32768#usize) ×
                    (Array Std.U16 32768#usize)) => True)
                  · repeat' split
                    all_goals step*
                  rintro ⟨x2, y2⟩ _
                  apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U32 65536#usize) ×
                      (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) × (Array Std.U16 32768#usize) ×
                      (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize)) => True)
                  · split
                    · split
                      · step*
                      · step*
                    · step*
                  rintro ⟨e1, e2, e3, e4, e5, e6, e7⟩ _
                  step*
              · rw [if_neg hc3]
                step*
                apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U16 32768#usize) ×
                  (Array Std.U16 32768#usize)) => True)
                · split
                  · split <;> step*
                  · step*
                rintro ⟨x, y⟩ _
                apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U16 32768#usize) ×
                  (Array Std.U16 32768#usize)) => True)
                · repeat' split
                  all_goals step*
                rintro ⟨x2, y2⟩ _
                apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U32 65536#usize) ×
                    (Array Std.U32 32768#usize) × (Array Std.U32 65536#usize) × (Array Std.U16 32768#usize) ×
                    (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize) × (Array Std.U16 32768#usize)) => True)
                · split
                  · split
                    · step*
                    · step*
                  · step*
                rintro ⟨e1, e2, e3, e4, e5, e6, e7⟩ _
                step*
            · rintro ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ ⟨h1, h2, h3⟩
              simp only at h1 h2 h3
              step*
          · rw [if_neg hi1]
            exfalso
            have := hli (by scalar_tac)
            scalar_tac
        · rw [if_neg hl3]
          apply Std.WP.spec_bind (Pₘ := fun (x : (Array Std.U16 32768#usize) ×
            (Array Std.U16 32768#usize) × Std.Usize × Std.Usize × Std.U32 × Std.Usize ×
            Std.Usize × Std.Usize × Std.Usize) =>
            x.2.2.1.val ≤ 258 ∧ x.2.2.2.1.val ≤ 32768 ∧
            (3 ≤ x.2.2.1.val → 1 ≤ x.2.2.2.2.2.2.2.2.val ∧
              x.2.2.1.val + x.2.2.2.2.2.2.2.2.val ≤ blen.val + 1))
          · split
            · step*
              refine ⟨by scalar_tac, by scalar_tac, fun _ => ⟨by scalar_tac, by scalar_tac⟩⟩
            · step*
              apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
              · split <;> step*
              intro miss2 _
              apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U16 32768#usize) ×
                (Array Std.U16 32768#usize) × Std.Usize) => True)
              · split
                · split <;> step*
                · step*
              rintro ⟨x, y, z⟩ _
              step*
          · rintro ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ ⟨h1, h2, h3⟩
            simp only at h1 h2 h3
            step*
      · rintro ⟨hd2, pv2, nr2, b1, b2, b3, b4, pl1, pd1, pg1, psl1, psd1, ms1, i1⟩ ⟨h1, h2, h3⟩
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
    (c1l c1d c2l c2d : Array Std.U16 32768#usize) (p0 blen long : Std.Usize) :
    slot.lazy input head4 prev near pref lenc dcost dlo dhi c1l c1d c2l c2d p0 blen long
      ⦃ fun _ => True ⦄ := by
  rw [slot.lazy]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  apply Std.WP.spec_bind (Pₘ := fun (r : Bool × Std.Usize) =>
    r.1 = true → r.2.val + 4 ≤ input.length)
  · split
    · step*
    · simp
  · rintro ⟨h4, l4⟩ hl
    exact lazy_loop_spec input head4 prev near pref lenc dcost dlo dhi c1l c1d c2l c2d p0 blen
      long _ h4 l4 0#usize 0#usize 0#u32 0#usize 0#usize 0#usize 0#usize 0#usize (by simp) hl
      (by simp) (by simp) (by simp)


/-! ## The backward dynamic program: search only -/

theorem relax_run_loop_spec (cost : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (bend : Array Std.U16 512#usize) (j hi : Std.Usize) (dcs best0 : Std.U32)
    (bl0 l0 steps0 : Std.Usize) (hj : j.val ≤ 32768) :
    slot.relax_run_loop cost lenc bend j hi dcs best0 bl0 l0 steps0 ⦃ fun _ => True ⦄ := by
  rw [slot.relax_run_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 300 - s.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨best, bl, l, steps⟩ _
    simp only [slot.relax_run_loop.body, lift, ite_ok]
    step*
    all_goals first
      | scalar_tac
      | (apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
         · split
           · step*
           · split
             · step*
             · step*
               apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
               · split <;> step*
               · intro nx _
                 split
                 · step*
                 · split <;> step*
         · intro l1 _
           step*)
  · trivial

@[local step]
theorem relax_run_spec (cost : Array Std.U32 65536#usize) (lenc : Array Std.U32 512#usize)
    (bend : Array Std.U16 512#usize) (j lo hi : Std.Usize) (dcs best0 : Std.U32)
    (bl0 : Std.Usize) (hj : j.val ≤ 32768) :
    slot.relax_run cost lenc bend j lo hi dcs best0 bl0 ⦃ fun _ => True ⦄ :=
  relax_run_loop_spec cost lenc bend j hi dcs best0 bl0 lo 0#usize hj

theorem backward_loop_spec (input : Slice Std.U8) (c1l c1d c2l c2d : Array Std.U16 32768#usize)
    (cost : Array Std.U32 65536#usize)
    (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 blen : Std.Usize) (cn : Std.U32) (j : Std.Usize)
    (hb : blen.val ≤ 32768) (hpb : p0.val + blen.val ≤ input.length) (hj : j.val ≤ blen.val) :
    slot.backward_loop input c1l c1d c2l c2d cost litc lenc dcost bend dlo dhi
      p0 blen cn j ⦃ fun _ => True ⦄ := by
  rw [slot.backward_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => s.2.2.2.2.val)
    (inv := fun s => s.2.2.2.2.val ≤ blen.val)
  · rintro ⟨cl, cd, cs, cc, jj⟩ hjj
    simp only at hjj
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.backward_loop.body, lift, ite_ok]
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
    (cost : Array Std.U32 65536#usize)
    (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (p0 blen : Std.Usize) :
    slot.backward input c1l c1d c2l c2d cost litc lenc dcost bend dlo dhi p0 blen
      ⦃ fun _ => True ⦄ := by
  rw [slot.backward]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*
  exact backward_loop_spec input c1l c1d c2l c2d _ litc lenc dcost bend dlo dhi
    p0 blen 0#u32 blen (by scalar_tac) (by scalar_tac) (le_refl _)


/-! ## Symbol counts and learned costs: search only -/

theorem count_loop0_spec (lf olf : Array Std.U32 512#usize) (half s : Std.Usize) :
    slot.count_loop0 lf olf half s ⦃ fun _ => True ⦄ := by
  rw [slot.count_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 512 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.count_loop0.body]
    split
    · apply Std.WP.spec_bind (Pₘ := fun (_ : Std.U32) => True)
      · split <;> step*
      · intro v _
        step*
    · step*
  · trivial

theorem count_loop1_spec (df odf : Array Std.U32 32#usize) (half s : Std.Usize) :
    slot.count_loop1 df odf half s ⦃ fun _ => True ⦄ := by
  rw [slot.count_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 32 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.count_loop1.body]
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
    slot.count_loop2 input chl chd lf df lcode dlo dhi p0 blen n k ⦃ fun _ => True ⦄ := by
  rw [slot.count_loop2]
  apply Std.loop.spec_decr_nat (measure := fun s => blen.val - s.2.2.val) (inv := fun _ => True)
  · rintro ⟨a, b, kk⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.count_loop2.body, lift]
    step*
    all_goals scalar_tac
  · trivial

@[local step]
theorem count_spec (input : Slice Std.U8) (chl chd : Array Std.U16 32768#usize)
    (lf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize) (lcode : Array Std.U8 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (olf : Array Std.U32 512#usize)
    (odf : Array Std.U32 32#usize) (half p0 blen : Std.Usize) (hb : blen.val ≤ 32768) :
    slot.count input chl chd lf df lcode dlo dhi olf odf half p0 blen ⦃ fun _ => True ⦄ := by
  rw [slot.count]
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
    slot.keep_loop0 lf olf s ⦃ fun _ => True ⦄ := by
  rw [slot.keep_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 512 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.keep_loop0.body]
    step*
  · trivial

theorem keep_loop1_spec (df odf : Array Std.U32 32#usize) (s : Std.Usize) :
    slot.keep_loop1 df odf s ⦃ fun _ => True ⦄ := by
  rw [slot.keep_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 32 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.keep_loop1.body]
    step*
  · trivial

@[local step]
theorem keep_spec (lf olf : Array Std.U32 512#usize) (df odf : Array Std.U32 32#usize) :
    slot.keep lf df olf odf ⦃ fun _ => True ⦄ := by
  rw [slot.keep]
  apply Std.WP.spec_bind (keep_loop0_spec lf olf 0#usize)
  intro a _
  apply Std.WP.spec_bind (keep_loop1_spec df odf 0#usize)
  intro b _
  step*

theorem learn_loop0_spec (lf : Array Std.U32 512#usize) (tot : Std.U32) (s : Std.Usize) :
    slot.learn_loop0 lf tot s ⦃ fun _ => True ⦄ := by
  rw [slot.learn_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 286 - s.2.val) (inv := fun _ => True)
  · rintro ⟨t, k⟩ _
    simp only [slot.learn_loop0.body, lift]
    step*
  · trivial

theorem learn_loop1_spec (lf : Array Std.U32 512#usize) (litc : Array Std.U32 256#usize)
    (bias tot : Std.U32) (s : Std.Usize) :
    slot.learn_loop1 lf litc bias tot s ⦃ fun _ => True ⦄ := by
  rw [slot.learn_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 256 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.learn_loop1.body, lift]
    step*
  · trivial

theorem learn_loop2_spec (lf : Array Std.U32 512#usize) (bias tot : Std.U32)
    (cc : Array Std.U32 32#usize) (c : Std.Usize) :
    slot.learn_loop2 lf bias tot cc c ⦃ fun _ => True ⦄ := by
  rw [slot.learn_loop2]
  apply Std.loop.spec_decr_nat (measure := fun s => 29 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.learn_loop2.body, lift]
    step*
  · trivial

theorem learn_loop3_spec (lenc : Array Std.U32 512#usize) (lcode lextra : Array Std.U8 512#usize)
    (cc : Array Std.U32 32#usize) (l : Std.Usize) :
    slot.learn_loop3 lenc lcode lextra cc l ⦃ fun _ => True ⦄ := by
  rw [slot.learn_loop3]
  apply Std.loop.spec_decr_nat (measure := fun s => 259 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.learn_loop3.body, lift]
    step*
  · trivial

theorem learn_loop4_spec (df : Array Std.U32 32#usize) (c : Std.Usize) (dt : Std.U32) :
    slot.learn_loop4 df c dt ⦃ fun _ => True ⦄ := by
  rw [slot.learn_loop4]
  apply Std.loop.spec_decr_nat (measure := fun s => 30 - s.1.val) (inv := fun _ => True)
  · rintro ⟨k, t⟩ _
    simp only [slot.learn_loop4.body, lift]
    step*
  · trivial

theorem learn_loop5_spec (df dcost : Array Std.U32 32#usize) (dext : Array Std.U8 32#usize)
    (c : Std.Usize) (dt : Std.U32) :
    slot.learn_loop5 df dcost dext c dt ⦃ fun _ => True ⦄ := by
  rw [slot.learn_loop5]
  apply Std.loop.spec_decr_nat (measure := fun s => 30 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.learn_loop5.body, lift]
    step*
  · trivial

@[local step]
theorem learn_spec (lf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize)
    (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (lcode lextra : Array Std.U8 512#usize)
    (dext : Array Std.U8 32#usize) (bias : Std.U32) :
    slot.learn lf df litc lenc dcost lcode lextra dext bias ⦃ fun _ => True ⦄ := by
  rw [slot.learn]
  apply Std.WP.spec_bind (learn_loop0_spec lf 1#u32 0#usize)
  intro t _
  apply Std.WP.spec_bind (learn_loop1_spec lf litc bias t 0#usize)
  intro a _
  apply Std.WP.spec_bind (learn_loop2_spec lf bias t _ 0#usize)
  intro cc _
  apply Std.WP.spec_bind (learn_loop3_spec lenc lcode lextra cc 3#usize)
  intro b _
  apply Std.WP.spec_bind (learn_loop4_spec df 0#usize 1#u32)
  intro u _
  apply Std.WP.spec_bind (learn_loop5_spec df dcost dext 0#usize u)
  intro c _
  step*

/-! ## Code tables and starting costs: search only -/

theorem len_tables_loop_spec (lbase : Array Std.U16 32#usize) (lext : Array Std.U8 32#usize)
    (lcode lextra : Array Std.U8 512#usize) (bend : Array Std.U16 512#usize) (c l : Std.Usize)
    (hc0 : c.val ≤ 28) :
    slot.len_tables_loop lbase lext lcode lextra bend c l ⦃ fun _ => True ⦄ := by
  rw [slot.len_tables_loop]
  apply Std.loop.spec_decr_nat (measure := fun s => 259 - s.2.2.2.2.val)
    (inv := fun s => s.2.2.2.1.val ≤ 28)
  · rintro ⟨a, b, e, cc, ll⟩ hc
    simp only at hc
    simp only [slot.len_tables_loop.body, lift]
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
    slot.code_from_loop dbase d c ⦃ fun _ => True ⦄ := by
  rw [slot.code_from_loop]
  apply Std.loop.spec_decr_nat (measure := fun s => 29 - s.val) (inv := fun _ => True)
  · intro cc _
    simp only [slot.code_from_loop.body]
    step*
  · trivial

@[local step]
theorem code_from_spec (dbase : Array Std.U16 32#usize) (d c0 : Std.Usize) :
    slot.code_from dbase d c0 ⦃ fun _ => True ⦄ :=
  code_from_loop_spec dbase d c0

theorem dist_tables_loop0_spec (dbase : Array Std.U16 32#usize) (dlo : Array Std.U8 256#usize)
    (c d : Std.Usize) (hd : 1 ≤ d.val) :
    slot.dist_tables_loop0 dbase dlo c d ⦃ fun _ => True ⦄ := by
  rw [slot.dist_tables_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => 257 - s.2.2.val)
    (inv := fun s => 1 ≤ s.2.2.val)
  · rintro ⟨a, cc, dd⟩ h
    simp only at h
    simp only [slot.dist_tables_loop0.body]
    step*
    all_goals scalar_tac
  · exact hd

theorem dist_tables_loop1_spec (dbase : Array Std.U16 32#usize) (dhi : Array Std.U8 256#usize)
    (c k : Std.Usize) :
    slot.dist_tables_loop1 dbase dhi c k ⦃ fun _ => True ⦄ := by
  rw [slot.dist_tables_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 256 - s.2.2.val) (inv := fun _ => True)
  · rintro ⟨a, cc, kk⟩ _
    simp only [slot.dist_tables_loop1.body]
    step*
  · trivial

@[local step]
theorem dist_tables_spec (dbase : Array Std.U16 32#usize) (dlo dhi : Array Std.U8 256#usize) :
    slot.dist_tables dbase dlo dhi ⦃ fun _ => True ⦄ := by
  rw [slot.dist_tables]
  apply Std.WP.spec_bind (dist_tables_loop0_spec dbase dlo 0#usize 1#usize (by simp))
  intro a _
  apply Std.WP.spec_bind (dist_tables_loop1_spec dbase dhi 0#usize 0#usize)
  intro b _
  step*

@[local step]
theorem len_tables_spec (lbase : Array Std.U16 32#usize) (lext : Array Std.U8 32#usize)
    (lcode lextra : Array Std.U8 512#usize) (bend : Array Std.U16 512#usize) :
    slot.len_tables lbase lext lcode lextra bend ⦃ fun _ => True ⦄ :=
  len_tables_loop_spec lbase lext lcode lextra bend 0#usize 3#usize (by simp)

@[local step]
theorem tables_spec (lcode lextra : Array Std.U8 512#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (dext : Array Std.U8 32#usize) :
    slot.tables lcode lextra bend dlo dhi dext ⦃ fun _ => True ⦄ := by
  rw [slot.tables]
  step*

theorem seed_loop0_spec (input : Slice Std.U8) (lim : Std.Usize) (hist : Array Std.U32 256#usize)
    (i : Std.Usize) (hl : lim.val ≤ input.length) :
    slot.seed_loop0 input lim hist i ⦃ fun _ => True ⦄ := by
  rw [slot.seed_loop0]
  apply Std.loop.spec_decr_nat (measure := fun s => lim.val - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.seed_loop0.body, lift]
    step*
  · trivial

theorem seed_loop1_spec (litc hist : Array Std.U32 256#usize) (tot : Std.U32) (s : Std.Usize) :
    slot.seed_loop1 litc hist tot s ⦃ fun _ => True ⦄ := by
  rw [slot.seed_loop1]
  apply Std.loop.spec_decr_nat (measure := fun s => 256 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.seed_loop1.body]
    step*
  · trivial

theorem seed_loop2_spec (lenc : Array Std.U32 512#usize) (lextra : Array Std.U8 512#usize)
    (l : Std.Usize) :
    slot.seed_loop2 lenc lextra l ⦃ fun _ => True ⦄ := by
  rw [slot.seed_loop2]
  apply Std.loop.spec_decr_nat (measure := fun s => 259 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.seed_loop2.body, lift]
    step*
  · trivial

theorem seed_loop3_spec (dcost : Array Std.U32 32#usize) (dext : Array Std.U8 32#usize)
    (c : Std.Usize) :
    slot.seed_loop3 dcost dext c ⦃ fun _ => True ⦄ := by
  rw [slot.seed_loop3]
  apply Std.loop.spec_decr_nat (measure := fun s => 30 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.seed_loop3.body, lift]
    step*
  · trivial

@[local step]
theorem seed_spec (input : Slice Std.U8) (litc : Array Std.U32 256#usize)
    (lenc : Array Std.U32 512#usize) (dcost : Array Std.U32 32#usize)
    (lextra : Array Std.U8 512#usize) (dext : Array Std.U8 32#usize) :
    slot.seed input litc lenc dcost lextra dext ⦃ fun _ => True ⦄ := by
  rw [slot.seed]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  simp only [ite_ok]
  have hl : (if Slice.len input < 32768#usize then Slice.len input else 32768#usize).val
      ≤ input.length := by
    split <;> scalar_tac
  generalize (if Slice.len input < 32768#usize then Slice.len input else 32768#usize) = lim at hl ⊢
  apply Std.WP.spec_bind (seed_loop0_spec input lim _ 0#usize hl)
  intro h _
  step*
  apply Std.WP.spec_bind (seed_loop1_spec litc h _ 0#usize)
  intro a _
  apply Std.WP.spec_bind (seed_loop2_spec lenc lextra 3#usize)
  intro b _
  apply Std.WP.spec_bind (seed_loop3_spec dcost dext 0#usize)
  intro c _
  step*

theorem add_bias_loop0_spec (litc : Array Std.U32 256#usize) (bias : Std.U32) (s : Std.Usize) :
    slot.add_bias_loop0 litc bias s ⦃ fun _ => True ⦄ := by
  rw [slot.add_bias_loop0]
  apply Std.loop.spec_decr_nat (measure := fun st => 256 - st.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.add_bias_loop0.body, lift]
    step*
  · trivial

theorem add_bias_loop1_spec (lenc : Array Std.U32 512#usize) (bias : Std.U32) (l : Std.Usize) :
    slot.add_bias_loop1 lenc bias l ⦃ fun _ => True ⦄ := by
  rw [slot.add_bias_loop1]
  apply Std.loop.spec_decr_nat (measure := fun st => 259 - st.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    simp only [slot.add_bias_loop1.body, lift]
    step*
  · trivial

@[local step]
theorem add_bias_spec (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (bias : Std.U32) :
    slot.add_bias litc lenc bias ⦃ fun _ => True ⦄ := by
  rw [slot.add_bias]
  apply Std.WP.spec_bind (add_bias_loop0_spec litc bias 0#usize)
  intro a _
  apply Std.WP.spec_bind (add_bias_loop1_spec lenc bias 3#usize)
  intro b _
  step*

theorem avg_lit_loop_spec (input : Slice Std.U8) (litc : Array Std.U32 256#usize)
    (lim : Std.Usize) (s : Std.U64) (i : Std.Usize) (hl : lim.val ≤ input.length) :
    slot.avg_lit_loop input litc lim s i ⦃ fun _ => True ⦄ := by
  rw [slot.avg_lit_loop]
  apply Std.loop.spec_decr_nat (measure := fun st => lim.val - st.2.val) (inv := fun _ => True)
  · rintro ⟨a, k⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.avg_lit_loop.body, lift]
    step*
  · trivial

@[local step]
theorem avg_lit_spec (input : Slice Std.U8) (litc : Array Std.U32 256#usize) :
    slot.avg_lit input litc ⦃ fun _ => True ⦄ := by
  rw [slot.avg_lit]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  simp only [ite_ok]
  have hl : (if Slice.len input < 32768#usize then Slice.len input else 32768#usize).val
      ≤ input.length ∧
      (if Slice.len input < 32768#usize then Slice.len input else 32768#usize).val ≤ 32768 := by
    constructor <;> split <;> scalar_tac
  generalize (if Slice.len input < 32768#usize then Slice.len input else 32768#usize) = lim at hl ⊢
  obtain ⟨hl1, hl2⟩ := hl
  apply Std.WP.spec_bind (avg_lit_loop_spec input litc lim 0#u64 0#usize hl1)
  intro s _
  simp only [lift]
  step*

/-! ## The emission: every chosen match is re-verified, so the template's invariant holds -/

theorem verified_spec (input : Slice Std.U8) (pos d ch k blen : Std.Usize)
    (hlen : pos.val + (blen.val - k.val) ≤ input.length) (hk : k.val ≤ blen.val)
    (hb : blen.val ≤ 32768) :
    slot.verified input pos d ch k blen ⦃ fun b => b = true →
      3 ≤ ch.val ∧ ch.val ≤ 258 ∧ 1 ≤ d.val ∧ d.val ≤ 32768 ∧ d.val ≤ pos.val ∧
      k.val + ch.val ≤ blen.val ∧ Matches input (pos.val - d.val) pos.val ch.val ⦄ := by
  rw [slot.verified]
  have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
  step*

theorem emit_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (chl chd : Array Std.U16 32768#usize) (p0 blen ntok0 k0 : Std.Usize)
    (hblen : p0.val + blen.val ≤ input.length) (hb : blen.val ≤ 32768)
    (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ blen.val) (hntok : ntok0.val ≤ p0.val + k0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take (p0.val + k0.val))) :
    slot.emit_loop input out0 chl chd p0 blen ntok0 k0 ⦃ fun r =>
      r.1.val ≤ p0.val + blen.val ∧ r.2.length = out0.length ∧
      LZ77.decode (toks r.2 r.1.val) = some ((bytes input).take (p0.val + blen.val)) ⦄ := by
  rw [slot.emit_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => blen.val - s.2.2.val)
    (inv := fun s =>
      s.2.2.val ≤ blen.val ∧ s.2.1.val ≤ p0.val + s.2.2.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.1.val) = some ((bytes input).take (p0.val + s.2.2.val)))
  · rintro ⟨out, ntok, k⟩ ⟨hkb, hnt, hlen, hde⟩
    simp only at hkb hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.emit_loop.body]
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


/-! ## The block loop: tokens so far decode to the input before this block -/

theorem parse_loop_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n : Std.Usize)
    (lcode lextra : Array Std.U8 512#usize) (bend : Array Std.U16 512#usize)
    (dlo dhi : Array Std.U8 256#usize) (dext : Array Std.U8 32#usize)
    (litc : Array Std.U32 256#usize) (lenc : Array Std.U32 512#usize)
    (dcost : Array Std.U32 32#usize) (long : Std.Usize) (bias : Std.U32)
    (head4 : Array Std.U32 65536#usize)
    (prev : Array Std.U32 32768#usize) (near : Array Std.U32 65536#usize)
    (c1l c1d c2l c2d : Array Std.U16 32768#usize)
    (cost : Array Std.U32 65536#usize)
    (lf : Array Std.U32 512#usize) (df : Array Std.U32 32#usize)
    (olf : Array Std.U32 512#usize) (odf : Array Std.U32 32#usize) (ntok0 p00 : Std.Usize)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hpos : p00.val ≤ n.val) (hntok : ntok0.val ≤ p00.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take p00.val)) :
    slot.parse_loop input out0 n lcode lextra bend dlo dhi dext litc lenc dcost long bias head4 prev
      near c1l c1d c2l c2d cost lf df olf odf ntok0 p00 ⦃ fun r =>
        r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
        LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.parse_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s =>
      s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ≤ n.val ∧
      s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val ≤ s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.val) =
        some ((bytes input).take s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.val))
  · rintro ⟨out, lc, le, dc, hd, pv, nr, a1, a2, a3, a4, cs, l1, d1, ol1, od1, ntok, p0⟩
      ⟨hp, hnt, hlen, hde⟩
    simp only at hp hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop.body]
    split
    case isTrue hlt =>
      step*
      simp only [ite_ok]
      have hbl : (if rest > slot.BLOCK then slot.BLOCK else rest).val ≤ 32768 ∧
          (if rest > slot.BLOCK then slot.BLOCK else rest).val ≤ rest.val ∧
          1 ≤ (if rest > slot.BLOCK then slot.BLOCK else rest).val := by
        split <;> scalar_tac
      generalize (if rest > slot.BLOCK then slot.BLOCK else rest) = blen at hbl ⊢
      obtain ⟨hb1, hb2, hb3⟩ := hbl
      step*
      apply Std.WP.spec_bind (Pₘ := fun (_ : (Array Std.U32 256#usize) ×
        (Array Std.U32 512#usize) × (Array Std.U32 32#usize) × (Array Std.U32 512#usize) ×
        (Array Std.U32 32#usize) × (Array Std.U32 512#usize) × (Array Std.U32 32#usize)) => True)
      · split
        · step*
        · step*
      rintro ⟨litc1, lenc1, dcost1, lf1, df1, olf1, odf1⟩ _
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

/-! ## The obligation -/

theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)
    (hlen : input.length ≤ out.length) :
    slot.parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      LZ77.Valid (bytes input) (toks r.2 r.1.val) ⦄ := by
  rw [slot.parse]
  simp only [ite_ok]
  step*
  exact parse_loop_spec input out _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0#usize 0#usize
    (by simp) hlen (by scalar_tac) (by scalar_tac) (by simp [toks, LZ77.decode])

end Submission
