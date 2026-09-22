import Lz77
import Slot

/-!
The optimal-parse-with-cost-iteration proof. The search side is the lazy proof with 24 probes. The
dynamic program (`match_bits`, `relax`, the forward and backward block loops) is
search too: postcondition `True`, only termination and bounds. The emission loop
re-verifies every chosen match with `match_len`, so its invariant is the template's.
-/

namespace Submission
open Aeneas Aeneas.Std Result ControlFlow

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr
  Matches Found Pending emitted emitted_ge emitted_lt pending_of_found emit_lit emit_match ite_ok)

/-! ## The hash: in range, and nothing else -/

@[local step]
theorem hash3_spec (a b c : Std.U8) :
    slot.hash3 a b c ⦃ fun h => h.val < 32768 ⦄ := by
  prove_hash3

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

/-! ## The search: `Found` is the postcondition and the invariant -/

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
          apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
          · split <;> step*
          · intro cur1 _
            step*
            rcases Nat.lt_or_ge l.val 3 with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h, by scalar_tac, by scalar_tac, by scalar_tac,
                by scalar_tac, by scalar_tac,
                by rw [show pos.val - i.val = cpos.val by scalar_tac]; exact l_post2⟩
        case isFalse =>
          apply Std.WP.spec_bind (Pₘ := fun (_ : Std.Usize) => True)
          · split <;> step*
          · intro cur1 _
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

/-! ## The cost model and the dynamic program: search, so only totality and bounds -/

theorem match_bits_loop_spec (dist : Std.Usize) (extra0 : Std.U32) (top0 : Std.Usize)
    (h0 : extra0.val ≤ 13 ∧ top0.val ≤ 4 * 2 ^ extra0.val) :
    slot.match_bits_loop dist extra0 top0 ⦃ fun r => r.val ≤ 13 ⦄ := by
  rw [slot.match_bits_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 13 - s.1.val)
    (inv := fun s => s.1.val ≤ 13 ∧ s.2.val ≤ 4 * 2 ^ s.1.val)
  · rintro ⟨extra, top⟩ ⟨hext, htop⟩
    simp only at hext htop
    simp only [slot.match_bits_loop.body]
    split
    case isTrue =>
      split
      case isTrue hlt =>
        have hpow : 4 * 2 ^ extra.val ≤ 4 * 2 ^ 12 := by
          have : extra.val ≤ 12 := by scalar_tac
          exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) this)
        have htop' : top.val ≤ 16384 := by omega
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show extra1.val = extra.val + 1 by scalar_tac, Nat.pow_succ]
        scalar_tac
      case isFalse => step*
    case isFalse => step*
  · exact h0

@[local step]
theorem match_bits_spec (len dist : Std.Usize) :
    slot.match_bits len dist ⦃ fun r => r.val ≤ 120 ⦄ := by
  rw [slot.match_bits]
  apply Std.WP.spec_bind (Pₘ := fun (lb : Std.U32) => lb.val ≤ 12)
  · split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split)
      <;> simp only [Std.WP.spec_ok] <;> scalar_tac
  · intro lb hlb
    apply Std.WP.spec_bind (match_bits_loop_spec dist 0#u32 4#usize (by simp))
    intro extra hextra
    step*

theorem relax_loop_spec (cost : Slice Std.U32) (i dist stop : Std.Usize) (b0 : Std.U32)
    (choice0 l0 : Std.Usize)
    (hcost : cost.length = 32769) (hstop : i.val + stop.val ≤ 32768) :
    slot.relax_loop cost i dist b0 choice0 l0 stop ⦃ fun _ => True ⦄ := by
  rw [slot.relax_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => stop.val - s.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨best, choice, l⟩ _
    simp only [slot.relax_loop.body]
    split
    case isTrue hlt =>
      have hmax : cost.length ≤ Std.Usize.max := Std.Slice.length_ineq cost
      step*
      simp only [lift, ite_ok]
      step*
    case isFalse => step*
  · trivial

@[local step]
theorem relax_spec (cost : Slice Std.U32) (i mlen dist blen : Std.Usize)
    (hcost : cost.length = 32769) (hi : i.val < blen.val) (hblen : blen.val ≤ 32768)
    (hmlen : mlen.val ≤ 4294967295) :
    slot.relax cost i mlen dist blen ⦃ fun _ => True ⦄ := by
  rw [slot.relax]
  have hmax : cost.length ≤ Std.Usize.max := Std.Slice.length_ineq cost
  simp only [lift, ite_ok]
  step*
  all_goals first
    | scalar_tac
    | (apply relax_loop_spec cost i dist _ _ _ _ hcost
       split <;> scalar_tac)

/-! ## The cost model: code tables, symbol costs, the second relaxation. Search only: every
postcondition is `True`, the lemmas exist so the loops are total and the indices in range. -/

@[local step]
theorem quarter_mult_spec (c : Std.U32) : slot.quarter_mult c ⦃ fun m => m.val ≤ 431 ⦄ := by
  rw [slot.quarter_mult]
  step*

theorem sym_cost_loop_spec (c0 : Std.U32) (scaled0 target : Std.U64) :
    slot.sym_cost_loop c0 scaled0 target ⦃ fun _ => True ⦄ := by
  rw [slot.sym_cost_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 60 - s.1.val)
    (inv := fun _ => True)
  · rintro ⟨c, scaled⟩ _
    simp only [slot.sym_cost_loop.body]
    step*
  · trivial

@[local step]
theorem sym_cost_spec (freq total : Std.U32) : slot.sym_cost freq total ⦃ fun _ => True ⦄ := by
  rw [slot.sym_cost]
  simp only [lift, ite_ok]
  step*
  all_goals first
    | scalar_tac
    | (apply Std.WP.spec_bind (sym_cost_loop_spec _ _ _)
       intro c _
       step*)

theorem len_code_loop_spec (len : Std.Usize) :
    slot.len_code_loop0 len 1#u32 11#usize 8#usize 8#usize ⦃ fun r =>
      r.1.val ≤ 5 ∧ r.2.1.val ≤ 131 ∧ r.2.2.1.val ≤ 24 ∧ 8 ≤ r.2.2.2.val ∧ r.2.2.2.val ≤ 128 ⦄ := by
  rw [slot.len_code_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 5 - s.1.val)
    (inv := fun s =>
        (s.1.val = 1 ∧ s.2.1.val = 11 ∧ s.2.2.1.val = 8 ∧ s.2.2.2.val = 8) ∨
        (s.1.val = 2 ∧ s.2.1.val = 19 ∧ s.2.2.1.val = 12 ∧ s.2.2.2.val = 16) ∨
        (s.1.val = 3 ∧ s.2.1.val = 35 ∧ s.2.2.1.val = 16 ∧ s.2.2.2.val = 32) ∨
        (s.1.val = 4 ∧ s.2.1.val = 67 ∧ s.2.2.1.val = 20 ∧ s.2.2.2.val = 64) ∨
        (s.1.val = 5 ∧ s.2.1.val = 131 ∧ s.2.2.1.val = 24 ∧ s.2.2.2.val = 128))
  · rintro ⟨extra, base, idx, width⟩ hs
    simp only at hs
    simp only [slot.len_code_loop0.body]
    step*
    all_goals scalar_tac
  · simp

theorem len_code_loop1_spec (len step off0 t0 : Std.Usize)
    (hlen : len.val < 258) (hstep : step.val ≤ 32) (ht : t0.val ≤ 600) :
    slot.len_code_loop1 len step off0 t0 ⦃ fun r => r.val ≤ off0.val + 3 ⦄ := by
  rw [slot.len_code_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 3 - s.1.val)
    (inv := fun s => s.2.val ≤ 600 ∧ (s.1.val ≤ off0.val + 3))
  · rintro ⟨off, tt⟩ ⟨ht, ho⟩
    simp only at ht ho
    simp only [slot.len_code_loop1.body]
    step*
    all_goals scalar_tac
  · exact ⟨ht, by scalar_tac⟩

@[local step]
theorem len_code_spec (len : Std.Usize) :
    slot.len_code len ⦃ fun r => r.1.val ≤ 28 ∧ r.2.val ≤ 5 ⦄ := by
  rw [slot.len_code]
  simp only [ite_ok]
  step*
  all_goals first
    | scalar_tac
    | (split <;> scalar_tac)
    | (apply Std.WP.spec_bind (len_code_loop_spec len)
       rintro ⟨extra, base, idx, width⟩ ⟨he, hb, hi, hw1, hw2⟩
       simp only at he hb hi hw1 hw2
       try simp only [ite_ok]
       step*
       all_goals first
         | scalar_tac
         | (split <;> scalar_tac)
         | (apply Std.WP.spec_bind (len_code_loop1_spec len _ 0#usize base
              (by scalar_tac) (by scalar_tac) (by scalar_tac))
            intro off hoff
            try simp only [ite_ok]
            step*
            all_goals first
              | scalar_tac
              | (split_ifs <;> dsimp only <;> exact ⟨by scalar_tac, by scalar_tac⟩)))

theorem dist_code_loop_spec (dist : Std.Usize) :
    slot.dist_code_loop0 dist 1#u32 5#usize 4#usize 4#usize ⦃ fun r =>
      r.1.val ≤ 13 ∧ r.2.1.val ≤ 32769 ∧ r.2.2.1.val ≤ 28 ∧ 4 ≤ r.2.2.2.val ∧ r.2.2.2.val ≤ 32768 ⦄ := by
  rw [slot.dist_code_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 13 - s.1.val)
    (inv := fun s => s.1.val ≤ 13 ∧ s.2.1.val = 1 + s.2.2.2.val ∧ s.2.2.1.val = 2 * s.1.val + 2 ∧
      4 ≤ s.2.2.2.val ∧ s.2.2.2.val ≤ 32768)
  · rintro ⟨extra, base, idx, width⟩ ⟨h1, h2, h3, h4, h5⟩
    simp only at h1 h2 h3 h4 h5
    simp only [slot.dist_code_loop0.body]
    step*
    all_goals scalar_tac
  · simp

theorem dist_code_loop1_spec (dist step off0 t0 : Std.Usize)
    (hd : dist.val ≤ 32768) (hstep : step.val ≤ 16384) (ht : t0.val ≤ 65536) :
    slot.dist_code_loop1 dist step off0 t0 ⦃ fun r => r.val ≤ off0.val + 1 ⦄ := by
  rw [slot.dist_code_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 1 - s.1.val)
    (inv := fun s => s.2.val ≤ 65536 ∧ s.1.val ≤ off0.val + 1)
  · rintro ⟨off, tt⟩ ⟨ht, ho⟩
    simp only at ht ho
    simp only [slot.dist_code_loop1.body]
    step*
    all_goals scalar_tac
  · exact ⟨ht, by scalar_tac⟩

@[local step]
theorem dist_code_spec (dist : Std.Usize) :
    slot.dist_code dist ⦃ fun r => r.1.val ≤ 29 ∧ r.2.val ≤ 13 ⦄ := by
  rw [slot.dist_code]
  simp only [ite_ok]
  have hcl : (if dist > 32768#usize then 32768#usize else dist).val ≤ 32768 := by
    split <;> scalar_tac
  generalize (if dist > 32768#usize then 32768#usize else dist) = d at hcl ⊢
  step*
  all_goals first
    | scalar_tac
    | (split <;> scalar_tac)
    | (apply Std.WP.spec_bind (dist_code_loop_spec _)
       rintro ⟨extra, base, idx, width⟩ ⟨he, hb, hi, hw1, hw2⟩
       simp only at he hb hi hw1 hw2
       try simp only [ite_ok]
       step*
       all_goals first
         | scalar_tac
         | (split <;> scalar_tac)
         | (apply Std.WP.spec_bind (dist_code_loop1_spec d _ 0#usize base
              hcl (by scalar_tac) (by scalar_tac))
            intro off hoff
            try simp only [ite_ok]
            step*
            all_goals first
              | scalar_tac
              | (split_ifs <;> dsimp only <;> exact ⟨by scalar_tac, by scalar_tac⟩)))

theorem costs_from_loop_spec (freq cost0 : Slice Std.U32) (n : Std.Usize) (total : Std.U32)
    (s0 : Std.Usize) (hf : n.val < freq.length) (hc : n.val ≤ cost0.length) :
    slot.costs_from_loop freq cost0 n total s0 ⦃ fun _ => True ⦄ := by
  rw [slot.costs_from_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.val)
    (inv := fun s => s.1.length = cost0.length)
  · rintro ⟨cost, s⟩ hlen
    simp only at hlen
    simp only [slot.costs_from_loop.body]
    step*
    all_goals first
      | scalar_tac
      | (refine ⟨?_, by scalar_tac⟩; rw [s1_post]; simpa [Std.Slice.set_val_eq] using hlen)
      | exact hlen
  · rfl

@[local step]
theorem costs_from_spec (freq cost : Slice Std.U32) (n : Std.Usize)
    (hf : n.val < freq.length) (hc : n.val ≤ cost.length) :
    slot.costs_from freq cost n ⦃ fun _ => True ⦄ := by
  rw [slot.costs_from]
  step*
  exact costs_from_loop_spec freq cost n _ 0#usize hf hc

@[local step]
theorem match_cost_spec (ll_cost d_cost : Slice Std.U32) (len dist : Std.Usize)
    (hl : ll_cost.length = 286) (hd : d_cost.length = 30) :
    slot.match_cost ll_cost d_cost len dist ⦃ fun _ => True ⦄ := by
  rw [slot.match_cost]
  simp only [lift, ite_ok]
  step*
  all_goals first
    | scalar_tac
    | (rcases lc with ⟨lci, lce⟩
       rcases dc with ⟨dci, dce⟩
       simp only at lc_post1 lc_post2 dc_post1 dc_post2
       try simp only [ite_ok]
       step*
       all_goals first | scalar_tac | (split <;> scalar_tac))

theorem relax2_loop_spec (cost ll_cost d_cost : Slice Std.U32) (i dist stop : Std.Usize)
    (b0 : Std.U32) (choice0 l0 : Std.Usize)
    (hcost : cost.length = 32769) (hl : ll_cost.length = 286) (hd : d_cost.length = 30)
    (hstop : i.val + stop.val ≤ 32768) :
    slot.relax2_loop cost ll_cost d_cost i dist b0 choice0 l0 stop ⦃ fun _ => True ⦄ := by
  rw [slot.relax2_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => stop.val - s.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨best, choice, l⟩ _
    simp only [slot.relax2_loop.body]
    split
    case isTrue hlt =>
      have hmax : cost.length ≤ Std.Usize.max := Std.Slice.length_ineq cost
      step*
      simp only [lift, ite_ok]
      step*
    case isFalse => step*
  · trivial

@[local step]
theorem relax2_spec (cost ll_cost d_cost : Slice Std.U32) (byte : Std.U8) (i mlen dist blen : Std.Usize)
    (hcost : cost.length = 32769) (hl : ll_cost.length = 286) (hd : d_cost.length = 30)
    (hi : i.val < blen.val) (hblen : blen.val ≤ 32768) :
    slot.relax2 cost ll_cost d_cost byte i mlen dist blen ⦃ fun _ => True ⦄ := by
  rw [slot.relax2]
  have hmax : cost.length ≤ Std.Usize.max := Std.Slice.length_ineq cost
  simp only [lift, ite_ok]
  step*
  all_goals first
    | scalar_tac
    | (apply relax2_loop_spec cost ll_cost d_cost i dist _ _ _ _ hcost hl hd
       split <;> scalar_tac)

/-! ## The forward pass: candidates at every position of the block -/

theorem parse_loop0_loop0_spec (input : Slice Std.U8)
    (head0 prev0 mlen0 mdist0 : Array Std.U32 32768#usize)
    (pos0 lim blen i0 : Std.Usize) (has30 : Bool)
    (hlim : has30 = true → lim.val + 3 ≤ input.length)
    (hblen : pos0.val + blen.val ≤ input.length) (hb : blen.val ≤ 32768) :
    slot.parse_loop0_loop0 input head0 prev0 mlen0 mdist0 pos0 has30 lim blen i0
      ⦃ fun _ => True ⦄ := by
  rw [slot.parse_loop0_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => blen.val - s.2.2.2.2.val)
    (inv := fun _ => True)
  · rintro ⟨hd, pv, ml, md, i⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0_loop0.body, lift, ite_ok]
    step*
    split
    · have hlim3 := hlim (by assumption)
      split
      · step*
        case n => exact Std.Slice.len input
        all_goals first
          | scalar_tac
          | (split <;> scalar_tac)
          | simp
          | (rcases x with ⟨l1, d1⟩
             step*)
      · step*
    · step*
  · trivial

/-! ## The backward pass: costs from every position to the block end -/

theorem parse_loop0_loop1_spec (mlen mdist : Array Std.U32 32768#usize)
    (cost0 choice0 : Array Std.U32 32769#usize) (blen j0 : Std.Usize)
    (hb : blen.val ≤ 32768) (hj : j0.val ≤ blen.val) :
    slot.parse_loop0_loop1 mlen mdist cost0 choice0 blen j0 ⦃ fun _ => True ⦄ := by
  rw [slot.parse_loop0_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => s.2.2.val)
    (inv := fun s => s.2.2.val ≤ blen.val)
  · rintro ⟨cost, choice, j⟩ hj
    simp only at hj
    simp only [slot.parse_loop0_loop1.body]
    split
    case isTrue hpos =>
      step*
    case isFalse => trivial
  · exact hj

/-! ## Counting the first path's symbols and relaxing again: search only -/

@[local step]
theorem parse_loop0_loop2_spec (ll_freq : Array Std.U32 287#usize) (s0 : Std.Usize) :
    slot.parse_loop0_loop2 ll_freq s0 ⦃ fun _ => True ⦄ := by
  rw [slot.parse_loop0_loop2]
  apply Std.loop.spec_decr_nat (measure := fun s => 287 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, s⟩ _
    simp only [slot.parse_loop0_loop2.body]
    step*
  · trivial

@[local step]
theorem parse_loop0_loop3_spec (d_freq : Array Std.U32 31#usize) (s0 : Std.Usize) :
    slot.parse_loop0_loop3 d_freq s0 ⦃ fun _ => True ⦄ := by
  rw [slot.parse_loop0_loop3]
  apply Std.loop.spec_decr_nat (measure := fun s => 31 - s.2.val) (inv := fun _ => True)
  · rintro ⟨a, s⟩ _
    simp only [slot.parse_loop0_loop3.body]
    step*
  · trivial

@[local step]
theorem parse_loop0_loop4_spec (input : Slice Std.U8) (mdist : Array Std.U32 32768#usize)
    (choice : Array Std.U32 32769#usize) (ll_freq : Array Std.U32 287#usize)
    (d_freq : Array Std.U32 31#usize) (pos0 blen k0 : Std.Usize)
    (hblen : pos0.val + blen.val ≤ input.length) (hb : blen.val ≤ 32768) :
    slot.parse_loop0_loop4 input mdist choice ll_freq d_freq pos0 blen k0 ⦃ fun _ => True ⦄ := by
  rw [slot.parse_loop0_loop4]
  apply Std.loop.spec_decr_nat (measure := fun s => blen.val - s.2.2.val) (inv := fun _ => True)
  · rintro ⟨llf, df, k⟩ _
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0_loop4.body, lift]
    step*
    all_goals first
      | scalar_tac
      | (rcases lc with ⟨lci, lce⟩
         rcases dc with ⟨dci, dce⟩
         simp only at lc_post1 lc_post2 dc_post1 dc_post2
         step*
         all_goals scalar_tac)
  · trivial

@[local step]
theorem parse_loop0_loop5_spec (input : Slice Std.U8) (mlen mdist : Array Std.U32 32768#usize)
    (cost0 choice0 : Array Std.U32 32769#usize) (ll_cost : Array Std.U32 286#usize)
    (d_cost : Array Std.U32 30#usize) (pos0 blen j0 : Std.Usize)
    (hblen : pos0.val + blen.val ≤ input.length) (hb : blen.val ≤ 32768) (hj : j0.val ≤ blen.val) :
    slot.parse_loop0_loop5 input mlen mdist cost0 choice0 ll_cost d_cost pos0 blen j0
      ⦃ fun _ => True ⦄ := by
  rw [slot.parse_loop0_loop5]
  apply Std.loop.spec_decr_nat
    (measure := fun s => s.2.2.val)
    (inv := fun s => s.2.2.val ≤ blen.val)
  · rintro ⟨cost, choice, j⟩ hj
    simp only at hj
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0_loop5.body, lift]
    split
    case isTrue hpos =>
      step*
      all_goals first | scalar_tac | simp
    case isFalse => trivial
  · exact hj

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

theorem parse_loop0_loop6_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (mdist : Array Std.U32 32768#usize) (choice : Array Std.U32 32769#usize)
    (ntok0 pos0 blen k0 : Std.Usize)
    (hblen : pos0.val + blen.val ≤ input.length) (hb : blen.val ≤ 32768)
    (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ blen.val) (hntok : ntok0.val ≤ pos0.val + k0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take (pos0.val + k0.val))) :
    slot.parse_loop0_loop6 input out0 mdist choice ntok0 pos0 blen k0 ⦃ fun r =>
      r.2.val ≤ pos0.val + blen.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.val) = some ((bytes input).take (pos0.val + blen.val)) ⦄ := by
  rw [slot.parse_loop0_loop6]
  apply Std.loop.spec_decr_nat
    (measure := fun s => blen.val - s.2.2.val)
    (inv := fun s =>
      s.2.2.val ≤ blen.val ∧ s.2.1.val ≤ pos0.val + s.2.2.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.1.val) = some ((bytes input).take (pos0.val + s.2.2.val)))
  · rintro ⟨out, ntok, k⟩ ⟨hkb, hnt, hlen, hde⟩
    simp only at hkb hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0_loop6.body]
    split
    case isTrue hklt =>
      have hntok_lt : ntok.val < out.length := by scalar_tac
      step*
      apply Std.WP.spec_bind (verified_spec input pos d ch k blen (by scalar_tac) (by scalar_tac) hb)
      intro b hb
      split
      case isTrue hbt =>
        obtain ⟨hch3, hch258, hd1, hdmax, hdpos, hend, hmatch⟩ := hb hbt
        step*
        have htok : i8.val = LZ77.mkMatch d.val ch.val := by
          simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i8_post, i5_post, i4_post, i7_post,
            i3_post, i6_post1, i2_post1, Std.UScalar.cast_val_eq]
          scalar_tac
        refine ⟨by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          toks_update out ntok i8 hntok_lt, htok,
          show pos0.val + k1.val = pos.val + ch.val by scalar_tac]
        refine LZ77.valid_match (bytes input) (toks out ntok.val) pos.val d.val ch.val
          (by rw [show pos.val = pos0.val + k.val by scalar_tac]; exact hde)
          hd1 hdpos (by simpa [LZ77.MAX_DIST] using hdmax) hch3
          (by simpa [LZ77.MAX_LEN] using hch258) (by rw [bytes_length]; scalar_tac) ?_
        intro j hj
        exact (bytes_congr input _ _ (by scalar_tac) (by scalar_tac) (hmatch j hj)).symm
      case isFalse hbf =>
        have hposlen : pos.val < input.length := by scalar_tac
        step*
        have hval : i3.val = (bytes input)[pos.val]! := by
          rw [bytes_getElem! input pos.val hposlen, i3_post, Std.U8.cast_U32_val_eq, i2_post]
        refine ⟨by scalar_tac, by scalar_tac,
          by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen, ?_, by scalar_tac⟩
        rw [s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
          toks_update out ntok i3 hntok_lt, hval,
          show pos0.val + k1.val = pos.val + 1 by scalar_tac]
        exact LZ77.valid_lit (bytes input) (toks out ntok.val) pos.val
          (by rw [show pos.val = pos0.val + k.val by scalar_tac]; exact hde)
          (by rw [bytes_length]; scalar_tac) (by rw [← hval]; scalar_tac)
    case isFalse hge =>
      have hkb' : k.val = blen.val := by scalar_tac
      refine ⟨by scalar_tac, hlen, ?_⟩
      rw [hde, hkb']
  · exact ⟨hk, hntok, rfl, hdec⟩

/-! ## The block loop: tokens so far decode to the input before this block -/

theorem parse_loop0_spec (input : Slice Std.U8) (out0 : Slice Std.U32) (n lim : Std.Usize)
    (head0 prev0 mlen0 mdist0 : Array Std.U32 32768#usize)
    (cost0 choice0 : Array Std.U32 32769#usize)
    (llf0 : Array Std.U32 287#usize) (df0 : Array Std.U32 31#usize)
    (llc0 : Array Std.U32 286#usize) (dc0 : Array Std.U32 30#usize)
    (ntok0 pos00 : Std.Usize) (has30 : Bool)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hlim : has30 = true → lim.val + 3 ≤ input.length)
    (hpos : pos00.val ≤ n.val) (hntok : ntok0.val ≤ pos00.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos00.val)) :
    slot.parse_loop0 input out0 n head0 prev0 mlen0 mdist0 cost0 choice0 llf0 df0 llc0 dc0
        ntok0 pos00 has30 lim
      ⦃ fun r => r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
        LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  rw [slot.parse_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.2.2.2.2.2.2.2.2.val)
    (inv := fun s =>
      s.2.2.2.2.2.2.2.2.2.2.2.2.val ≤ n.val ∧
      s.2.2.2.2.2.2.2.2.2.2.2.1.val ≤ s.2.2.2.2.2.2.2.2.2.2.2.2.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.2.2.2.2.2.2.2.1.val) =
        some ((bytes input).take s.2.2.2.2.2.2.2.2.2.2.2.2.val))
  · rintro ⟨out, hd, pv, ml, md, cs, ch, llf, df, llc, dc, ntok, pos0⟩ ⟨hp, hnt, hlen, hde⟩
    simp only at hp hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    have hlim3 : has30 = true → lim.val + 3 ≤ input.length := hlim
    simp only [slot.parse_loop0.body]
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
      apply Std.WP.spec_bind (parse_loop0_loop0_spec input hd pv ml md pos0 lim blen 0#usize has30
        (fun h => hlim3 h) (by scalar_tac) hb1)
      rintro ⟨hd1, pv1, ml1, md1⟩ _
      step*
      apply Std.WP.spec_bind (parse_loop0_loop1_spec ml1 md1 _ _ blen blen hb1 (le_refl _))
      rintro ⟨cs1, ch1⟩ _
      simp only [lift, Std.Array.to_slice_mut]
      step*
      all_goals first | scalar_tac | simp | skip
      apply Std.WP.spec_bind (parse_loop0_loop6_spec input out md1 _ ntok pos0 blen 0#usize
        (by scalar_tac) hb1 (by scalar_tac) (by scalar_tac) (by scalar_tac) (by simpa using hde))
      rintro ⟨out1, ntok1⟩ ⟨hnt1, hlen1, hde1⟩
      simp only at hnt1 hlen1 hde1
      step*
      refine ⟨by scalar_tac, by scalar_tac, hlen1.trans hlen, ?_, by scalar_tac⟩
      rw [hde1, show pos01.val = pos0.val + blen.val by scalar_tac]
    case isFalse hge =>
      have hpn : pos0.val = n.val := by scalar_tac
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
      (Std.Array.repeat 32768#usize 0#u32) (Std.Array.repeat 32768#usize 0#u32)
      (Std.Array.repeat 32769#usize 0#u32) (Std.Array.repeat 32769#usize 0#u32)
      (Std.Array.repeat 287#usize 0#u32) (Std.Array.repeat 31#usize 0#u32)
      (Std.Array.repeat 286#usize 0#u32) (Std.Array.repeat 30#usize 0#u32)
      0#usize 0#usize has3
      (by simp) hlen hlim (by scalar_tac) (by scalar_tac)
      (by simp [toks, LZ77.decode])

end Submission
