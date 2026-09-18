import Lz77
import Slot

/-!
The optimal-parse proof. The search side is the lazy proof with 24 probes. The
dynamic program (`match_bits`, `relax`, the forward and backward block loops) is
search too: postcondition `True`, only termination and bounds. The emission loop
re-verifies every chosen match with `match_len`, so its invariant is the template's.
-/

namespace Submission
open Aeneas Aeneas.Std Result ControlFlow

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr)

/-- `step*` will not enter `if c then ok x else ok y`; as `ok (if c then x else y)` it will. -/
theorem ite_ok {α : Type} (c : Prop) [Decidable c] (x y : α) :
    (if c then ok x else ok y : Result α) = ok (if c then x else y) := by
  split <;> rfl

/-! ## The hash: in range, and nothing else -/

@[local step]
theorem hash3_spec (a b c : Std.U8) :
    slot.hash3 a b c ⦃ fun h => h.val < 32768 ⦄ := by
  rw [slot.hash3]
  step*

/-! ## The match-length loop: the one load-bearing function -/

/-- `Matches input a b n`: the `n` bytes at `a` and at `b` agree. -/
def Matches (input : Slice Std.U8) (a b n : Nat) : Prop :=
  ∀ k, k < n → input.val[b + k]! = input.val[a + k]!

theorem Matches.mono {input : Slice Std.U8} {a b n m : Nat} (h : Matches input a b n)
    (hm : m ≤ n) : Matches input a b m :=
  fun k hk => h k (by omega)

theorem match_len_loop_spec (input : Slice Std.U8) (a b cap l0 : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length)
    (hl0 : l0.val ≤ cap.val) (h0 : Matches input a.val b.val l0.val) :
    slot.match_len_loop input a b cap l0 ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ := by
  rw [slot.match_len_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun l => cap.val - l.val)
    (inv := fun l => l.val ≤ cap.val ∧ Matches input a.val b.val l.val)
  · rintro l ⟨hle, hinv⟩
    simp only [slot.match_len_loop.body]
    split
    case isTrue hlt =>
      have hltn : l.val < cap.val := by scalar_tac
      have hbi : b.val + l.val < input.length := by omega
      have hai : a.val + l.val < input.length := by omega
      have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
      apply Std.WP.spec_bind (Std.Usize.add_spec (x := b) (y := l) (by scalar_tac))
      intro i hi
      apply Std.WP.spec_bind (Std.Slice.index_usize_spec input i (by scalar_tac))
      intro x1 hx1
      apply Std.WP.spec_bind (Std.Usize.add_spec (x := a) (y := l) (by scalar_tac))
      intro i2 hi2
      apply Std.WP.spec_bind (Std.Slice.index_usize_spec input i2 (by scalar_tac))
      intro x3 hx3
      split
      case isTrue heq =>
        apply Std.WP.spec_bind (Std.Usize.add_spec (x := l) (y := 1#usize) (by scalar_tac))
        intro l1 hl1
        simp only [Std.WP.spec_ok]
        refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
        intro k hk
        rcases Nat.lt_or_ge k l.val with h | h
        · exact hinv k h
        · have hkl : k = l.val := by scalar_tac
          rw [hkl, ← hi, ← hi2, getElem!_pos _ _ (by scalar_tac),
              getElem!_pos _ _ (by scalar_tac), ← hx1, ← hx3]
          exact heq
      case isFalse => exact ⟨hle, hinv⟩
    case isFalse => exact ⟨hle, hinv⟩
  · exact ⟨hl0, h0⟩

@[local step]
theorem match_len_spec (input : Slice Std.U8) (a b cap : Std.Usize)
    (ha : a.val + cap.val ≤ input.length) (hb : b.val + cap.val ≤ input.length) :
    slot.match_len input a b cap ⦃ fun l =>
      l.val ≤ cap.val ∧ Matches input a.val b.val l.val ⦄ :=
  match_len_loop_spec input a b cap 0#usize ha hb (by scalar_tac) (by
    intro k hk; simp at hk)

/-- Either nothing was found, or the `(distance, length)` is in range and its
    bytes were compared. -/
def Found (input : Slice Std.U8) (n pos best_len best_dist : Std.Usize) : Prop :=
  best_len.val < 3 ∨
    (3 ≤ best_len.val ∧ best_len.val ≤ 258 ∧ pos.val + best_len.val ≤ n.val ∧
      1 ≤ best_dist.val ∧ best_dist.val ≤ 32768 ∧ best_dist.val ≤ pos.val ∧
      Matches input (pos.val - best_dist.val) pos.val best_len.val)

/-! ## The search: `Found` is the postcondition and the invariant -/

theorem find_match_loop_spec (input : Slice Std.U8) (prev : Slice Std.U32)
    (n pos cap bl0 bd0 cur0 probes0 : Std.Usize)
    (hn : n.val = input.length) (hprev : prev.length = 32768)
    (hcap : pos.val + cap.val ≤ n.val) (hcap258 : cap.val ≤ 258)
    (h0 : Found input n pos bl0 bd0) :
    slot.find_match_loop input prev pos cap bl0 bd0 cur0 probes0
      ⦃ fun r => Found input n pos r.1 r.2 ⦄ := by
  have hMP : slot.MAX_PROBES = 24#usize := by unfold slot.MAX_PROBES; rfl
  rw [slot.find_match_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => 24 - s.2.2.2.val)
    (inv := fun s => Found input n pos s.1 s.2.1)
  · rintro ⟨bl, bd, cur, probes⟩ hinv
    simp only at hinv
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.find_match_loop.body, hMP]
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
    slot.match_bits len dist ⦃ fun r => r.val ≤ 30 ⦄ := by
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
  have hTS : slot.TRY_SHORT.val = 8 := by unfold slot.TRY_SHORT; simp
  simp only [lift, ite_ok]
  step*
  all_goals first
    | scalar_tac
    | (apply relax_loop_spec cost i dist _ _ _ _ hcost
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

theorem parse_loop0_loop2_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (mdist : Array Std.U32 32768#usize) (choice : Array Std.U32 32769#usize)
    (ntok0 pos0 blen k0 : Std.Usize)
    (hblen : pos0.val + blen.val ≤ input.length) (hb : blen.val ≤ 32768)
    (hout : input.length ≤ out0.length)
    (hk : k0.val ≤ blen.val) (hntok : ntok0.val ≤ pos0.val + k0.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take (pos0.val + k0.val))) :
    slot.parse_loop0_loop2 input out0 mdist choice ntok0 pos0 blen k0 ⦃ fun r =>
      r.2.val ≤ pos0.val + blen.val ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.val) = some ((bytes input).take (pos0.val + blen.val)) ⦄ := by
  rw [slot.parse_loop0_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun s => blen.val - s.2.2.val)
    (inv := fun s =>
      s.2.2.val ≤ blen.val ∧ s.2.1.val ≤ pos0.val + s.2.2.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.1.val) = some ((bytes input).take (pos0.val + s.2.2.val)))
  · rintro ⟨out, ntok, k⟩ ⟨hkb, hnt, hlen, hde⟩
    simp only at hkb hnt hlen hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0_loop2.body]
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
    (cost0 choice0 : Array Std.U32 32769#usize) (ntok0 pos00 : Std.Usize) (has30 : Bool)
    (hn : n.val = input.length) (hout : input.length ≤ out0.length)
    (hlim : has30 = true → lim.val + 3 ≤ input.length)
    (hpos : pos00.val ≤ n.val) (hntok : ntok0.val ≤ pos00.val)
    (hdec : LZ77.decode (toks out0 ntok0.val) = some ((bytes input).take pos00.val)) :
    slot.parse_loop0 input out0 n head0 prev0 mlen0 mdist0 cost0 choice0 ntok0 pos00 has30 lim
      ⦃ fun r => r.1.val ≤ input.length ∧ r.2.length = out0.length ∧
        LZ77.decode (toks r.2 r.1.val) = some (bytes input) ⦄ := by
  have hB : slot.BLOCK.val = 32768 := by unfold slot.BLOCK; simp
  rw [slot.parse_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.2.2.2.2.val)
    (inv := fun s =>
      s.2.2.2.2.2.2.2.2.val ≤ n.val ∧ s.2.2.2.2.2.2.2.1.val ≤ s.2.2.2.2.2.2.2.2.val ∧
      s.1.length = out0.length ∧
      LZ77.decode (toks s.1 s.2.2.2.2.2.2.2.1.val) =
        some ((bytes input).take s.2.2.2.2.2.2.2.2.val))
  · rintro ⟨out, hd, pv, ml, md, cs, ch, ntok, pos0⟩ ⟨hp, hnt, hlen, hde⟩
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
      apply Std.WP.spec_bind (parse_loop0_loop2_spec input out md1 ch1 ntok pos0 blen 0#usize
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
      0#usize 0#usize has3
      (by simp) hlen hlim (by scalar_tac) (by scalar_tac)
      (by simp [toks, LZ77.decode])

end Submission
