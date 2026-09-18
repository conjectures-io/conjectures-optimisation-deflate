import Lz77
import Slot

/-!
Lazy matching over hash chains, `miniz_oxide` level 9's own dials: a split
probe budget, a `far_and_small` filter on freshly found matches, and an
immediate-accept shortcut once a match reaches `IMMEDIATE_ACCEPT`. The search
side (`find_match`) is the `lazy` proof's, generalized to a variable probe
budget. The emission side adds two new leaves beyond `lazy`'s three: taking a
match immediately (no pending) and taking a lookahead match immediately after
flushing the previously-pending byte as a literal (two tokens in one step).
-/

namespace Submission
open Aeneas Aeneas.Std Result ControlFlow

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open LZ77 (toks bytes bytes_length bytes_getElem! toks_update bytes_congr)

/-! ## The hash: in range, and nothing else -/

@[local step]
theorem hash3_spec (a b c : Std.U8) :
    slot.hash3 a b c ⦃ fun h => h.val < 32768 ⦄ := by
  rw [slot.hash3]
  step*

/-! ## Two arithmetic helpers: only need to terminate, values are irrelevant -/

@[local step]
theorem probe_budget_spec (hint : Std.Usize) :
    slot.probe_budget hint ⦃ fun _ => True ⦄ := by
  rw [slot.probe_budget]
  split <;> simp

@[local step]
theorem far_and_small_spec (len dist : Std.Usize) :
    slot.far_and_small len dist ⦃ fun _ => True ⦄ := by
  rw [slot.far_and_small]
  split <;> simp

/-! ## The match-length loop: the one load-bearing function -/

/-- `Matches input a b n`: the `n` bytes at `a` and at `b` agree. -/
def Matches (input : Slice Std.U8) (a b n : Nat) : Prop :=
  ∀ k, k < n → input.val[b + k]! = input.val[a + k]!

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

/-! ## The three hash-insert loops (one per emission site): terminate, prove nothing else -/

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

@[local step]
theorem parse_loop0_loop1_spec (input : Slice Std.U8)
    (head0 prev0 : Array Std.U32 32768#usize)
    (has30 : Bool) (lim «end» k0 : Std.Usize)
    (hlim : has30 = true → lim.val + 3 ≤ input.length) :
    slot.parse_loop0_loop1 input head0 prev0 has30 lim «end» k0
      ⦃ fun r => r.2.2 = true → lim.val + 3 ≤ input.length ⦄ := by
  rw [slot.parse_loop0_loop1]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «end».val - s.2.2.2.val)
    (inv := fun s => s.2.2.1 = true → lim.val + 3 ≤ input.length)
  · rintro ⟨hd, pv, h3, k⟩ hinv
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0_loop1.body]
    step*
  · exact hlim

@[local step]
theorem parse_loop0_loop2_spec (input : Slice Std.U8)
    (head0 prev0 : Array Std.U32 32768#usize)
    (has30 : Bool) (lim «end» k0 : Std.Usize)
    (hlim : has30 = true → lim.val + 3 ≤ input.length) :
    slot.parse_loop0_loop2 input head0 prev0 has30 lim «end» k0
      ⦃ fun r => r.2.2 = true → lim.val + 3 ≤ input.length ⦄ := by
  rw [slot.parse_loop0_loop2]
  apply Std.loop.spec_decr_nat
    (measure := fun s => «end».val - s.2.2.2.val)
    (inv := fun s => s.2.2.1 = true → lim.val + 3 ≤ input.length)
  · rintro ⟨hd, pv, h3, k⟩ hinv
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    simp only [slot.parse_loop0_loop2.body]
    step*
  · exact hlim

/-- Either nothing was found, or the `(distance, length)` is in range and its
    bytes were compared. Everything a search has to establish, and nothing else. -/
def Found (input : Slice Std.U8) (n pos best_len best_dist : Std.Usize) : Prop :=
  best_len.val < 3 ∨
    (3 ≤ best_len.val ∧ best_len.val ≤ 258 ∧ pos.val + best_len.val ≤ n.val ∧
      1 ≤ best_dist.val ∧ best_dist.val ≤ 32768 ∧ best_dist.val ≤ pos.val ∧
      Matches input (pos.val - best_dist.val) pos.val best_len.val)

/-! ## The search: `Found` is the postcondition and the invariant; `cur` is never mentioned.
    Unlike `lazy`, the probe budget is a parameter, not a fixed constant, and there is no
    "nice length" early cutoff, so the loop body is a straight line once the chain step
    is reached -- simpler than `lazy`'s, not harder. -/

theorem find_match_loop_spec (input : Slice Std.U8) (prev : Slice Std.U32)
    (n pos cap probe_cap bl0 bd0 cur0 probes0 : Std.Usize)
    (hn : n.val = input.length) (hprev : prev.length = 32768)
    (hcap : pos.val + cap.val ≤ n.val) (hcap258 : cap.val ≤ 258)
    (h0 : Found input n pos bl0 bd0) :
    slot.find_match_loop input prev pos cap probe_cap bl0 bd0 cur0 probes0
      ⦃ fun r => Found input n pos r.1 r.2 ⦄ := by
  rw [slot.find_match_loop]
  apply Std.loop.spec_decr_nat
    (measure := fun s => probe_cap.val - s.2.2.2.val)
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
          step*
          rcases Nat.lt_or_ge l.val 3 with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h, by scalar_tac, by scalar_tac, by scalar_tac,
              by scalar_tac, by scalar_tac,
              by rw [show pos.val - i.val = cpos.val by scalar_tac]; exact l_post2⟩
        case isFalse =>
          step*
      case isFalse => exact hinv
    · rintro ⟨bl1, bd1, cur1⟩ hf
      step*
  · exact h0

@[local step]
theorem find_match_spec (input : Slice Std.U8) (prev : Slice Std.U32)
    (n pos cap start probe_cap : Std.Usize)
    (hn : n.val = input.length) (hprev : prev.length = 32768)
    (hcap : pos.val + cap.val ≤ n.val) (hcap258 : cap.val ≤ 258) :
    slot.find_match input prev pos cap start probe_cap
      ⦃ fun r => Found input n pos r.1 r.2 ⦄ :=
  find_match_loop_spec input prev n pos cap probe_cap 0#usize 0#usize start 0#usize
    hn hprev hcap hcap258 (Or.inl (by scalar_tac))

/-! ## The lazy state -/

/-- Nothing pending, or `(len, dist)` is `Found` at `pos - 1`. -/
def Pending (input : Slice Std.U8) (n pos len dist : Std.Usize) : Prop :=
  len.val < 3 ∨
    (1 ≤ pos.val ∧ 3 ≤ len.val ∧ len.val ≤ 258 ∧ (pos.val - 1) + len.val ≤ n.val ∧
      1 ≤ dist.val ∧ dist.val ≤ 32768 ∧ dist.val ≤ pos.val - 1 ∧
      Matches input (pos.val - 1 - dist.val) (pos.val - 1) len.val)

/-- The input prefix the tokens written so far decode to. -/
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

/-! ## The parse loop: tokens so far decode to `emitted`, and a pending match is `Pending` -/

theorem parse_loop0_spec (input : Slice Std.U8) (out0 : Slice Std.U32)
    (n lim : Std.Usize) (head0 prev0 : Array Std.U32 32768#usize)
    (ntok0 pos0 pl0 pd0 : Std.Usize) (has30 : Bool)
    (hn : n.val = input.length)
    (hout : input.length ≤ out0.length)
    (hlim : has30 = true → lim.val + 3 ≤ input.length)
    (hpos : pos0.val ≤ n.val) (hntok : ntok0.val ≤ emitted pos0.val pl0.val)
    (hpend : Pending input n pos0 pl0 pd0)
    (hdec : LZ77.decode (toks out0 ntok0.val) =
      some ((bytes input).take (emitted pos0.val pl0.val))) :
    slot.parse_loop0 input out0 n head0 prev0 ntok0 pos0 has30 lim pl0 pd0 ⦃ fun r =>
      r.2.2.1.val < 3 ∧ r.2.1.val ≤ input.length ∧ r.1.length = out0.length ∧
      LZ77.decode (toks r.1 r.2.1.val) = some (bytes input) ⦄ := by
  rw [slot.parse_loop0]
  apply Std.loop.spec_decr_nat
    (measure := fun s => n.val - s.2.2.2.2.1.val)
    (inv := fun s =>
      s.2.2.2.2.1.val ≤ n.val ∧
      s.2.2.2.1.val ≤ emitted s.2.2.2.2.1.val s.2.2.2.2.2.2.1.val ∧
      s.1.length = out0.length ∧
      (s.2.2.2.2.2.1 = true → lim.val + 3 ≤ input.length) ∧
      Pending input n s.2.2.2.2.1 s.2.2.2.2.2.2.1 s.2.2.2.2.2.2.2 ∧
      LZ77.decode (toks s.1 s.2.2.2.1.val) =
        some ((bytes input).take (emitted s.2.2.2.2.1.val s.2.2.2.2.2.2.1.val)))
  · rintro ⟨out, hd, pv, ntok, pos, h3, pl, pd⟩ ⟨hp, hnt, hlen, hh3, hpd, hde⟩
    simp only at hp hnt hlen hh3 hpd hde
    have hmax : input.length ≤ Std.Usize.max := Std.Slice.length_ineq input
    have hmaxout : out.length ≤ Std.Usize.max := Std.Slice.length_ineq out
    -- `scalar_tac` cannot see through the irreducible constant; every immediate-accept branch needs its value.
    have hIA : slot.IMMEDIATE_ACCEPT.val = 128 := by unfold slot.IMMEDIATE_ACCEPT; simp
    simp only [slot.parse_loop0.body]
    split
    case isTrue hposlt =>
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
            rw [show ((if cap > 258#usize then ok 258#usize else ok cap)
                  : Result Std.Usize)
                = ok (if cap > 258#usize then 258#usize else cap) from by
                  split <;> rfl]
            step*
            case hcap => split <;> scalar_tac
            case hcap258 => split <;> scalar_tac
            split
            case isTrue hlt3 => exact Or.inl (by scalar_tac)
            case isFalse hge3 =>
              step*
              split
              case isTrue hfar => exact Or.inl (by scalar_tac)
              case isFalse hnfar => exact cur_len1_post
          case isFalse => exact Or.inl (by scalar_tac)
        case isFalse => exact Or.inl (by scalar_tac)
      · rintro ⟨head1, prev1, cur_len, cur_dist⟩ hfound
        replace hfound : Found input n pos cur_len cur_dist := hfound
        have hlim3 : h3 = true → lim.val + 3 ≤ input.length := hh3
        have hntok_lt : ntok.val < out.length := by
          have : emitted pos.val pl.val ≤ pos.val := by unfold emitted; split <;> omega
          scalar_tac
        step*
        -- `step*` leaves behind a handful of side goals it can't close on its
        -- own: array-bound (`hbound`) and arithmetic-overflow (`hmax`) checks
        -- for the *second* write in case A specifically, whose margin needs
        -- `pl ≥ 3` (⟹ `ntok ≤ pos - 1`, one more byte than `hntok_lt` gives
        -- generically) or a fact hidden inside `Found`/`Pending`. Try every
        -- combination rather than name the exact tag, since which check is
        -- outstanding (if any) depends on which of the six branches produced
        -- the goal.
        all_goals first
          | scalar_tac
          | (rcases hfound with h | ⟨_, _, _, _, _, _, _⟩ <;> scalar_tac)
          | (rcases hpd with h | ⟨_, _, _, _, _, _, _, _⟩ <;> scalar_tac)
          | (rcases hfound with h | ⟨_, _, _, _, _, _, _⟩ <;>
             rcases hpd with h2 | ⟨_, _, _, _, _, _, _, _⟩ <;> scalar_tac)
          | (rw [emitted_ge (by scalar_tac : (3 : Nat) ≤ pl.val)] at hnt; scalar_tac)
          | (rcases hfound with h | ⟨_, _, _, _, _, _, _⟩ <;>
             rw [emitted_ge (by scalar_tac : (3 : Nat) ≤ pl.val)] at hnt <;> scalar_tac)
          | (rw [__post2]
             have hlen_eq : (out.set ntok i2).length = out.length := by
               simp [Std.Slice.set_val_eq]
             rw [hlen_eq, ntok1_post]
             rw [emitted_ge (by scalar_tac : (3 : Nat) ≤ pl.val)] at hnt
             scalar_tac)
          | skip
        all_goals first
        | ( -- B: beaten pending, defer
            rcases hpd with h | ⟨hpos1, hl3, hlmax, hend, hd1, hdmax, hdpos, hmatch⟩
            · exfalso; scalar_tac
            rw [emitted_ge hl3] at hnt hde
            have hcur3 : 3 ≤ cur_len.val := by scalar_tac
            have hposlen : pos.val - 1 < input.length := by scalar_tac
            have hi : i.val = pos.val - 1 := by scalar_tac
            have hval : i2.val = (bytes input)[pos.val - 1]! := by
              rw [bytes_getElem! input (pos.val - 1) hposlen, i2_post, Std.U8.cast_U32_val_eq, i1_post]
              simp only [hi]
            refine ⟨by scalar_tac, ?_, by rw [__post2]; simpa [Std.Slice.set_val_eq] using hlen,
              hlim3, pending_of_found input n pos _ cur_len cur_dist (by scalar_tac) hfound,
              ?_, by scalar_tac⟩
            · rw [emitted_ge hcur3]; scalar_tac
            · rw [emitted_ge hcur3, __post2, show ntok1.val = ntok.val + 1 by scalar_tac,
                toks_update out ntok i2 hntok_lt, hval,
                show pos1.val - 1 = (pos.val - 1) + 1 by scalar_tac]
              exact LZ77.valid_lit (bytes input) (toks out ntok.val) (pos.val - 1) hde
                (by rw [bytes_length]; scalar_tac) (by rw [← hval]; scalar_tac) )
        | ( -- D: no pending, immediate accept
            have hpl3 : pl.val < 3 := by scalar_tac
            rw [emitted_lt hpl3] at hnt hde
            rcases hfound with hfl | ⟨hfl3, hflmax, hfend, hfd1, hfdmax, hfdpos, hfmatch⟩
            · exfalso; scalar_tac
            have htok : i6.val = LZ77.mkMatch cur_dist.val cur_len.val := by
              simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i6_post, i3_post, i2_post,
                i5_post, i1_post, i4_post1, i_post1, Std.UScalar.cast_val_eq]
              scalar_tac
            refine ⟨by scalar_tac, ?_, by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen,
              head2_post, Or.inl hpl3, ?_, by scalar_tac⟩
            · rw [emitted_lt hpl3]; scalar_tac
            · rw [emitted_lt hpl3, s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
                toks_update out ntok i6 hntok_lt, htok, show «end».val = pos.val + cur_len.val by scalar_tac]
              refine LZ77.valid_match (bytes input) (toks out ntok.val) pos.val
                cur_dist.val cur_len.val hde hfd1 hfdpos
                (by simpa [LZ77.MAX_DIST] using hfdmax) hfl3
                (by simpa [LZ77.MAX_LEN] using hflmax) (by rw [bytes_length]; scalar_tac) ?_
              intro k hk
              exact (bytes_congr input _ _ (by scalar_tac) (by scalar_tac) (hfmatch k hk)).symm )
        | ( -- E: no pending, defer
            rcases hpd with h | ⟨hpos1, hl3, _⟩
            · rw [emitted_lt h] at hnt hde
              have hcur3 : 3 ≤ cur_len.val := by scalar_tac
              refine ⟨by scalar_tac, ?_, hlen, hlim3,
                pending_of_found input n pos _ cur_len cur_dist (by scalar_tac) hfound,
                ?_, by scalar_tac⟩
              · rw [emitted_ge hcur3]; scalar_tac
              · rw [emitted_ge hcur3]; convert hde using 3; scalar_tac
            · exfalso; scalar_tac )
        | ( -- F: plain literal
            rcases hpd with h | ⟨hpos1, hl3, _⟩
            · rw [emitted_lt h] at hnt hde
              have hposlen : pos.val < input.length := by scalar_tac
              have hval : i1.val = (bytes input)[pos.val]! := by
                rw [bytes_getElem! input pos.val hposlen, i1_post,
                  Std.U8.cast_U32_val_eq, i_post]
              refine ⟨by scalar_tac, ?_, by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen,
                hlim3, Or.inl h, ?_, by scalar_tac⟩
              · rw [emitted_lt h]; scalar_tac
              · rw [emitted_lt h, s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
                  toks_update out ntok i1 hntok_lt, hval,
                  show pos1.val = pos.val + 1 by scalar_tac]
                exact LZ77.valid_lit (bytes input) (toks out ntok.val) pos.val hde
                  (by rw [bytes_length]; scalar_tac) (by rw [← hval]; scalar_tac)
            · exfalso; scalar_tac )
        | ( -- A: beaten pending, immediate accept -- literal at pos-1, then the match at pos
            rcases hpd with h | ⟨hpos1, hl3, hlmax, hend, hd1, hdmax, hdpos, hmatch⟩
            · exfalso; scalar_tac
            rw [emitted_ge hl3] at hnt hde
            have hcur3 : 3 ≤ cur_len.val := by scalar_tac
            have hposlen : pos.val - 1 < input.length := by scalar_tac
            have hi : i.val = pos.val - 1 := by scalar_tac
            have hval : i2.val = (bytes input)[pos.val - 1]! := by
              rw [bytes_getElem! input (pos.val - 1) hposlen, i2_post, Std.U8.cast_U32_val_eq, i1_post]
              simp only [hi]
            have hstep1 : LZ77.decode (toks (out.set ntok i2) ntok1.val) =
                some ((bytes input).take pos.val) := by
              rw [show ntok1.val = ntok.val + 1 by scalar_tac, toks_update out ntok i2 hntok_lt, hval,
                show pos.val = (pos.val - 1) + 1 by scalar_tac]
              exact LZ77.valid_lit (bytes input) (toks out ntok.val) (pos.val - 1) hde
                (by rw [bytes_length]; scalar_tac) (by rw [← hval]; scalar_tac)
            rcases hfound with hfl | ⟨hfl3, hflmax, hfend, hfd1, hfdmax, hfdpos, hfmatch⟩
            · exfalso; scalar_tac
            have htok : i9.val = LZ77.mkMatch cur_dist.val cur_len.val := by
              simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i9_post, i6_post, i5_post, i4_post,
                i3_post1, i8_post, i7_post1, Std.UScalar.cast_val_eq]
              scalar_tac
            have hlen_set : (out.set ntok i2).length = out.length := by
              simp [Std.Slice.set_val_eq]
            have hntok1_lt : ntok1.val < (out.set ntok i2).length := by
              rw [hlen_set]; scalar_tac
            refine ⟨by scalar_tac, ?_, by rw [s_post, __post2]; simpa [Std.Slice.set_val_eq] using hlen,
              head2_post, Or.inl (by scalar_tac), ?_, by scalar_tac⟩
            · rw [emitted_lt (by scalar_tac)]; scalar_tac
            · rw [emitted_lt (by scalar_tac), s_post, __post2,
                show ntok2.val = ntok1.val + 1 by scalar_tac,
                toks_update (out.set ntok i2) ntok1 i9 hntok1_lt, htok,
                show «end».val = pos.val + cur_len.val by scalar_tac]
              refine LZ77.valid_match (bytes input) (toks (out.set ntok i2) ntok1.val) pos.val
                cur_dist.val cur_len.val hstep1 hfd1 hfdpos
                (by simpa [LZ77.MAX_DIST] using hfdmax) hfl3
                (by simpa [LZ77.MAX_LEN] using hflmax) (by rw [bytes_length]; scalar_tac) ?_
              intro k hk
              exact (bytes_congr input _ _ (by scalar_tac) (by scalar_tac) (hfmatch k hk)).symm )
        | ( -- C: pending wins
            rcases hpd with h | ⟨hpos1, hl3, hlmax, hend, hd1, hdmax, hdpos, hmatch⟩
            · exfalso; scalar_tac
            rw [emitted_ge hl3] at hnt hde
            have htok : i6.val = LZ77.mkMatch pd.val pl.val := by
              simp only [LZ77.mkMatch, LZ77.MATCH_BASE, i6_post, i3_post, i2_post,
                i5_post, i1_post, i4_post1, i_post1, Std.UScalar.cast_val_eq]
              scalar_tac
            refine ⟨by scalar_tac, ?_, by rw [s_post]; simpa [Std.Slice.set_val_eq] using hlen,
              head2_post, Or.inl (by scalar_tac), ?_, by scalar_tac⟩
            · rw [emitted_lt (by scalar_tac)]; scalar_tac
            · rw [emitted_lt (by scalar_tac), s_post, show ntok1.val = ntok.val + 1 by scalar_tac,
                toks_update out ntok i6 hntok_lt, htok,
                show «end».val = (pos.val - 1) + pl.val by scalar_tac]
              refine LZ77.valid_match (bytes input) (toks out ntok.val) (pos.val - 1)
                pd.val pl.val hde hd1 hdpos
                (by simpa [LZ77.MAX_DIST] using hdmax) hl3
                (by simpa [LZ77.MAX_LEN] using hlmax) (by rw [bytes_length]; scalar_tac) ?_
              intro k hk
              exact (bytes_congr input _ _ (by scalar_tac) (by scalar_tac) (hmatch k hk)).symm )
    case isFalse hge =>
      have hpn : pos.val = n.val := by scalar_tac
      have hpl : pl.val < 3 := by
        rcases hpd with h | ⟨_, hl3, _, hend, _⟩
        · exact h
        · exfalso; omega
      rw [emitted_lt hpl] at hnt hde
      refine ⟨hpl, by scalar_tac, hlen, ?_⟩
      rw [hde, hpn, hn]
      simp
  · exact ⟨hpos, hntok, rfl, hlim, hpend, hdec⟩

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
    apply Std.WP.spec_bind (parse_loop0_spec input out (Std.Slice.len input) lim
      (Std.Array.repeat 32768#usize 0#u32) (Std.Array.repeat 32768#usize 0#u32)
      0#usize 0#usize 0#usize 0#usize has3
      (by simp) hlen hlim (by scalar_tac) (by simp [emitted]) (Or.inl (by scalar_tac))
      (by simp [toks, LZ77.decode, emitted]))
    rintro ⟨out1, ntok, pl, pd⟩ ⟨hpl, hntok, hlen1, hdec⟩
    step*
    exact ⟨hntok, hlen1, hdec⟩

end Submission
