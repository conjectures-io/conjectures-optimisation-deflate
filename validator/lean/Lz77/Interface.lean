import Lz77.Lemmas

/-!
# The obligation, as the operator states it

`Spec.lean` says what a token stream *means*; this file says what a **submission
must prove**, in a form that does not mention any particular submission.

That indirection is the point. A miner writes `Submission.parse_spec` however they
like, and the verifier — not the miner — writes

```lean
theorem accepted : LZ77.Obligation slot.parse := fun i o h => Submission.parse_spec i o h
```

into a file the submission never sees. If the miner weakened their statement, that
line does not typecheck, and no amount of care in reading Lean is needed to notice.
This is v1's "statement check" done as a type check rather than as a string
comparison, which is the only version of it that cannot be gamed.

`toks` and `bytes` live here rather than in the submission for the same reason:
they are how the contract reads the extracted machine state, so they belong to the
side that owns the contract.
-/

namespace LZ77

open Aeneas Aeneas.Std

/-- The token stream written so far, as the contract's `List Nat`. -/
def toks (out : Slice Std.U32) (n : Nat) : List Nat := (out.val.take n).map (·.val)

/-- The input, as the contract's `List Nat`. -/
def bytes (input : Slice Std.U8) : List Nat := input.val.map (·.val)

/-- **The obligation.**

    For every input, and every output buffer at least as long as the input:
    `parse` returns a token count and a buffer, it never fails and always
    terminates (that is what living in `Result` and being proved `⦃ _ ⦄` means),
    it does not change the buffer's length, and **the tokens it wrote decode back
    to the input**.

    Nothing here constrains how the parse was found. -/
def Obligation
    (parse : Slice Std.U8 → Slice Std.U32 → Result (Std.Usize × Slice Std.U32)) : Prop :=
  ∀ (input : Slice Std.U8) (out : Slice Std.U32), input.length ≤ out.length →
    parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      Valid (bytes input) (toks r.2 r.1.val) ⦄

@[simp] theorem bytes_length (input : Slice Std.U8) :
    (bytes input).length = input.length := by
  simp [bytes]

theorem bytes_getElem! (input : Slice Std.U8) (i : Nat) (h : i < input.length) :
    (bytes input)[i]! = (input.val[i]).val := by
  simp only [bytes, List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h]
  rfl

theorem take_set_succ {α : Type} (l : List α) (i : Nat) (v : α) (h : i < l.length) :
    (l.set i v).take (i + 1) = l.take i ++ [v] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using h)]
  congr 1
  · rw [List.take_set]
    exact List.set_eq_of_length_le (by rw [List.length_take]; omega)
  · simp

theorem toks_update (out : Slice Std.U32) (i : Std.Usize) (v : Std.U32)
    (h : i.val < out.length) :
    toks (out.set i v) (i.val + 1) = toks out i.val ++ [v.val] := by
  simp only [toks, Std.Slice.set_val_eq, take_set_succ _ _ _ h, List.map_append,
    List.map_cons, List.map_nil]

theorem bytes_congr (input : Slice Std.U8) (i j : Nat)
    (hi : i < input.length) (hj : j < input.length)
    (h : input.val[i]! = input.val[j]!) : (bytes input)[i]! = (bytes input)[j]! := by
  rw [bytes_getElem! input i hi, bytes_getElem! input j hj]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] at h
  rw [h]

end LZ77
