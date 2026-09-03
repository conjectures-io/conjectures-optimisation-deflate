import Proof.Parse

/-!
# What the submission actually rests on

Aeneas's own Lean library contains `sorry` (`Std/Slice.lean`, `Std/StringIter.lean`),
so "it builds" is not the check — a proof that reached a sorried lemma would build
too. This is the check. Anything beyond Lean's own `propext`, `Classical.choice`
and `Quot.sound` — `sorryAx` above all — is a rejection.

The verifier greps this output; it does not read it.
-/

#print axioms Submission.parse_spec
#print axioms Submission.match_len_spec
#print axioms Submission.parse_loop0_spec
#print axioms LZ77.valid_match
#print axioms LZ77.valid_lit
