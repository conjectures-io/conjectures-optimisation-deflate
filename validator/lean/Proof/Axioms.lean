import Proof.Parse

/-!
# What the submission actually rests on

Aeneas's own Lean library contains `sorry` (`Std/Slice.lean`, `Std/StringIter.lean`),
so "it builds" is not the check — a proof that reached a sorried lemma would build
too. Anything beyond Lean's own `propext`, `Classical.choice` and `Quot.sound` —
`sorryAx` above all — is a rejection.

This file is for a miner's own `lake build` and `just prove`, so it names only the
one theorem every submission must have. The verifier does not read it: it runs
`#print axioms accepted` on the gate in a separate `lean` process.
-/

#print axioms Submission.parse_spec
