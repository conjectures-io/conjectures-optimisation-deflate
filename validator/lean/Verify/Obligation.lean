import Proof.Parse

/-!
# The gate

**Written by the verifier, regenerated on every submission, never supplied by a
miner.** It is three lines and it is the whole statement check.

`LZ77.Obligation` is the operator's statement, in `Lz77/Interface.lean`, pinned by
hash. `slot.parse` is what `charon` and `aeneas` produced from the submitted
`parse.rs`, which the verifier extracted itself. `Submission.parse_spec` is
whatever the miner proved.

If the miner weakened their statement — quantified over fewer inputs, dropped the
length condition, replaced `Valid` with something weaker, proved a lemma about a
different function — the application below does not typecheck. There is nothing to
read carefully and nothing to compare as text.
-/

theorem accepted : LZ77.Obligation slot.parse :=
  fun input out h => Submission.parse_spec input out h

#print axioms accepted
