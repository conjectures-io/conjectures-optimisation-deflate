import Lz77
import Slot
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

## Why `Lz77` and `Slot` are imported here

**This file must not inherit the meaning of `slot.parse` from the file it is
checking.** `import Proof.Parse` alone is not enough, and the gap was real: a
submission that *omitted* `import Slot` from its own `Parse.lean` left the name
`slot.parse` free, could define it there as anything it liked — including a
verbatim copy of some other submission's extracted model — and prove the
obligation about that. The generated model of the submitted `parse.rs` was then
never mentioned by anything, while stage 6 went on to score it. The proof and the
scored program were different programs.

Importing `Lz77` and `Slot` here closes it structurally: the gate names its own
dependencies, so `slot.parse` and `LZ77.Obligation` are the operator's
definitions no matter what the submission does or does not import. A submission
that also declares `slot.parse` now collides at import rather than shadowing —
Lean refuses an environment in which one name has two declarations.

Stage 1 additionally rejects a submitted proof that declares anything in the
`slot` or `LZ77` namespaces, so the failure arrives with a readable message
instead of as an import error. That check is the usability half; this import is
the control.
-/

theorem accepted : LZ77.Obligation slot.parse :=
  fun input out h => Submission.parse_spec input out h

#print axioms accepted
