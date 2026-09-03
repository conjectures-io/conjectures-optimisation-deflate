# validator/

Everything needed to accept, reject and score a submission.

```bash
just init                               # install everything, build, self-test
just doctor                             # what is present, what is missing
just check <submission-dir>             # the gate, then the score
just check <submission-dir> --no-score  # the gate alone
just corpus --force                     # rebuild the scoring corpus
just repin                              # after an operator-side change
```

Exit codes: `0` accepted, `1` rejected, `2` the validator itself is
misconfigured — and the distinction matters, because rejecting a submission
because your Aeneas is missing is worse than crashing.

## The gate

Six stages. **The order is the design**: nothing is compiled for speed and nothing
is timed until the proof has been accepted, so a submission cannot buy validator
time with a program that has no proof.

| stage | what it does | what it stops |
|---|---|---|
| 0 intake | copies in exactly `parse.rs` and `Parse.lean` | a submission that smuggles anything else |
| 1 policy | scans the Rust against 11 patterns | code outside the translated subset |
| 2 pins | hashes 23 contract and harness files | editing the contract you are judged against |
| 3 extract | **re-runs charon+aeneas itself** | an extraction that is a claim by the claimant |
| 4 statement | `LZ77.Obligation slot.parse` typechecks | a weakened theorem |
| 5 axioms | `#print axioms accepted` | `sorryAx` — Aeneas's own library contains `sorry` |
| 6 score | round-trip, bytes, speed floor | everything else |

[`docs/THREAT_MODEL.md`](docs/THREAT_MODEL.md) goes through each one with the
attack it answers and the negative test that shows it works.

## What the operator owns

| | lines | |
|---|---|---|
| `lean/Lz77/Spec.lean` | 25 | what a token stream means |
| `lean/Lz77/Lemmas.lean` | 66 | `valid_lit`, `valid_match` — the per-patch interface |
| `lean/Lz77/Interface.lean` | 40 | `toks`, `bytes`, and `Obligation` itself |
| `lean/Verify/Obligation.lean` | 4 | the gate |
| `harness/src/deflate.rs` | 411 | tokens to DEFLATE bytes. Trusted, fixed |
| `harness/src/token.rs` | 47 | the token encoding |
| `harness/src/main.rs` | 167 | round-trip check, scoring, the speed floor |
| `verifier/verify.py` | 236 | the six stages |

`lean/Lz77/` is the investment that makes submissions affordable, and
[`docs/DESIGN.md`](docs/DESIGN.md) explains why it is shaped the way it is. It is
paid once.

## Running a round

1. **Fix the corpus.** The one committed here is the development reference and
   its hashes are in [`docs/CORPUS.md`](docs/CORPUS.md); `verifier/make-corpus.py`
   builds a fresh mix and refuses to overwrite it without `--force`. In a real
   round you commit to a hash first and reveal the contents after scoring, and
   publish *shape* statistics only. [`docs/SCORING.md`](docs/SCORING.md) has the
   governance and the reason it matters.
2. **Verify each submission** with `just check`. Rejections are cheap; the
   ordering guarantees a bad submission is rejected before it costs a build.
3. **Rank the accepted ones** by total compressed bytes. It is an exact integer,
   so two validators on different hardware produce the *same* ranking. There is no
   tie-break by measurement, and no possibility of two honest validators
   disagreeing.
4. **Promote the winner.** Copy its `parse.rs` over `harness/src/baseline.rs`
   (keeping that file's header), then `just repin`. The bar has moved.

## After changing anything the operator owns

`just repin`. Stage 2 compares against `verifier/PINS.json`, so an operator-side
edit without a re-pin makes every submission fail — which is the correct default,
because the alternative is scoring submissions against a contract that quietly
changed.

Re-pinning is also the moment to think about whether the change invalidates
already-accepted proofs. Anything in `lean/Lz77/` can; the harness cannot, because
no proof mentions it.

## Layout

```
lean/
  Lz77/          THE CONTRACT — pinned, never supplied by a miner
  Verify/        THE GATE — three lines the verifier writes itself
  Slot/          generated from the submission by stage 3
  Proof/         where the submission's Parse.lean is placed by stage 0
slot/            the crate root the submitted parse.rs becomes
harness/
  src/token.rs   the token encoding — the same function as LZ77.emit
  src/deflate.rs tokens to DEFLATE bytes. Trusted, fixed, identical for everyone
  src/baseline.rs the incumbent: a frozen copy of a promoted parse.rs
  src/main.rs    round-trip check, compressed bytes, speed floor
verifier/
  verify.py      the six stages
  extract.sh     charon + aeneas, run by the verifier
  init.sh        install the whole toolchain from nothing; --check to report only
  config.sh      the pins, and where each tool is found
  make-corpus.py the scoring corpus
  PINS.json      hashes of everything a miner may not change
corpus/          the reference corpus; hashes in docs/CORPUS.md
docs/            DESIGN, SCORING, CORPUS, THREAT_MODEL, TOOLCHAIN
```
