# Proof manual for the LZ77 parser

Start with the [miner guide](../docs/MINER.md) for the workflow and the
[competition page](https://conjectures.io/competitions/deflate) for current
rules and official metrics. This manual covers the parser contract and proof.

## Quick Summary

- You write one Rust file for the LZ77 parsing stage and one Lean file proving that its tokens decode back to the input. Benchmarking, admission, and rewards are separate steps; see [scoring](../docs/SCORING.md).
- Run `just bench` to measure locally, `just check` for the full local gate, and `just probe` to inspect a stuck proof goal.
- The proof covers only the places where you write a token. The search is free: any search needs only `Found`, which says the match is in range and its bytes were compared. Change the search and you rewrite one lemma.
- The template and examples illustrate parsing and proof strategies. Measure them on your own checkout rather than relying on fixed example results.
- The Rust and proof rules below describe the supported subset. Copy the example closest to the change you want to make.

```bash
./setup.sh
just corpus-pull
cp -r miner/template my-submission
just bench my-submission
VERIFY_CORPUS=corpus-stage1 just check my-submission
python miner/submit.py submit my-submission --hotkey <hotkey file> --url https://<api>
```

## 1. Set up

| step | command | notes |
|---|---|---|
| clone and set up | `./setup.sh` | apt packages, a pinned `just`, `uv` and `.venv`, `.env` from `.env.example`, then the Lean, Aeneas, Charon and Mathlib toolchain: about 15 minutes and 9 GB |
| only the fast parts | `./setup.sh --no-toolchain` | seconds; enough to run the Python tests and read the code, not enough to prove |
| what is installed | `./setup.sh --check` or `just doctor` | installs nothing, exit 1 if anything is missing |
| no root, no bubblewrap | set `VERIFY_SANDBOX=off` in `.env` | your proofs are checked unconfined; a validator never does this |
| a wrapped C compiler | also `VERIFY_SANDBOX=off`, and set the linker through `CARGO_TARGET_<triple>_LINKER`, not `RUSTFLAGS` | the score stage builds inside a read-only sandbox; the gate refuses to run with `RUSTFLAGS` set because extraction must use the pinned compilation recipe |
| the scoring corpus | `just corpus-pull` | fetches `corpus-stage1`, the public benchmark corpus; see [benchmark and corpora](../docs/BENCHMARK.md) |

Everything runs from the repository root. Submission directories can live anywhere; the recipes accept absolute paths.

## 2. What you submit

Exactly two files in one directory:

```
my-submission/
  parse.rs      the whole LZ77 parsing stage: hash, match verifier, search, decision, emission
  Parse.lean    a proof of `parse_spec`: the tokens `parse` writes decode back to the input
```

`parse.rs` is compiled as its own crate root and must be in the provable subset (section 5); stage 2 of the gate additionally checks every operation the extracted model calls against a closed allowlist of `core` and `alloc` operations (`validator/verifier/resolved.py`), so a `Vec`, slice indexing, `len`, and the checked, wrapping and saturating integer operations are in, and anything else needs a reviewed model, not a bypass. `Parse.lean` may import only `Lz77`, `Slot`, `Mathlib`, `Aeneas`, must contain no `sorry`, and must state `parse_spec` with the pinned obligation's meaning. The gate typechecks `LZ77.Obligation slot.parse` against your theorem; nothing is compared as text. Each file is under 512 KB.

## 3. What to achieve

Aim for a parser that is correct, fast, and compresses well on the configured
corpora. The validator verifies the proof and round trip, then records benchmark
evidence. Reward eligibility and weighting are described in
[scoring](../docs/SCORING.md); the [competition page](https://conjectures.io/competitions/deflate)
publishes current rules and official metrics. The shared DEFLATE encoder is in
`validator/measure`, so your change is the LZ77 parser and its proof.

## 4. How to measure

| command | what it tells you | when |
|---|---|---|
| `just bench my-submission` | local bytes and timing on the default corpus; with no directory it benchmarks the examples | when changing `parse.rs` |
| `just bench my-submission --corpus corpus-initial` | local comparison on the committed initial corpus | when using that corpus explicitly |
| `just check my-submission` | the seven-stage gate: intake, policy, static, extract, statement, axioms, score | before submitting, and whenever the proof changes |
| `just check-proof my-submission` | the same without the score | when only the proof changed |
| `just probe my-submission <line> --stop` | the goals and hypotheses at that line of your proof, against the real extraction, in a private workspace under `data/verification-workspace/` | when a proof step fails, especially inside `first \| ... \| ...` |
| `just extract my-submission` | the Lean model of your Rust, left in a printed private workspace | before writing a proof for new Rust |
| `just cost my-submission` | lines of Rust and of proof | when estimating proof size |

The validator measures on its own machine, on a corpus you may not see, so treat your time ratio as an estimate with a margin: the reference parsers' ratios move a few percent between machines. Bytes do not move at all.

## 5. The seven Rust rules

Charon and Aeneas translate imperative, index-based Rust into Lean. Iterator-shaped code is outside the subset. Stage 1 of the gate enforces the mechanical rules; the rest fail later and more expensively.

**Rule 1. Indices, `while`, and plain `if`.** Stage 1 parses your Rust with a syntax checker (`validator/precheck`) and rejects `unsafe` in any form, labelled loops, `extern` and foreign code, async functions, `use crate::`, attributes for conditional compilation or linker overrides, and any macro that is not pure Rust expansion. Stage 2 then rejects iterator adapters, trait objects and anything else outside the operation allowlist. `for ... in` fails there too: `Iterator` is opaque to Aeneas.

```rust
// rejected - Iterator is opaque, so there is nothing to reason about
let total: usize = xs.iter().map(|x| x.len()).sum();

// accepted
let mut total = 0usize;
let mut i = 0usize;
while i < xs.len() { total += xs[i].len(); i += 1; }
```

**Rule 2. Prefer `i <= n - k` to `i + k <= n`.** In the extracted model a slice may have length `usize::MAX`, so the addition can overflow and `parse` is not total. The guarded subtraction cannot. Hoist `has3` and `lim` out of the loop.

```rust
// rejected in the proof - the addition is not total
if pos + 3 <= n { ... }

// accepted
let has3 = n >= 3;
let lim = if has3 { n - 3 } else { 0 };
if has3 && pos <= lim { ... }
```

**Rule 3. Bound array indices with `%`, not `&`.** `h % 32768 < 32768` is one `omega` step; the mask needs a bitvector argument the tactics do not run.

**Rule 4. Every loop needs a counter that decreases regardless of the data.** A chain walk terminates because `probes` increases, not because the chain is acyclic. Walking a corrupt chain is harmless because `match_len` compares the bytes before anything is emitted.

```rust
let mut probes = 0usize;
while probes < MAX_PROBES && cur > 0 && cur <= pos {
    ...
    cur = prev[cpos % 32768] as usize;
    probes += 1;
}
```

**Rule 5. Lift a nested loop into its own function if it reads an array from the enclosing scope.** Aeneas reports `Unimplemented` for a second loop nested in `parse`'s outer loop when it reads a local array. Pass the array as a parameter: `find_match(input, prev, pos, cap, start)`. This is also the unit a submission replaces, so naming it keeps the rest of the proof untouched when you change the search. The same applies to `bool` loop state: use a sentinel index instead.

**Rule 6. No fallible arithmetic where it cannot be guarded.** A `while` guard may hold comparisons and arithmetic that provably cannot fail; move the rest into the body. Divisions need a non-zero divisor, `usize` subtraction needs ordered operands. `cur = 0` ends a walk without `break`. Two single-value `if`s instead of `if c { best = x; choice = y }`: the tuple `let` the latter produces is one `step*` will not enter.

```rust
while probes < MAX_PROBES && cur > 0 && cur <= pos {
    let cpos = cur - 1;
    if pos - cpos <= 32768 { ... } else { cur = 0; }
    probes += 1;
}
```

**Rule 7. The proof runs no code.** Rejected in `Parse.lean`: `#eval`, `run_cmd`, `run_tac`, `run_elab`, `initialize`, `dbg_trace`, `trace "..."`, any import outside the four. The scan reads the raw file, comments included, so do not name these commands in a comment either. Register lemmas with `@[local step]` instead of writing elaborators.

## 6. What you must prove, and what you need not

A token is a `u32`: `t < 256` is the literal byte `t`; `t = 2^24 + (dist-1)*256 + (len-3)` copies `len` bytes from `dist` back, with `1 <= dist <= 32768` and `3 <= len <= 258`. Copies may overlap. The encoding is arithmetic on purpose: `+`, `*`, `/`, `%` are what `omega` reasons about.

The obligation, `LZ77.Obligation` in `validator/lean/Lz77/Interface.lean`:

```lean
def Obligation
    (parse : Slice Std.U8 → Slice Std.U32 → Result (Std.Usize × Slice Std.U32)) : Prop :=
  ∀ (input : Slice Std.U8) (out : Slice Std.U32), input.length ≤ out.length →
    parse input out ⦃ fun r =>
      r.1.val ≤ input.length ∧
      r.2.length = out.length ∧
      Valid (bytes input) (toks r.2 r.1.val) ⦄
```

Four things: it never fails on any input, it always terminates, it does not change the buffer length, and the tokens decode back to the input (`LZ77.Valid` in `validator/lean/Lz77/Spec.lean`, the LZ77 layer of RFC 1951 without Huffman coding).

You do **not** have to prove anything about how you find matches, that a match is the best one, or that your data structures are consistent. The line falls at `Found`:

```lean
def Found (input : Slice Std.U8) (n pos best_len best_dist : Std.Usize) : Prop :=
  best_len.val < 3 ∨
    (3 ≤ best_len.val ∧ best_len.val ≤ 258 ∧ pos.val + best_len.val ≤ n.val ∧
      1 ≤ best_dist.val ∧ best_dist.val ≤ 32768 ∧ best_dist.val ≤ pos.val ∧
      Matches input (pos.val - best_dist.val) pos.val best_len.val)
```

Either you found nothing, or something in range whose bytes agree. Left of that line, a hash lands in range and an insert loop terminates and stays in bounds, postcondition `True`. Right of it, a token is written and the invariant steps. Change the search and the whole proof diff is one lemma establishing `Found`.

Your loop invariant is "the tokens written so far decode to the input consumed so far". `validator/lean/Lz77/Search.lean` steps it for you: `emit_lit`, `emit_match`, `Found.emit`, plus `ite_ok` and the tactic macros `prove_hash3`, `prove_match_len_loop`, `prove_match_len`.

```lean
theorem emit_lit (input : Slice Std.U8) (out : Slice Std.U32) (ntok : Std.Usize) (pos : Nat) (v : Std.U32)
    (hde : decode (toks out ntok.val) = some ((bytes input).take pos))
    (hpos : pos < input.length) (hntok : ntok.val < out.length)
    (hv : v.val = (bytes input)[pos]!) :
    decode (toks (out.set ntok v) (ntok.val + 1)) = some ((bytes input).take (pos + 1))
```

## 7. The ten proof rules

The verifier extracts `parse.rs` into `Slot/Funs.lean` in a private workspace, generates `Slot/Constants.lean` (`slot.X.val = n` for each constant you declared) and typechecks `theorem accepted : LZ77.Obligation slot.parse := fun i o h => Submission.parse_spec i o h`. Then `#print axioms` must show Lean's three and nothing else.

| # | rule | the failure it prevents |
|---|---|---|
| 1 | `i <= n - k`, never `i + k <= n` | overflow side goal on a `usize::MAX` slice |
| 2 | bound indices with `%`, not `&` | a bitvector argument the tactics do not run |
| 3 | no `bool` loop state; no loop nested in a loop that reads a local array | Aeneas `Unimplemented` at its loop fixed point |
| 4 | two single-value `if`s instead of one tuple-assigning `if` | a tuple `let` that `step*` will not enter; `mo-lazy` and `optimal` both hit this |
| 5 | every loop has a counter that decreases regardless of the data | a chain need not be acyclic |
| 6 | name facts by your Rust variables, never by generated names | `i6_post`, `__post2` change whenever the Rust ahead of them changes shape |
| 7 | `obtain`/`refine` right after `step*`; a loop-body goal is a flat conjunction | `refine ⟨⟨a, b⟩, c⟩` fails where `refine ⟨a, b, c⟩` is wanted |
| 8 | never `unfold` or `simp` an extracted constant; read it as `slot.X.val = n` | `irreducible` constants lose instance transparency; the literal goes stale when the Rust moves |
| 9 | `simp only [lift]` before `step*` around saturating ops; `if c then ok x else ok y` becomes `ok (if c then x else y)` via `ite_ok` | `step*` has no rule for `lift (saturating_add ..)` and will not enter a value-`if` in bind position |
| 10 | when `first \| A \| B` fails, probe | `first` reports only the last branch's error; `--stop` isolates one branch |

Two more that save time: the arithmetic tactic is `scalar_tac`, and it sees every `_post` fact in scope plus the generated constants; `step*` closes most side goals itself, so try it before writing anything. `step*` will not enter a `do` block whose first statement is an `if`; cut it with `Std.WP.spec_bind (Pₘ := fun r => Found input n pos r.1 r.2)`, which is where you wanted `Found` anyway.

How a proof is laid out:

```text
open LZ77 (toks bytes bytes_getElem! Matches Found emit_lit emit_match ...)

hash3_spec          : by prove_hash3            -- one line if you kept the template's hash
match_len_loop_spec : by prove_match_len_loop
match_len_spec      : by prove_match_len
<your search>_spec  : postcondition Found       -- the only lemma a new search needs
<insert loops>_spec : postcondition True        -- terminate, stay in bounds
parse_loop_spec     : the invariant             -- one case per token-writing site
parse_spec          : the obligation, unchanged -- copy it
```

The invariant for a greedy parser: `pos ≤ n ∧ ntok ≤ pos ∧ out.length = out0.length ∧ decode (toks out ntok) = some (take pos (bytes input))`. A lazy parser adds `Pending` and replaces `pos` by `emitted pos len` in two places. A DP parser re-verifies each chosen match with `match_len` before writing it, so its invariant is the greedy one.

## 8. A worked example

This example changes one search constant. Run it locally to see the results on
your current corpus and machine.

```bash
cp -r miner/examples/lazy my-submission
sed -i 's/MAX_PROBES: usize = 32/MAX_PROBES: usize = 48/' my-submission/parse.rs

just bench my-submission
VERIFY_CORPUS=corpus-stage1 just check my-submission
```

This proof reads the depth from the extracted constant,
`slot.MAX_PROBES.val - probes`, so changing the constant does not require a
hard-coded proof edit. Inspect the actual gate output before submitting.

## 9. Read in this order

`miner/examples/no-lz77/Parse.lean` (one token-writing site), `miner/template` (a literal and a match site, single-slot hash), `miner/examples/hash-chains` (the search replaced, one lemma changed), `miner/examples/lazy` (a pending match), `miner/examples/optimal` (a DP whose output is re-verified before it is written). Copy the closest one.

## 10. Submit

```bash
python miner/submit.py submit my-submission --hotkey ~/.bittensor/wallets/<w>/hotkeys/<h> --url https://<api>
python miner/submit.py status <id> --url ...         # the stage report, bytes, time ratio, minutes later
python miner/submit.py leaderboard --url ...         # every hotkey's best accepted submission, ranked
```

`--url` is the conjectures platform API's origin; it serves every competition, and this one at `/v1/competitions/deflate` (`--competition` picks another). The two files are signed with your hotkey over the competition, their hash, your address and the current time, so a signature for one competition cannot be replayed against another; the platform refuses a timestamp more than five minutes from its own clock, so keep your clock right. Submissions are verified as they arrive; the same files twice return the same id.

**Submitting costs one registration on the subnet.** Register, submit, and the slot is spent when the gate accepts. A rejection costs nothing, so fix the proof and resubmit on the same registration; `submit` prints how many slots you have left.

## 11. When it fails

1. `just check my-submission` names the stage. Stage 1 is a syntax rule. Stage 2 is an operation outside the allowlist, named in the message. Stage 3 is your Rust (Rust rules 5 and 6, proof rules 3 and 4). Stage 4 is your proof. Stage 5 is `sorry` or an axiom. Stage 6 is bytes or time. Failed runs keep their workspace under `data/verification-workspace/` with every log.
2. Read the first error. `unsolved goals` with a goal you believe: proof rule 8 or a missing `_post` fact. `Unknown identifier x_post`: proof rule 6. `scalar_tac failed`: probe the line, look for the missing bound.
3. `just probe my-submission LINE`, with `--stop` when the failing tactic is inside `first`.
4. Compare with the example closest to your emission site.

## 12. What gets you rejected

A third file. `unsafe`, iterators, an external crate, a non-pure macro, an operation outside the allowlist, or an import other than the four. `sorry`, or any axiom beyond Lean's three. A weakened theorem. A token stream that does not round-trip through two independent inflaters. A parser whose tokens differ between runs. A signature outside the service's timestamp window. For current benchmark eligibility limits, consult the [competition page](https://conjectures.io/competitions/deflate) and [scoring](../docs/SCORING.md).
