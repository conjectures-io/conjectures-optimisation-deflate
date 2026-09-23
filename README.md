# conjectures-miniz-oxide-competition

Verification now runs in private workspaces with separate static, Lean and benchmark
stages. See [verification commands, supported Rust and database eligibility](docs/VERIFICATION.md).

## Quick Summary

- A proof-gated DEFLATE competition. Miners submit a Rust LZ77 parser and a Lean proof that its token stream decodes back to the input; a six-stage verifier re-extracts the Rust with Charon and Aeneas, type-checks the proof against a pinned contract inside a sandbox, and scores accepted parsers by compressed bytes on a held-out corpus. Lower wins.
- Participation is one signed upload, paid for by one subnet registration: the service verifies submissions as they arrive and ranks every hotkey's best on a leaderboard. Ties go to the earlier submission. The speed floor is 8x the incumbent. A registration is spent only when the gate accepts, so a rejection is a free retry.
- One command from a fresh clone to a passing self-test.

```bash
git clone <this repo> && cd conjectures-miniz-oxide-competition
./setup.sh                      # apt packages, just, .venv, .env, Lean/Aeneas toolchain (~15 min, 9 GB); idempotent
just check miner/template       # the whole gate, then the score, on the first incumbent
just --list                     # everything else
```

## Why enter

**The slot is the whole LZ77 parsing stage**, not a constant: hash, match verifier,
candidate search, the greedy, lazy or optimal decision, emission. 66 to 254 lines of Rust that
Charon and Aeneas translate with no hand-written axioms.

**Correctness does not depend on the search.** The proof says the hash lands in range
and nothing about what it computes; the loop that maintains the chains has postcondition
`True`; only the bytes actually compared before a match is emitted are load-bearing.
So a better search costs one rewritten lemma, and even a change to the emission stayed
under 120 lines:

| | `parse.rs` | `Parse.lean` | bytes | vs incumbent | time |
|---|---|---|---|---|---|
| `miner/examples/no-lz77` (literals only) | 20 | 51 | 5,147,015 | 2.390x | 0.01x |
| `miner/template` (greedy, hash head) - the first incumbent | 66 | 152 | 2,605,048 | 1.210x | 0.15x |
| `miner/examples/hash-chains` (16 probes), `hc-d4`, `hc-d64` | 90 | 193 | 2,239,367 / 2,354,578 / 2,197,601 | 1.040x / 1.093x / 1.021x | |
| `miner/examples/lazy` (lazy, 32 probes) - **the incumbent** | 118 | 262 | 2,153,387 | 1.000x | 1.0x |
| `miner/examples/mo-lazy` (miniz level-9 strategy) | 254 | 370 | 2,118,446 | 0.984x | 2.5x |
| `miner/examples/optimal` (optimal parse, 24 probes) | 198 | 344 | 2,115,138 | 0.982x | 6.5x |
| `miner/examples/optimal-iter` (optimal parse, one cost iteration) | 339 | 613 | 2,102,388 | 0.976x | 7.5x |
| miniz_oxide level 9 | | | 2,126,479 | 0.987x | |
| **libdeflate level 12** | | | **2,013,342** | **0.935x** | |

The incumbent moved once already: lazy was promoted over the template, and with it
the speed floor (8x of the incumbent) grew sevenfold in absolute terms, which is what
made optimal parsing admissible. libdeflate is still 6.5% under the incumbent, and the
gap is algorithmic: hash chains saturate at miniz level 9 whatever their depth; the
rest is optimal parsing and block splitting, all inside the provable subset, because
SIMD cannot change which match is chosen.

## Miner

The complete guide is [`miner/MANUAL.md`](miner/MANUAL.md); this section is the short form.

```bash
cp -r miner/template my-submission          # a passing submission to start from
just bench my-submission                    # ratio and time only, seconds - measure before proving
just check my-submission                    # the six-stage gate, then the score

python miner/submit.py submit my-submission --hotkey ~/.bittensor/wallets/<w>/hotkeys/<h> --url http://<validator>:9200
python miner/submit.py status <id> --url ...                            # the stage report, bytes, time ratio, minutes later
python miner/submit.py leaderboard --url ...                            # every hotkey's best accepted submission, ranked
```

A submission is exactly two files, `parse.rs` and `Parse.lean`, signed with the hotkey over
their hash, your address and the current time; the nine references above are complete,
passing examples to start from. Submissions are verified as they arrive and the same files
twice return the same id.

**Submitting costs one registration on the subnet.** Register, submit, and the slot is
spent when the gate *accepts* -- a rejection costs nothing, so fix the proof and resubmit
on the same registration. `submit` prints how many slots you have left. Your machine's
clock has to be roughly right: the signature carries a timestamp and the validator refuses
one more than five minutes from its own.

## The benchmark

Two stages, one manifest, 28 files and ~15.9 MB each, cut from a ~900 MB pool of real
data. **Stage 1 is public**, so a miner scores against exactly what a validator does and
never needs the pool. **Stage 2 is held out**: the same 28 filenames, the same format
labels and the same size budget, cut from the *disjoint* half of every pool with a seed
the operator keeps.

Neither is committed here. Each lives in its own repository and arrives via
`just corpus-pull`:

| repository | | |
|---|---|---|
| `conjectures-compression-corpus-1` | public | `data/benchmark/corpus-stage1/` |
| `conjectures-compression-corpus-2` | private | `data/benchmark/corpus-stage2/` |

That split is deliberate. If stage 2's bytes were committed here, this repository could
never be made public and could never be forked into the miner-facing one -- and since
git keeps history, deleting the files later would not undo either. Separating the
datasets puts the boundary on a repository ACL, which you can change, rather than on
this history, which you cannot. `corpus-pull` skips stage 2 with a note rather than an
error when you lack access, so a miner still gets a working checkout.

```bash
just corpus-pull                            # both stages; stage 2 skipped without access
                                             # corpus-stage1 is the default (validator/corpora.toml)
VERIFY_CORPUS=corpus-stage2 just check my-submission
```

Re-cutting a corpus -- for a new round, or after a leak -- needs the pool:

```bash
just corpus-sources                         # once: ~900 MB into data/benchmark/sources/
just corpus-verify                          # complete? undrifted? still reproduces?
just corpus-build --stage 1                 # reproduces the published public set
just corpus-build --stage 2                 # reads BENCHMARK_STAGE2_SEED from .env
```

Then commit the result to the matching dataset repository.

**Why the corpora are distributed as bytes rather than rebuilt from the fetch script.**
The tidier design is to ship the fetch script and have everyone build their own, and it
does not work here: **38 of the 73 sources are floating URLs.** Eighteen are GitHub
branch heads -- sqlite, curl, mathlib4, django and TypeScript all take commits most days
-- and the rest are live Wikipedia articles, current npm metadata, CSVs regenerated
daily, and an arXiv OAI query that returns different records every call. A miner and a
validator fetching a week apart would score against different corpora, which for a
competition ranked on compressed bytes is fatal. The bytes in the dataset repositories
are the specification; the pool is only needed to cut a new stage.

`just corpus-verify` checks a pool anyway, and `just corpus-sources` runs it on the way
out: every source present and non-empty, and -- the one that matters -- whether the pool
as it stands still cuts a byte-identical stage 1. Exit 1 means re-fetch; exit 3 means
upstream moved, which is expected in time and breaks nothing, because the published
bytes are the reference.

**The same volatility means stage 2 must be distributed as bytes, not as a seed.** Two
validators rebuilding from one seed at different times get different corpora and would
rank submissions differently. `just corpus-package` writes the held-out set to a single
checksummed archive under `data/benchmark/dist/` (gitignored), carrying a manifest with
per-file hashes and the seed's *fingerprint* — never the seed. Put it somewhere private;
publishing it ends its usefulness. Each validator then runs `just corpus-install <url>`,
which verifies the archive checksum, checks every file against the manifest, and refuses
to overwrite an existing corpus unless told to.

Everything except one 40 KB file is real. `scripts/fetch-corpus-sources.sh` downloads from
GitHub (sqlite, redis, curl, ripgrep, tokio, serde, django, flask, requests, mathlib4,
maven, TypeScript, bootstrap, the Rust book), Project Gutenberg, loghub's log corpora,
cdnjs, the npm registry, NCBI, Wikipedia and Hugging Face.
**[CORPUS-SOURCES.md](CORPUS-SOURCES.md) lists them all** -- what each corpus file
is cut from, every download with its licence, and the licence totals. It is generated
from the download manifest and the byte counts recorded while the pools are built, so it
cannot drift from what was actually used. Nothing third-party is redistributed by this repository -- the pool is
gitignored and each machine fetches its own.

| group | files | source |
|---|---|---|
| source code | `source.c.txt` `source.rs.txt` `source.py.txt` `lean.txt` | sqlite/redis/curl, ripgrep/tokio/serde, django/flask/requests, mathlib4 |
| natural language | `prose.txt` `docs.md.txt` `multibyte.txt` | Gutenberg English; repo docs and the Rust book; Chinese/Japanese/Russian novels plus gettext catalogues |
| structured text | `records.json.txt` `catalog.xml.txt` `page.html.txt` `metrics.csv.txt` `dump.sql.txt` `server.log` | npm registry, arXiv OAI and Maven POMs, Wikipedia articles, OurAirports and COVID data, Chinook/Sakila/Northwind, loghub |
| dense / encoded | `bundle.min.js.txt` `sourcemap.map.txt` | cdnjs bundles; source maps, which are base64 VLQ inside JSON |
| binary and compressed | `binary.db.bin` `images.bin` `compressed.bin` `genome.fasta` | SQLite test databases and gettext `.mo`; real PNG/JPEG; jars and gzip tarballs; E. coli and yeast genomes |
| model weights | `weights-f32.bin` `weights-f16.bin` `weights-bf16.bin` `weights-q8.bin` | all-MiniLM-L6-v2 (F32), pythia-70m (F16), SmolLM2-135M (BF16), and SmolLM2-135M-Instruct quantized to Q8_0 and Q4_K_M — all Apache-2.0, fetched as 16 MB heads |
| degenerate *(the one generated part)* | `sparse.bin` | 40 KB of long zero runs |

Most parts are concatenations of many real files, so they take the repository's
existing `<what>.<ext>.txt` convention: `catalog.xml.txt` is XML, but it is not one XML
document.

**The one generated part carries 0.25% of the bytes and 0.00% of the headroom.** It
is there because nothing natural exercises distance-1 matches at the 258 cap cleanly;
everything else is real.

An earlier version of this corpus generated most parts from seeded PRNGs. That version
was tuned until its match distances sat on Silesia's and its weight compressibility sat
within 0.2% of a real checkpoint's, and it was still the wrong idea: synthetic data can
only contain the structure someone thought to model, which is exactly the structure a
parser can be tuned against. It also flattered submissions -- its most redundant file
had a `gap` of 0.655 against 0.686 for the most redundant real one. The calibration did
hold up, for what it is worth: real BF16 profiles at `gap` 0.984 and 79.8% zlib against
the generator's 0.984 and 79.2%.

Real checkpoints also carry what a generator was never going to: `weights-q8.bin` and
`weights-q4k.bin` are llama.cpp's own output, Q8_0's flat 34-byte blocks against
Q4_K_M's 256-element superblocks with 6-bit scales. Both profile dead flat (`gap`
1.000) -- quantized weights are genuinely incompressible, which is worth knowing and is
why they are small. Only BF16 moves at all, at 0.984. One wrinkle the profiler caught:
two quantizations of the same model share their metadata byte for byte, and for SmolLM2
that is 1.8 MB of tokenizer vocabulary. Pooling it made the two parts measure the same
thing; the builder skips past it to the tensor data.

### How the sizes were chosen

A `corpus-profile` binary reported, per file, `gap` = optimal-parse bytes over
greedy-parse bytes -- the entire quantity this competition scores -- plus match length
and distance distributions:

```bash
corpus-profile stage1 data/benchmark/corpus-stage1 silesia data/benchmark/silesia
```

Its source lived in `scripts/pareto-bench/`, retired along with the rest of the old
benchmark path (see Layout, below) -- these commands can't be re-run as written until
it's ported to `validator/measure`. The methodology below is what it settled.

Two things it settles. First, which files can rank anyone at all: parts profiling at
`gap` ≥ 0.98 cannot change their output under any parser, so they are held to a small
share of the corpus and kept only for what they do test -- that a parser round-trips
hostile input and does not crawl on it.

Second, speed. Real logs and SQL dumps turn out to be so redundant that `optimal` costs
38x and 41x the incumbent's time on them for little headroom, while prose, markdown and
C source buy more at 3-5x. A first balance put `optimal` at 7.6x against the harness's
8.0x floor -- 5% of headroom, enough that the next better-but-slower parser would be
rejected on time rather than judged on bytes. Weighting toward the cheap discriminators
brought it to 5.6x and raised total headroom 16% at the same time.

Measured results for the whole candidate set -- the two stages against each other,
the Pareto frontier, per-format behaviour and the speed margin -- are in
[docs/benchmark/RESULTS.md](docs/benchmark/RESULTS.md), with the raw run file beside
it. Headline: every provable candidate ranks the same on both stages to within 0.001.

### Coverage

A second tool, `scripts/corpus-coverage.py`, asks whether the manifest spans the parse
behaviour real data shows (it reads `corpus-profile`'s output, so it's affected by the
same retirement noted above) -- over measured behaviour, not over format names, because
an LZ77 parser does not see formats and two extensions can be one
behaviour. Each file becomes a point in six profile axes; it reports **reach** (for each
file in an external reference corpus, the distance to the nearest benchmark file) and
**spacing** (parts that measure the same thing twice). Silesia is the reference.

It has decided three manifest changes. A `.docx` part was built and dropped at 0.035
from `images.bin` -- a zip of XML behaves like any other compressed container. Two GGUF
quantizations profiled 0.002 apart, so only Q8_0 is carried. WebAssembly was added
because Silesia's `mozilla` had nothing within 0.125; it is now 0.066. Current worst
reach is 0.161, on `osdb`.

[CORPUS-SOURCES.md](CORPUS-SOURCES.md) carries the full data-type taxonomy, the list of
popular types that are *not* here and why, and the two places the metric is deliberately
overruled.

### What the hidden stage does and does not stop

**It stops memorization.** The pool is cut into 128 KB blocks and split by index
parity: stage 1 gets the even blocks, stage 2 the odd ones. Measured, 24 of the 26
sliced parts share *no* 512-byte block between the stages; the two that do share 1.4%
and 0.3% are genuinely repeated boilerplate in the upstream data. So stage 2 is real
data the public set never contained.

The pool itself is public -- it is GitHub and Gutenberg, and the fetch script is in the
open. What is hidden is which slice, in which order. That is a quantitative
defence, and a much stronger one than the synthetic corpus had: stage 0 of the gate
caps a submission at 1 MB, against ~290 MB in stage 2's half of the pool. It does not
depend on anyone failing to find the data.

**It does not stop distributional tuning**, and should not pretend to: the two stages
are deliberately the same distribution, because a held-out set that is a *different*
problem is not a fair one. Picking chain depth by content is legitimate adaptive
compression and no gate can tell it from overfitting. Breadth is what limits it.

Stage 2 is a fair drop-in, not a harder test. Every reference ranks identically on
both, within 0.1%:

| | stage 1 | stage 2 |
|---|---|---|
| `miner/template` | 1.14718x | 1.14718x |
| `miner/examples/hash-chains` | 1.02853x | 1.02920x |
| `miner/examples/lazy` (incumbent) | 1.00000x | 1.00000x |
| `miner/examples/optimal` | 0.98423x | 0.98481x |

### Cost, against `corpus-initial`

| | `corpus-initial` | staged corpus |
|---|---|---|
| files / raw bytes | 5 / 8.1 MB | 28 / 15.9 MB |
| compressibility span | 12.5% – 40.2% | 3.1% – 94.8% |
| `optimal` vs incumbent | 0.98224x | 0.98423x |
| `optimal` parse time vs incumbent | 5.86x | 5.53x |

14% of the corpus is near-incompressible and the score is a pooled byte ratio, so a
gain on the compressible part is diluted -- `optimal` wins 1.58% here against 1.78% on
`corpus-initial`. Byte counts are exact rather than sampled, so this costs display
range, not resolution: a one-byte win is still a one-byte win, and ties still break on
submission time. The per-file budget is one table at the top of
`scripts/make-benchmark-corpus.py`; re-run `corpus-profile` after changing it, because
headroom and speed trade against each other.

## Operator

```bash
./setup.sh --chain              # the bittensor SDK on top of a normal setup; validators only
just db-up && just db-migrate   # Postgres 17, then the schema
just service                    # the API
just service-worker             # the gate, draining the queue
just chain-watcher              # subnet registrations -> the store
just weight-setter              # scores the round and sets weights, once an epoch
# or, all four at once:  pm2 start pm2/service.config.js
```

Four processes, one database, one wallet -- [docs/OPERATIONS.md](docs/OPERATIONS.md) is
the whole of it, including what to check when something is wrong.

The store is Postgres, not a file. It holds submissions, the subnet registrations the
chain watcher records, the entitlement claims that tie the two together, and the audit of
every weight vector. `just db-psql` opens a shell on it; `just db-weights` prints what the
last vector paid and why. A validator upgrading from the old SQLite file runs
`just db-import-sqlite` once.

**One registration buys one accepted submission.** A hotkey with no registration on the
subnet cannot submit at all; a hotkey with one may have one submission in the queue, and
it is charged only when the gate accepts. A rejection is a free retry -- fix the proof and
resubmit on the same registration. To submit again after an acceptance, register again.

The API and the gate are separate processes on purpose: the gate is a ~45 minute
subprocess per submission, so as a thread it pinned the API to one worker and took the API
down whenever it died. Several `service-worker` processes can drain one queue, on one
machine or on several -- each claims a different submission. Run exactly one chain watcher
and one weight setter; without the watcher no hotkey has a registration, and so nobody can
submit at all.

**Emission is 60% Pareto position, 40% recent improvement.** Sixty per cent follows the
frontier, weighted by how much each point actually buys rather than by mere membership;
forty follows the last ten improvements on the record, decaying, newest most. What neither
claims burns. `just weights-preview` recalculates an operator preview using the current
formula and stored benchmark evidence without touching the database or chain; `WEIGHT_DRY_RUN=1` runs the whole weight-setting path except the last
call, and [docs/SCORING.md](docs/SCORING.md) is the argument for why the default weight
function is the one it is.

Corpora live in `validator/corpora.toml` (`just corpora` lists them); a held-out one is marked `public = false`, which keeps its per-file numbers inside the validator and reports only totals. `VERIFY_CORPUS` in `.env` overrides the default for one run, by name or by directory -- a validator running the staged benchmark points it at `corpus-stage2`, pulled by `just corpus-pull` and built by `just corpus-build --stage 2` from a `BENCHMARK_STAGE2_SEED` that must never reach the public repo, CI logs or the miners' side of the wire. Promote a leader by copying its `parse.rs` over `validator/incumbent/parse.rs` (keep the header) and running `just repin`; every later submission is scored against it. After any edit to a pinned file, `just repin`.

## The gate

| stage | checks | stops |
|---|---|---|
| 0 intake | exactly two files, each under 512 KB | smuggled files |
| 1 policy | syntax-aware Rust precheck; Lean source prefilter | unsafe code, conditional compilation, custom macros, direct I/O |
| 2 static | pinned Charon IR and reviewed external operations | aliased/indirect capabilities and unsupported models |
| 3 extract | Charon and Aeneas run by the validator | a self-supplied extraction |
| 4 statement | `LZ77.Obligation slot.parse` type-checks, in bubblewrap, under time and memory caps | a weakened theorem, a runaway proof |
| 5 axioms | only `propext`, `Classical.choice`, `Quot.sound`, read from a separate read-only `lean` run; extraction re-hashed | `sorry`, a forged report |
| 6 score | each parser built as its own cdylib in a sandbox that may write only its own workspace, then measured in one that may write nothing: round trip through two inflaters, bytes, speed floor | wrong output, a slow win |

Exit 0 accepted, 1 rejected, 2 the validator itself is broken. Pin integrity is checked at setup/CI, not per submission. See [the verification guide](docs/VERIFICATION.md) for independent stage commands and the supported subset.

## Layout

```
setup.sh                 from a fresh clone to a passing self-test
CORPUS-SOURCES.md        every benchmark source, its licence, and what it feeds
justfile                 every command; `just --list`
pyproject.toml           all Python deps (uv), ruff and pyright config; ./.venv via `uv sync`
                         the `chain` group is the bittensor SDK: `./setup.sh --chain`, validators only
compose.yaml             Postgres 17 and the one-shot migration runner
.env.example             VERIFY_*, SERVICE_*, POSTGRES_* with defaults; copied to .env
deploy/
  db/                    first-boot extensions, GUCs, the read-only monitor role; tuned postgresql.conf
  migrate/               Alembic: the schema's deploy path, and the image that applies it
miner/
  MANUAL.md              the one document a miner reads: setup, rules, contract, proof rules, worked example, submit
  submit.py              submit, status, leaderboard
  template/              the simplest passing submission, with its proof
  examples/              no-lz77, hash-chains, hc-d4, hc-d64, lazy (the incumbent), mo-lazy, optimal, optimal-iter: all proven
validator/
  verifier/              verify.py (the gate), init.sh (toolchain), config.sh (pins), extract.sh
  lean/Lz77/             the contract: token spec, the two lemmas a proof uses, the search library every proof shares, the obligation
  lean/Verify/           the gate's three lines
  measure/               the engine: trusted DEFLATE encoder, round trip, timing; candidate/ is the crate template every parser is built from
  incumbent/parse.rs     what every submission is measured against
  bench/                 the driver (workspace, sandboxed build, sandboxed measurement), the verdict, the reports, and `python -m bench`
  sandbox/bwrap.py       generic confinement; knows nothing about benchmarks
  corpora.toml           what can be measured, which is the default, and which is held out
                         (format labels live beside each corpus instead, see below)
  db/                    the store: models, migrations' source of truth, and four repositories
  chain/                 the subnet: the two seams, the poll loop, the cadence; finney.py alone touches the SDK
  scoring/               the 60/40 rule, and the eight weight functions scripts/pareto-weights.py argued over
  workers/               chain-watcher, weight-setter, and `weights-preview`
  service/               the API, and the gate worker that drains the queue (separate processes)
  tools/                 one-off operator scripts (the SQLite import)
  tests/                 `just test`: one test per attack, plus the references through the gate
scripts/
  fetch-corpus-sources.sh   the ~800 MB real-world pool the corpus is cut from, weights included
  SOURCES.tsv               machine record of the pool; renders to CORPUS-SOURCES.md
  make-benchmark-corpus.py  the staged benchmark: one 28-part manifest, cut twice
  pull-corpus.sh            fetch both corpora from their dataset repositories
  download-silesia.sh       the Silesia reference corpus: the control
  corpus-coverage.py        does the manifest span real-world parse behaviour? (WIP: its
                            corpus-profile source lived in the now-retired pareto-bench/;
                            needs porting to validator/measure, see below)
  pareto-weights.py         the eight weight functions compared on synthetic shapes and real
                            runs; the functions themselves are validator/scoring/pareto.py
  verify-corpus.py          is a downloaded pool complete, undrifted, reproducing?
data/benchmark/          corpus-stage1/ and corpus-stage2/ (gitignored; `just corpus-pull`
                         fetches them from their own repositories), sources/ (gitignored,
                         the ~900 MB pool both stages are cut from), corpus-initial/
                         (committed, the original five files), silesia/ and
                         silesia-subset/ (gitignored, downloaded); each corpus has a
                         <name>.formats.json sibling (filename -> format label) -- never
                         inside the directory itself, so scoring never compresses it as
                         data. corpus-initial.formats.json is committed by hand;
                         silesia*.formats.json are regenerated by download-silesia.sh;
                         corpus-stage{1,2}.formats.json are mirrored by corpus-pull from
                         formats.json in each dataset repo's own root, beside its README
                         and SOURCES.md
data/bench-workspace/    one directory per benchmark run; kept on failure, swept by `just bench-clean`
pm2/                     the service under PM2
.github/workflows/       CI: fast tier on every push, full tier with the toolchain nightly
```

Configuration is `.env`: `VERIFY_SANDBOX=off` lets a miner without bubblewrap run the gate unconfined (never a validator); `VERIFY_LEAN_TIMEOUT`, `VERIFY_LEAN_MEMORY_MB`, `VERIFY_TOTAL_TIMEOUT`, `SERVICE_PORT` do what their names say. The store is `POSTGRES_*`, or a single `DATABASE_URL` that overrides them. `VERIFY_CORPUS=<name|dir>` scores against a corpus other than the default, e.g. `VERIFY_CORPUS=silesia-subset just bench miner/template`; `just corpus-download` fetches the Silesia reference corpus (`--subset` for a fast ~34 MB mix, `--full` for the standard ~202 MB set). `VERIFY_BENCH_*` tune the benchmark's own sandbox, reps and workspace retention — see `validator/bench/driver.py`.

## Benchmark

```bash
just bench                                                     # every candidate on the default corpus, timed as the gate times
just bench my-submission --corpus silesia-subset               # any submissions, any configured corpus
just corpora                                                   # what is configured, and which is the default
just bench-report                                              # score, floor verdicts, Pareto front, per-format tables, stability, plots
just bench-compare data/benchmark-runs/A.jsonl data/benchmark-runs/B.jsonl   # two runs of the same code must agree
```

With no arguments the candidates are `miner/template` and every `miner/examples/*`, so adding one is adding a directory; each candidate is measured with the incumbent only by default. Set `VERIFY_BENCH_BARS=1` to include the external `miniz_oxide` and `libdeflate` references for local comparison; `--no-bars` explicitly disables them. This default also applies to `just bench-db` and `just baseline-seed`. Each parser is compiled as its own cdylib and `dlopen`ed, the incumbent included, so whatever that boundary costs it costs both sides and cancels in the ratio. Every warmup and measured round runs both LZ77 and the shared DEFLATE encoder. The harness records LZ77 time, encoding time, and their paired sum separately. Benchmark summaries and the speed floor use the sum of per-file median **total compression times**, excluding warmups. The Pareto speed axis uses per-file candidate/incumbent ratios of these median totals, averaged equally within each corpus and then equally across corpora. The median total is computed from each repetition’s stage sum, not by adding stage medians. File I/O, token hashing, and decompression checks are outside the timers; token hashes still detect nondeterminism every round. Runs record the sha256 of every source and corpus file and are never overwritten.

### Memory and CPU limits: systemd user setup

On Linux with systemd, benchmarks use `systemd-run --user --scope` to apply memory and CPU limits, alongside bubblewrap isolation. This requires a running systemd user manager. If you see `Failed to connect to bus: No such file or directory`, check the user session:

```bash
loginctl show-user "$(id -un)" -p State -p Linger -p RuntimePath
systemctl --user status
```

If the user is not logged in or lingering, enable lingering and start the user manager. Run these commands as the account that will run the benchmark, using `sudo` only as shown:

```bash
sudo loginctl enable-linger "$(id -un)"
sudo systemctl start "user@$(id -u).service"
export XDG_RUNTIME_DIR="/run/user/$(id -u)"
export DBUS_SESSION_BUS_ADDRESS="unix:path=$XDG_RUNTIME_DIR/bus"
```

[Lingering](https://www.freedesktop.org/software/systemd/man/latest/loginctl.html#enable-linger%20USER%E2%80%A6) keeps the user manager available after logout and starts it at boot. The exports point this shell at that user's runtime directory and bus; they do not start the manager themselves.

Verify that the requested limits can be applied, then benchmark:

```bash
# Choose CPU IDs available on your machine; this example uses logical CPUs 2–3.
taskset -pc $$
systemd-run --user --scope -p MemoryMax=2048M -p AllowedCPUs=2-3 true

VERIFY_BENCH_BUILD_MEMORY_MB=4096 \
VERIFY_BENCH_MEMORY_MB=2048 \
VERIFY_BENCH_CPUS=2-3 \
just bench miner/examples/lazy/parse.rs
```

This allows 4 GiB during compilation and 2 GiB during measurement, with both restricted to logical CPUs 2–3. CPU restriction does not reserve those CPUs exclusively or impose a CPU-time quota. These settings can also go in `.env`; memory limits default to the values above, while CPU placement is unrestricted by default.

If the systemd resource-limit probe fails, the local benchmark CLI warns that it is running without memory or CPU limits and retains bubblewrap isolation when available. A successful benchmark alone therefore does not confirm that limits were applied: the probe above must succeed, and the benchmark must not report that fallback. Validator benchmark runs reject a failed resource-limit probe.

## Documents

[Benchmark storage](docs/BENCHMARK_STORAGE.md) describes the five-table raw result and
aggregation schema, timing queries, and migration rollback commands.

| | |
|---|---|
| [miner/MANUAL.md](miner/MANUAL.md) | mining, start to finish: setup, the two files, the seven Rust rules, the contract, the ten proof rules, a worked example, submit |
| [docs/SCORING.md](docs/SCORING.md) | how emission is scored: the 60/40 rule, worked on the real frontier |
| [docs/OPERATIONS.md](docs/OPERATIONS.md) | running a validator: the four processes, the store, the wallet, what to check |
| [CORPUS-SOURCES.md](CORPUS-SOURCES.md) | every benchmark source, its licence, and what it feeds |

## Trusted base

Lean's kernel with its three axioms; Mathlib; Aeneas's Lean library; Charon and Aeneas themselves (the extracted model is what the proof is about); `measure/src/deflate.rs` and `token.rs`, unproved. Every toolchain download is sha256-pinned in `validator/verifier/config.sh`. The round-trip check through two independent inflaters is the empirical backstop for the last two.

### Saving benchmark evidence to Postgres

Ordinary `just bench` remains local and does not connect to Postgres. To opt in:

```bash
just db-migrate
just bench-db miner/examples/lazy/parse.rs --corpus silesia-subset
just bench-import data/benchmark-runs/<run-uuid>.jsonl
```

`bench-db` accepts the same arguments as `bench`, checks the database before benchmarking,
and saves one complete local JSONL artifact per candidate before importing it. Both DB
commands use `DATABASE_URL` or the existing `POSTGRES_*` settings in `.env`.
They print database run IDs; aggregation, scoring, and weights remain separate.

If a database write fails, the command exits unsuccessfully and the artifacts remain
available for `bench-import`. Retrying returns the existing run ID. Multiple paths are
accepted; each file is committed independently. Old single-candidate v3 JSONL files are
supported. Old merged multi-candidate reports are rejected because they discarded
reference samples. Importing requires neither corpus/source files nor a Rust build.

### Baseline frontier and database aggregation

`just baseline-seed --corpus corpus-stage1 --corpus corpus-stage2` incrementally verifies
and benchmarks the reference submissions into the database. Use `--overwrite` for fresh
measurements, preserving history. `just weights-preview --out-dir data/benchmark-reports/baselines`
plots the resulting frontier and baseline burn allocations. See [operations](docs/OPERATIONS.md)
and [scoring](docs/SCORING.md) for aggregation inputs, timing uncertainty and payout eligibility.

### Compression timing protocol (v4)

`just bench` and `just bench-db` report `lz77`, `encode`, and `total` seconds.
`just weights-preview` uses equal-corpus, equal-file mean candidate/incumbent
total-time ratios for the Pareto speed axis; absolute times remain telemetry. The shared encoder's cost
therefore counts toward a submission's speed, including savings from fewer tokens.
External reference compressors report their full compression time with no stage split.
The token output buffer is allocated before timing; allocation inside LZ77 and the
encoder is included. This measures the compression computation, excluding harness I/O
and correctness checks.

Migration `0006` adds nullable `encode_s` and `total_s` to `benchmark_speed_samples`,
and `compression_seconds` to submissions and aggregations. `time_s` retains its
historical meaning: LZ77 for submissions, full compression for external references.
`parse_seconds` remains LZ77 telemetry; new aggregations' `incumbent_seconds` is total
compression time. Per-stage medians/stddev and total-time bootstrap uncertainty are
retained in aggregation statistics.

Old v3 measurements remain importable and inspectable, but their single encoding
sample cannot reconstruct repeated full-compression measurements. They are excluded
from current scoring. After updating, apply the migration and rebenchmark baselines:

```bash
just db-migrate
just baseline-seed --corpus corpus-stage1 --corpus corpus-stage2
just weights-preview --out-dir "$PWD/data/benchmark-reports/current"
```

The incremental seeder detects the changed protocol and creates fresh runs; `--overwrite`
is unnecessary. Earlier runs, aggregations and score snapshots remain available.
The historical timing tables earlier in this README describe LZ77-only measurements.

`just weights-preview` automatically reapplies the current aggregation formula to
the runs linked to each submission's latest published aggregation. Formula changes
need no new benchmark or proof run for this preview. Historical verification is
labelled in the report and does not establish current live-payout eligibility.
Use repeated `--aggregation-id ID` to choose earlier evidence explicitly.

`just weights-preview` saves `scores.json` and four figures to
`data/benchmark-reports/current/` by default (overwriting the previous preview).
Use `--out-dir PATH` to choose another directory. The figures are:

- `pareto.png`: mean per-file time relative to the incumbent versus compression ratio,
  submission allocations (hatched
  portions burn), and a square normalized frontier. Normalization uses the frontier's
  time and size extremes, matching the global part of `local-global`; a constant axis
  maps to zero. Dominated points appear only in the original-coordinate panel.
- `pareto-uncertainty.png`: horizontal 95% bootstrap intervals for aggregate total
  compression time. These cover recorded repetition variability, not host drift.
- `compression-times.png`: total and LZ77 timing repeatability on fixed data, in seconds
  and as percentage deviations from each algorithm's median. Each observation sums
  the nth measured repetition across all selected files/corpora; warmups are excluded.
  Points, sample standard deviations and box plots show repetition variability. These
  are aligned file-local repetitions, not independently executed whole-corpus runs,
  and do not measure variability between separate benchmark invocations. Raw totals
  are exported as `timing_repetition_totals` in `scores.json`.
- `compression-vs-lz77.png`: one point per algorithm comparing aggregate total and
  LZ77 time (each a sum of per-file medians).

Algorithm colours are shared across all figures. Plots use the selected aggregations'
DB evidence and require no local JSONL files.


To compare experimental Pareto weights on synthetic frontiers, run:

```bash
.venv/bin/python scripts/pareto-weights.py
```

Reports are written to `data/spike/pareto/weights/`. `compare-*.png` compares all
methods on the same points; `COPY-AUDIT.md` measures the combined reward of a
point and its near-copies. Focused plots under `improvement-space-study/`
compare local-global with the incremental improvement-space factor. Use
`--method`, `--scenario` and `--out-dir` to narrow the experiment. The selected `local-global-improvement-space-log` method is now the live-scoring
default; the remaining experimental methods are comparison-only.

The spike also supports `improvement-space-log` and
`local-global-improvement-space-log`. They measure each adjacent improvement as
`log(worse / better)`, normalized by `log(worst / best)`, on both axes. Equal
proportional improvements receive equal credit; equal absolute improvements
receive more credit at lower values. Only the improvement factor changes in
the combined variant; its local-global coefficients retain their linear definition.

The default weight method is `local-global-improvement-space-log`. Set
`SCORING_METHOD` to select a different registered method explicitly.


Statistical speed admission runs after aggregation and before rewards. Use
`just admission-run` for newly published evidence or `just admission-replay --preview`
to inspect a changed context before explicit replay. `just admission-replay --historical`
backfills retained historically verified benchmarks without rerunning them; it does not
refresh live verification eligibility. `just baseline-seed` handles ordered baseline
admission automatically. `just weights-preview` writes gain-interval and per-file
admission plots alongside the Pareto report in `data/benchmark-reports/current/`.
See [statistical admission and replay](docs/SCORING.md#statistical-speed-admission).
