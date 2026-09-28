# Miner guide

Submit two files: `parse.rs`, a Rust LZ77 parser, and `Parse.lean`, a proof that
its token stream decodes to the input. The [proof manual](../miner/MANUAL.md)
explains the contract, supported Rust subset, and proof techniques. The
[competition page](https://conjectures.io/competitions/deflate)
is the source for current rules and official metrics.

## Local workflow

From the repository root:

```bash
./setup.sh
source .venv/bin/activate
just corpus-pull
cp -r miner/template my-submission
just bench my-submission
VERIFY_CORPUS=corpus-stage1 just check my-submission
```

If setup installed `just` or Rust for the first time, ensure
`$HOME/.local/bin` and `$HOME/.cargo/bin` are on your shell's `PATH` before
running the commands above. In a container, set `VERIFY_SANDBOX=off` for local
proof checks because bubblewrap may be unable to create namespaces.

`just bench` measures locally without checking the proof. `just check` runs the
proof gate and benchmark. The standalone benchmark uses the public corpus by
default; validator runs also use the held-out corpus. The explicit
`VERIFY_CORPUS` override makes the local full-gate check use the public corpus.
Local speed depends on the
host and is an estimate of validator performance. Use `just corpora` to see the
configured corpora and `just --list` for more commands.

The template and `miner/examples/` show different parsing strategies. Their
results are examples, not current leaderboard measurements. For proof debugging,
use `just extract my-submission` to inspect the extracted Lean model and
`just probe my-submission LINE` to inspect a goal. See
[verification](VERIFICATION.md) for stage behavior and failure reports.

## Submit

The submission client requires the platform API origin and a Bittensor hotkey.
In a new shell, run `source .venv/bin/activate` first:

```bash
python miner/submit.py submit my-submission --hotkey <hotkey-file> --url <api-origin>
python miner/submit.py status <submission-id> --url <api-origin>
python miner/submit.py leaderboard --url <api-origin>
```

The client signs the submission. See `python miner/submit.py --help` and the
[proof manual](../miner/MANUAL.md) for requirements and failure diagnosis.
