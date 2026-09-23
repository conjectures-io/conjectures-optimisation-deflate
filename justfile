# conjectures-miniz-oxide-competition - one entry point for both sides; toolchain paths from validator/verifier/config.sh.

set dotenv-load := true

root   := justfile_directory()
val    := root / "validator"
python := root / ".venv/bin/python"

# Every Python file the linter and the type checker cover.
py_paths := val / "bench " + val / "verifier " + val / "sandbox " + val / "service " + val / "tests " + root / "deploy/migrate/alembic " + root / "miner/submit.py"
ruff_paths := py_paths + " " + val / "db " + val / "chain " + val / "scoring " + val / "workers " + val / "tools " + root / "scripts/pareto-weights.py"

# The benchmark and the gate are one Python package under validator/.
bench := python + " -m bench"
export PYTHONPATH := val

default:
    @just --list

# --- Setup ------------------------------------------------------------------

# From a fresh clone to a passing self-test: packages, just, .venv, .env, toolchain.
# Idempotent. ~15 min and ~9 GB on a bare machine, seconds once done.
setup *ARGS:
    {{root}}/setup.sh {{ARGS}}

# The toolchain part of setup alone: Lean, Aeneas, Charon, Mathlib, build, self-test.
init *ARGS:
    PYTHON={{python}} {{val}}/verifier/init.sh {{ARGS}}

# Report what is installed and what is missing. Installs nothing. Exit 1 if
# anything is missing, so it works as a precondition check in CI.
doctor:
    {{root}}/setup.sh --check

# Build the scoring corpus. Pass source roots to override the defaults.
corpus *ROOTS:
    {{python}} {{val}}/verifier/make-corpus.py {{ROOTS}}

# Fetch stage 1 and stage 2 corpora; accepts --stage 1 or --stage 2.
corpus-pull *ARGS:
    bash {{root}}/scripts/pull-corpus.sh {{ARGS}}

# Download the Silesia reference corpus into data/benchmark/. --subset|--full|both (default).
corpus-download *ARGS:
    {{root}}/scripts/download-silesia.sh {{ARGS}}

# Package the held-out stage 2 into one archive, so every validator scores the exact
# same bytes. The seed is NOT enough to distribute it: 38 of the 73 pool sources are
# floating URLs, so two validators rebuilding from the same seed at different times
# get different corpora and would rank submissions differently. Writes to
# data/benchmark/dist/ (gitignored). Put the result somewhere private -- this is the
# hidden set; publishing it ends its usefulness.
# Package the held-out stage 2 so every validator scores the same bytes.
corpus-package:
    #!/usr/bin/env bash
    set -euo pipefail
    d={{root}}/data/benchmark
    [ -d "$d/corpus-stage2" ] || { echo "no corpus-stage2/ -- run \`just corpus-build --stage 2\` first" >&2; exit 1; }
    n=$(find "$d/corpus-stage2" -maxdepth 1 -type f | wc -l)
    [ "$n" -gt 0 ] || { echo "corpus-stage2/ is empty" >&2; exit 1; }
    stamp=$(date -u +%Y%m%dT%H%M%SZ)
    fp=$(printf '%s' "${BENCHMARK_STAGE2_SEED:-}" | sha256sum | cut -c1-16)
    stage=$(mktemp -d); trap 'rm -rf "$stage"' EXIT
    cp -r "$d/corpus-stage2" "$stage/corpus-stage2"
    {
        echo "corpus-stage2 -- the held-out scoring corpus. Do not publish."
        echo
        echo "built    $stamp"
        echo "seed     sha256:$fp   (fingerprint only; the seed itself stays in .env)"
        echo "files    $n"
        echo "bytes    $(du -sb "$d/corpus-stage2" | cut -f1)"
        echo
        echo "Every validator must score against THESE bytes. Rebuilding from the seed"
        echo "is not equivalent: the source pool has floating upstreams and drifts."
        echo
        (cd "$stage/corpus-stage2" && sha256sum -- * | sort -k2)
    } > "$stage/MANIFEST.txt"
    mkdir -p "$d/dist"
    out="$d/dist/corpus-stage2-$stamp-$fp.tar.gz"
    tar -czf "$out" -C "$stage" MANIFEST.txt corpus-stage2
    (cd "$(dirname "$out")" && sha256sum "$(basename "$out")" > "$(basename "$out").sha256")
    echo "packaged $n files -> $out"
    echo "checksum $(cut -d' ' -f1 < "$out.sha256")"
    echo
    echo "Upload it somewhere private, then on each validator:"
    echo "  just corpus-install <url-or-path>"
    echo "  VERIFY_CORPUS=data/benchmark/corpus-stage2   # in .env"

# Install a packaged stage 2 from a path or URL.
corpus-install SRC FORCE="":
    #!/usr/bin/env bash
    set -euo pipefail
    d={{root}}/data/benchmark
    if [ -d "$d/corpus-stage2" ] && [ "{{FORCE}}" != "force" ]; then
        echo "$d/corpus-stage2 already exists. Pass 'force' as a second argument to replace it." >&2
        exit 1
    fi
    w=$(mktemp -d); trap 'rm -rf "$w"' EXIT
    case "{{SRC}}" in
        http*) curl -sSL --fail -o "$w/a.tar.gz" "{{SRC}}"
               curl -sSL --fail -o "$w/a.tar.gz.sha256" "{{SRC}}.sha256" ;;
        *)     cp "{{SRC}}" "$w/a.tar.gz"; cp "{{SRC}}.sha256" "$w/a.tar.gz.sha256" ;;
    esac
    want=$(cut -d' ' -f1 < "$w/a.tar.gz.sha256")
    got=$(sha256sum "$w/a.tar.gz" | cut -d' ' -f1)
    [ "$want" = "$got" ] || { echo "CHECKSUM MISMATCH: expected $want, got $got" >&2; exit 1; }
    tar -xzf "$w/a.tar.gz" -C "$w"
    [ -d "$w/corpus-stage2" ] || { echo "archive has no corpus-stage2/" >&2; exit 1; }
    (cd "$w/corpus-stage2" && sha256sum -c <(sed -n '/^[0-9a-f]\{64\}  /p' ../MANIFEST.txt) >/dev/null) \
        || { echo "a corpus file does not match the manifest" >&2; exit 1; }
    rm -rf "$d/corpus-stage2"
    mv "$w/corpus-stage2" "$d/corpus-stage2"
    sed -n '1,8p' "$w/MANIFEST.txt"
    echo
    echo "installed $(find "$d/corpus-stage2" -maxdepth 1 -type f | wc -l) files -> $d/corpus-stage2"
    echo "set VERIFY_CORPUS=data/benchmark/corpus-stage2 in .env"

# Check a downloaded source pool is complete and undrifted.
corpus-verify *ARGS:
    python3 {{root}}/scripts/verify-corpus.py {{ARGS}}

# --- Benchmark ---------------------------------------------------------------

# miner/template and every miner/examples/* against the incumbent, timed as the
# gate times, on the default corpus. External references: VERIFY_BENCH_BARS=1. Pass submission dirs to
# narrow it, or --corpus NAME to move it.
bench *ARGS: build
    {{bench}} {{ARGS}} --runs-dir {{root}}/data/benchmark-runs

# Score, floor verdicts, Pareto front, per-format tables and stability for a run (default: the latest).
bench-report *RUN:
    {{python}} -m bench.analyze {{RUN}}

# Two runs of the same code must agree on every byte and token; total compression time within 15%.
bench-compare A B:
    {{python}} -m bench.compare {{A}} {{B}}

# Benchmark locally and explicitly persist per-candidate evidence in Postgres.
bench-db *ARGS: build
    {{bench}} {{ARGS}} --runs-dir {{root}}/data/benchmark-runs --store-db

# Import/retry saved single-candidate JSONL artifacts without rerunning benchmarks.
bench-import +FILES:
    {{python}} -m bench.storage {{FILES}}

# Remove every retained run workspace under data/bench-workspace/.
bench-clean:
    {{bench}} --clean

# What the benchmark and the gate can be pointed at, and which is the default.
# Edit validator/corpora.toml to add one; set VERIFY_CORPUS to override the default
# for one run, by name or by directory.
corpora:
    {{bench}} --corpora


# Build the slot (Charon's extraction target) and the measurement engine.
# `init` does this; this is for after an edit.
build:
    cd {{val}}/slot && cargo build --release -q
    cd {{val}}/measure && cargo build --release -q

# --- Submissions ------------------------------------------------------------

# The full gate, then the score. This is what a validator runs.
#   just check miner/template
check DIR *ARGS:
    {{python}} {{val}}/verifier/verify.py {{root}}/{{DIR}} {{ARGS}}

# The proof gate alone -- intake, policy, extraction, statement, axioms.
check-proof DIR:
    {{python}} {{val}}/verifier/verify.py {{root}}/{{DIR}} --no-score

# Identity to configure on a separate scoring service.
verification-fingerprint:
    {{python}} -m verifier.identity

# Preview old completed workspaces; pass --apply to remove them.
verification-clean *ARGS:
    {{python}} {{val}}/verifier/cleanup.py {{ARGS}}

# Static syntax and resolved Rust checks; does not invoke Lean.
preverify RUST:
    {{python}} {{val}}/verifier/verify.py {{RUST}} --stage static --keep always

# Verify immutable stored submissions; DB access is checked before tools run.
preverify-db ID:
    {{python}} {{val}}/verifier/verify.py --submission-id {{ID}} --stage static --keep always

verify-lean-db ID:
    {{python}} {{val}}/verifier/verify.py --submission-id {{ID}} --stage lean --keep always

# Translation, statement and axiom checks; no DB required.
verify-lean RUST PROOF:
    {{python}} {{val}}/verifier/verify.py {{RUST}} --stage lean --proof {{PROOF}} --keep always

# Produce a private extracted model for proof development.
extract DIR:
    {{python}} {{val}}/verifier/verify.py {{DIR}}/parse.rs --stage extract --keep always

# The goals and hypotheses at LINE of DIR/Parse.lean, against the real extraction; --stop cuts there.
probe DIR LINE *ARGS:
    {{python}} {{val}}/verifier/probe.py {{absolute_path(DIR)}} {{LINE}} {{ARGS}}

# Check a proof in its own workspace.
prove DIR:
    {{python}} {{val}}/verifier/verify.py {{DIR}}/parse.rs --stage lean --proof {{DIR}}/Parse.lean --keep always

# --- The store --------------------------------------------------------------

# Start Postgres and wait for it to be healthy. Values come from .env.
db-up:
    #!/usr/bin/env bash
    set -euo pipefail
    docker compose up -d db
    printf 'waiting for postgres'
    for _ in $(seq 1 60); do
        if docker exec conjectures_miniz_db pg_isready -q -U "${POSTGRES_USER:-conjectures}" -d "${POSTGRES_DB:-conjectures}" 2>/dev/null; then
            printf ' ready\n'; exit 0
        fi
        printf '.'; sleep 1
    done
    printf ' timed out\n'
    docker compose logs --tail 40 db
    exit 1

# Stop Postgres, keeping its data.
db-down:
    docker compose down

# Apply every migration. Idempotent; safe to re-run.
db-migrate:
    cd deploy/migrate && {{python}} -m alembic upgrade head

# Reverse migrations to a revision; removes data introduced by those revisions.
db-downgrade REVISION:
    cd deploy/migrate && {{python}} -m alembic downgrade {{REVISION}}

# Drop the schema and rebuild it from the migrations. Destroys every submission.
db-reset:
    cd deploy/migrate && {{python}} -m alembic downgrade base
    cd deploy/migrate && {{python}} -m alembic upgrade head

# A psql shell on the validator's database.
db-psql:
    docker exec -it conjectures_miniz_db psql -U "${POSTGRES_USER:-conjectures}" -d "${POSTGRES_DB:-conjectures}"

# What the last weight vector paid, and why.
db-weights:
    #!/usr/bin/env bash
    docker exec -i conjectures_miniz_db psql -U "${POSTGRES_USER:-conjectures}" -d "${POSTGRES_DB:-conjectures}" <<'SQL'
    SELECT w.id, w.block, w.accepted, w.dry_run, w.summary, w.created_at
      FROM weight_sets w ORDER BY w.id DESC LIMIT 5;
    SELECT s.hotkey, s.on_frontier, round(s.pareto_weight::numeric, 5) AS pareto,
           round(s.improvement_weight::numeric, 5) AS improvement,
           round(s.combined_weight::numeric, 5) AS combined
      FROM score_snapshots s
     WHERE s.weight_set_id = (SELECT max(id) FROM weight_sets)
     ORDER BY s.combined_weight DESC;
    SQL

# One-time: move an old SQLite queue into Postgres. See the script's own --help.
db-import-sqlite DB="validator/.work/service.db" *ARGS="":
    {{python}} {{val}}/tools/import-sqlite.py {{DB}} {{ARGS}}

# --- Submission service -----------------------------------------------------
# Service commands accept --background (PM2 start) or --stop (PM2 stop).

# Serve the API. The gate runs beside it as its own process -- see `just service-worker`.
service *ARGS:
    {{python}} {{val}}/tools/service_start.py service {{ARGS}}

# Drain the submission queue through the gate. Run one per machine with a toolchain.
service-worker *ARGS:
    {{python}} {{val}}/tools/service_start.py service-worker {{ARGS}}

# --- The chain --------------------------------------------------------------

# Stream subnet registrations into the store. Without it nobody can submit.
chain-watcher *ARGS:
    {{python}} {{val}}/tools/service_start.py chain-watcher {{ARGS}}

# Score the round and set weights, once an epoch. WEIGHT_DRY_RUN=1 records without setting.
weight-setter *ARGS:
    {{python}} {{val}}/tools/service_start.py weight-setter {{ARGS}}

# What the scorer would pay right now: reads the store, touches neither chain nor wallet.
weights-preview *ARGS:
    cd {{val}} && {{python}} -m workers.report --out-dir "{{root}}/data/benchmark-reports/current" {{ARGS}}

# --- Operator ---------------------------------------------------------------

# Re-pin the contract, the engine and the gate. Run after any operator-side change.
repin:
    {{python}} {{val}}/verifier/pins.py --write

# Fail if PINS.json is stale. CI and setup run this; no submission does.
check-pins:
    {{python}} {{val}}/verifier/pins.py --check

# What a submission costs, in lines.
cost DIR:
    #!/usr/bin/env bash
    set -euo pipefail
    {{python}} - <<EOF
    from pathlib import Path
    def code(f):
        n, blk = 0, False
        for l in Path(f).read_text().split("\n"):
            t = l.strip()
            if not t: continue
            if blk:
                if "-/" in t or "*/" in t: blk = False
                continue
            if t.startswith("/-") or t.startswith("/*"):
                if "-/" not in t and "*/" not in t: blk = True
                continue
            if t.startswith("--") or t.startswith("//"): continue
            n += 1
        return n
    d = Path("{{root}}/{{DIR}}")
    v = Path("{{val}}")
    print(f"{'the slot, in Rust':34} {code(d/'parse.rs'):5} lines")
    print(f"{'the proof -- PER PATCH':34} {code(d/'Parse.lean'):5} lines")
    print()
    for label, f in [("contract: Spec.lean", "lean/Lz77/Spec.lean"),
                     ("contract: Lemmas.lean", "lean/Lz77/Lemmas.lean"),
                     ("contract: Interface.lean", "lean/Lz77/Interface.lean"),
                     ("the gate: Obligation.lean", "lean/Verify/Obligation.lean")]:
        print(f"{label + '  -- paid ONCE':34} {code(v/f):5} lines")
    EOF

# The negative tests: what each stage of the gate rejects, and the reference
# submissions it accepts. Stages 0-1 run anywhere; 3-5 skip without the toolchain.
test *ARGS:
    {{python}} -m pytest -q {{val}}/tests {{ARGS}}

# The same, minus tests marked `slow` (Lean/toolchain builds, the real gate end to
# end) -- for checking an unrelated change without paying for a Lean build.
test-fast *ARGS:
    {{python}} -m pytest -q {{val}}/tests -m "not slow" {{ARGS}}

# ruff format + check + basedpyright over every Python file. Rules live in pyproject.toml.
lint:
    {{python}} -m ruff format --check {{ruff_paths}}
    {{python}} -m ruff check {{ruff_paths}}
    {{python}} -m basedpyright {{py_paths}}

# Every reference submission, end to end. The repository's own smoke test.
smoke: build
    just check miner/template --results /tmp/smoke-template.json
    just check miner/examples/hash-chains --results /tmp/smoke-hash-chains.json
    just check miner/examples/lazy --results /tmp/smoke-lazy.json
    just check miner/examples/mo-lazy --results /tmp/smoke-mo-lazy.json
    just check miner/examples/optimal --results /tmp/smoke-optimal.json
    just check miner/examples/no-lz77 --results /tmp/smoke-no-lz77.json
    just check miner/examples/optimal-iter --results /tmp/smoke-optimal-iter.json

# Aggregate stored runs; --corpus NAME:SHA256, --source HASH or --submission-id ID.
bench-aggregate *ARGS:
    {{python}} -m bench.aggregate {{ARGS}}

# Incrementally verify and seed operator baselines; --overwrite forces new measurements.
baseline-seed *ARGS: build
    {{python}} -m bench.baselines {{ARGS}}

# Admit newly published benchmark aggregations; changed existing contexts remain pending.
admission-run *ARGS:
    cd {{val}} && {{python}} -m workers.admission {{ARGS}}

# Explicitly replay admission after evidence/policy/order changes; --preview is read-only.
admission-replay *ARGS:
    cd {{val}} && {{python}} -m workers.admission --replay {{ARGS}}
