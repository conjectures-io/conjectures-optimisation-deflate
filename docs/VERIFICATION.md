# Submission verification

The validator runs **static prevalidation → Lean verification → benchmark**.
Each stage is independently callable. A local benchmark remains available without
verification or a database; importing measurements does not certify a submission.

## Commands

```sh
just preverify miner/examples/lazy/parse.rs
just verify-lean miner/examples/lazy/parse.rs miner/examples/lazy/Parse.lean
just preverify-db 123
just verify-lean-db 123
just bench miner/examples/lazy/parse.rs
just bench-db miner/examples/lazy/parse.rs
just bench-import data/benchmark-runs/example.jsonl
```

DB commands resolve the stored submission by ID and check its signed digest. The
Lean DB command requires successful static prevalidation of the same source,
proof and verifier fingerprint. A local Lean command cannot populate DB success.
The service reuses matching successful static/Lean verification for another
benchmark; it does not trust an imported report or miner-provided LLBC.

`just check DIR` runs the proof gate, while `just prove DIR` is an alias for the
independent Lean command. `just extract DIR` leaves the extracted model in its
printed private workspace for proof development. These commands no longer copy
submissions over files in the checkout.

The Python gate accepts `--stage static|lean|extract|full`, `--proof FILE`,
`--submission-id ID`, and `--keep auto|always|never`. Exit codes are 0 for success,
1 for rejected/unsupported input or a stage timeout, and 2 for validator errors.
Standalone stage commands keep their reports by default through the just recipes.
Without `--keep`, successful runs are removed and failed runs are retained.

## Workspaces and confinement

Every invocation snapshots its input bytes into a unique directory under
`data/verification-workspace/`. The directory contains LLBC, generated Lean,
private build outputs, command logs and a JSON report with input hashes and stage
outcomes. Only dependency caches and tool installations are shared read-only.

Charon, Aeneas and Lean run through the common bubblewrap runner with a minimal
filesystem and an explicit environment. Database credentials are not passed to
them. Submitted proof elaboration can write only its own module outputs; the
obligation is compiled separately with the proof and extracted modules read-only.
The final axiom query has no writable build outputs. Rust compiler failures stop
extraction immediately, and old LLBC is truncated before invoking Charon.

`VERIFY_TOOL_TIMEOUT` defaults to 900 seconds per compiler/translator/trusted-build
command. `VERIFY_LEAN_TIMEOUT` defaults to 900 seconds per proof/obligation/query
command. `VERIFY_LEAN_MEMORY_MB` defaults to 16384 and applies to all expensive
verification commands; 0 explicitly disables the cap. A requested cap requires a
working `systemd-run --user` connection: it is never silently omitted. See
[validator startup](STARTUP.md#systemd-user-limits) for the user-session check.
Timeouts terminate process groups.

`VERIFY_SANDBOX=off` is for local experimentation only; DB verification refuses it.

```sh
just verification-clean --days 7          # preview finished workspaces
just verification-clean --days 7 --apply  # remove those workspaces
just verification-clean --legacy         # preview exact retired output files
just verification-clean --legacy --apply # archive them (stop old-version workers first)
```

Cleanup uses advisory locks to skip active workspaces; it can reclaim an abandoned
workspace after its owning process dies. Unknown and symlinked directories are kept. Legacy files
under `validator/lean/Slot`, `validator/lean/Proof/Parse.lean`, `validator/lean/slot.llbc`
and `validator/.work/axioms.lean` are no longer gate outputs. The slot's generated
Rust remains a trusted template input for building the standalone slot crate.
Legacy cleanup moves only the listed files into `data/verification-workspace/legacy-*`,
preserving unpublished proofs. Archives are not removed by ordinary workspace cleanup;
review them before deleting them manually. Dependency caches, benchmark data and
unknown files are never legacy-cleanup targets.

## Static policy and supported Rust

A pinned `syn` parser checks Rust syntax before Charon. It handles nested comments,
raw strings/identifiers, nested attributes and imports structurally. Custom macros,
conditional compilation (`cfg`, `cfg_attr`, `cfg!`), foreign code, unsafe code,
external modules, statics and compiler/linker/extraction overrides are rejected.
Write the selected implementation directly and expand pure macros. `inline`,
`inline(always)`, `inline(never)`, `cold`, literal documentation and the harmless
`allow(dead_code)` / `allow(unused_variables)` attributes are supported.

The next check inspects the pinned Charon 0.1.245 LLBC. Every admitted local
function needs an inspectable body. External operations must appear in an explicit
reviewed list: scalar arithmetic/bit operations, slice length and indexing, and
Vec construction (including `with_capacity`), push, length, indexing and deref. Array indexing/repetition,
ordinary scalar/array/local-structure computations, and local generic traits
(including default methods and associated types) are supported. Charon extracts
all provided methods, even unused defaults; concrete method dictionaries and
referenced bodies are checked before generic calls are admitted.

Unknown statement/call forms, opaque local items, function-pointer/dynamic calls,
unreviewed external models and custom `Drop` implementations remain unsupported.
Custom destructors can change output even without I/O, and the pinned Aeneas
preset does not faithfully preserve those effects. Standard storage deallocation
and generic drops are admitted only within the closed type set, which excludes
custom destructors, foreign resource types and user allocators. Unsupported pure
code receives an explicit model/subset diagnostic, not an accusation of cheating.

The compatibility suite covers every shipped parser, heap-backed parsing, generic
traits, defaults and associated types. It does not establish equivalence with every
Rust program Aeneas can translate. For unsupported library conveniences, use
inspected local functions or indexed loops; inline known callbacks. These checks
place no new limits on search depth, match strategy, table sizes or compression
choices, but we cannot promise that rewriting every unsupported abstraction has
zero performance cost. Expanding the external model set requires model and
callback/drop review plus positive and adversarial regression tests.

Charon/Aeneas are trusted translators, not an I/O detector by themselves. In the
pinned Aeneas backend, `std::io::stdio::_print` is explicitly modeled as `.ok ()`:
extraction can erase a native printing effect. The resolved policy therefore
rejects it even if syntax checks are bypassed. Filesystem writes are separately
tested to fail Aeneas translation without either prefilter. All external-template
output filenames are checked, not just `FunsExternal_Template.lean`.

Source: [pinned Aeneas printing model](https://github.com/AeneasVerif/aeneas/blob/5b9dcf33dccdb1560ea7203ac57ea202476b6ed3/backends/lean/Aeneas/Std/Std/Io.lean).

The gate refuses `RUSTFLAGS`, `CARGO_ENCODED_RUSTFLAGS`, `RUSTUP_TOOLCHAIN` and
`CARGO_PROFILE_RELEASE_*` overrides that could change the pinned recipe.

The native parser and extraction use nightly-2026-08-18, Rust 2021, disabled debug
assertions and enabled overflow checks. Native optimization and the trusted C ABI
wrapper differ intentionally. User-controlled conditional compilation is forbidden.
Existing benchmark timings need to be measured again after this compiler change.

## Database and official scoring

Migration `0003` adds nullable source/proof hashes, verifier fingerprint, static
and Lean success timestamps, an attempt token and the trusted measured-source hash
on `submissions`. Existing rows remain unverified; benchmark data is preserved.
Apply with `just db-migrate`. A downgrade removes only the new verification fields.

A new verification attempt clears superseded success atomically. Lean-only retries
retain the required matching static success. Publishing checks the attempt token;
stale workers cannot publish over a newer attempt. Queue claims are checked as
well. Benchmark failure does not erase independently successful proof verification.

Current official scoring requires both milestones, the current verifier fingerprint
and a measured-source hash written by the trusted gate. Raw JSON imports cannot
set these fields. A separate scorer can set `VERIFY_REQUIRED_FINGERPRINT` to the
operator-published fingerprint (`just verification-fingerprint`), so it does not need a Lean installation. The default
computes the identity from the local pinned inputs and installed translator binaries.

This stores the latest verification state, not an audit history of every attempt.
The current scorer still consumes the existing submission summary columns. A future
raw-run aggregation worker must additionally authenticate its benchmark producer
and match each selected run's source hash to the verified submission; an imported
JSON source hash is not authentication. Building that aggregation service is separate
from this hardening change.
