"""Independent positive controls and adversarial tests of the trusted gate."""

from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

import pytest
from sqlalchemy import text
from test_gate import TEMPLATE, VALIDATOR, needs_toolchain

from db.verification import StaleAttempt
from sandbox import bwrap
from verifier import resolved, verify
from verifier.cleanup import LEGACY, archive_legacy, cleanup
from verifier.identity import fingerprint
from verifier.workspace import Workspace


@pytest.mark.parametrize(
    "source",
    [
        'pub fn parse() { std::fs::write("x", "y"); }',
        'pub fn parse() { std :: r#fs :: write("x", "y"); }',
        "#[cfg(not(debug_assertions))] pub fn hidden() {}",
        "pub fn parse() { #[cfg_attr(debug_assertions, inline)] fn f() {} }",
        'macro_rules! hidden { () => { std::fs::write("x", "y") } }',
        'pub fn parse() { println!("forged result"); }',
        'pub fn parse() { let _ = include_str!("secret"); }',
        '#[path="other.rs"] mod hidden;',
        '#[export_name="parse"] pub fn hidden() {}',
    ],
)
def test_syntax_rejects_hidden_or_direct_capabilities(source):
    assert verify.scan_rust(source)


def test_syntax_does_not_scan_strings_or_nested_comments():
    assert (
        verify.scan_rust(
            (
                "/* outer /* unsafe */ still a comment */\n#[inline(always)] pub "
                'fn helper() -> &\'static str { r#"std::fs::write cfg! unsafe"# }\n'
            )
        )
        == []
    )


@pytest.mark.parametrize("path", sorted((VALIDATOR.parent / "miner").glob("**/parse.rs")))
def test_every_shipped_parser_passes_syntax(path):
    assert verify.scan_rust(path.read_text()) == []


def compile_source(tmp_path, source):
    out = tmp_path / "output"
    out.mkdir(exist_ok=True)
    path = tmp_path / "parse.rs"
    path.write_text(source)
    result = subprocess.run(
        [str(VALIDATOR / "verifier/extract.sh"), str(path), str(out), "compile"],
        capture_output=True,
        text=True,
        timeout=90,
    )
    return result, out / "slot.llbc"


GOOD = (
    "pub fn parse(input: &[u8], out: &mut [u32]) -> usize { let mut "
    "i=0; while i<input.len() {out[i]=input[i] as u32; i+=1;} i }"
)


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize(
    "body",
    [
        'let _ = std::fs::write("/tmp/submission-must-not-execute", input);',
        'use std::fs::{write as alias}; let _ = alias("/tmp/submission-must-not-execute", input);',
        'fn helper() { let _ = std::fs::read("secret"); } helper();',
        "std::process::exit(1);",
        'let _ = std::env::var("SECRET");',
        'let _ = std::net::TcpStream::connect("127.0.0.1:1");',
        "std::thread::yield_now();",
        "let _ = std::time::SystemTime::now();",
        "std::io::Write::write_all(&mut std::io::stdout(), input).ok();",
        "let f: fn(&'static str) -> _ = std::fs::read::<&'static str>; let _ = f(\"secret\");",
    ],
)
def test_resolved_layer_rejects_without_syntax_filter(tmp_path, body):
    positive, path = compile_source(tmp_path, GOOD)
    assert positive.returncode == 0, positive.stdout + positive.stderr
    assert resolved.check(path) == ["core::slice::{impl}::len"]
    result, path = compile_source(
        tmp_path, "pub fn parse(input: &[u8], _out: &mut [u32]) -> usize {" + body + " 0 }"
    )
    # A compile/toolchain failure is not evidence that the effect check works.
    assert result.returncode == 0, result.stdout + result.stderr
    with pytest.raises(resolved.Unsupported):
        resolved.check(path)


@needs_toolchain
@pytest.mark.slow
def test_charon_failure_cannot_reuse_previous_output(tmp_path):
    first, path = compile_source(tmp_path, GOOD)
    assert first.returncode == 0 and path.stat().st_size > 0
    second, path = compile_source(tmp_path, "invalid Rust !!!")
    assert second.returncode != 0
    assert path.stat().st_size == 0


@needs_toolchain
@pytest.mark.slow
def test_real_aeneas_rejects_io_without_either_prefilter(tmp_path):
    result, path = compile_source(tmp_path, (VALIDATOR / "tests/parsers/syscalls.rs").read_text())
    assert result.returncode == 0, result.stdout + result.stderr
    result = subprocess.run(
        [
            str(VALIDATOR / "verifier/extract.sh"),
            str(tmp_path / "parse.rs"),
            str(path.parent),
            "translate",
        ],
        capture_output=True,
        text=True,
        timeout=90,
    )
    assert result.returncode == 1
    assert "REJECTED: the submission reaches outside" in result.stderr


@needs_toolchain
@pytest.mark.slow
def test_concurrent_static_stages_leave_checkout_unchanged(tmp_path):
    paths = [
        p
        for folder in ("lean", "slot/generated")
        for p in (VALIDATOR / folder).rglob("*")
        if p.is_file() and ".lake" not in p.parts and ".extract" not in p.parts
    ]
    before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

    def run(_):
        return subprocess.run(
            [
                sys.executable,
                str(VALIDATOR / "verifier/verify.py"),
                str(TEMPLATE / "parse.rs"),
                "--stage",
                "static",
                "--keep",
                "never",
            ],
            env=dict(os.environ, VERIFY_LEAN_MEMORY_MB="0"),
            capture_output=True,
            text=True,
            timeout=90,
        )

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(run, range(2)))
    assert all(r.returncode == 0 for r in results), [r.stdout + r.stderr for r in results]
    assert (
        results[0].stdout.split("workspace: ")[1].splitlines()[0]
        != results[1].stdout.split("workspace: ")[1].splitlines()[0]
    )
    assert before == {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def test_retention_and_cleanup_do_not_follow_symlinks(tmp_path):
    root = tmp_path / "workspaces"
    workspace = Workspace(VALIDATOR, root)
    assert cleanup(root, 0, apply=True) == []
    workspace.finish(1, "auto")
    outside = tmp_path / "outside"
    outside.mkdir()
    (outside / "evidence").write_text("keep")
    (workspace.path / "link").symlink_to(outside, target_is_directory=True)
    (root / "verify-symlink").symlink_to(outside, target_is_directory=True)
    assert cleanup(root, 0, apply=True) == [workspace.path]
    assert (outside / "evidence").read_text() == "keep"
    workspace = Workspace(VALIDATOR, root)
    workspace.finish(0, "auto")
    assert not workspace.path.exists()


def test_timeout_kills_descendants(tmp_path):
    marker = tmp_path / "escaped"
    result = bwrap.run(
        bwrap.Sandbox(enabled=False),
        [
            sys.executable,
            "-c",
            (
                "import subprocess,time; subprocess.Popen(['sh','-c', 'sleep 1; "
                "echo bad > '+__import__('sys').argv[1]]); time.sleep(30)"
            ),
            str(marker),
        ],
        cwd=tmp_path,
        timeout=0.1,
    )
    assert result.returncode == 124
    import time

    time.sleep(1.2)
    assert not marker.exists()


def test_requested_memory_requires_systemd(monkeypatch):
    def missing(_name: str) -> None:
        return None

    monkeypatch.setattr(shutil, "which", missing)
    with pytest.raises(bwrap.Unavailable, match="systemd-run"):
        bwrap.check_resources(bwrap.Sandbox(memory_mb=512))


def submission(store):
    source, proof = b"source", b"proof"
    sid, _ = store.submissions.add("test", hashlib.sha256(source + proof).hexdigest())
    return sid, source, proof


def test_milestones_cache_and_stale_attempts(store):
    sid, source, proof = submission(store)
    token, cached = store.verification.begin(sid, source, proof, "a" * 64)
    assert not cached
    with pytest.raises(ValueError, match="static"):
        store.verification.publish(sid, token, "lean")
    store.verification.publish(sid, token, "static")
    store.verification.publish(sid, token, "lean")
    new, cached = store.verification.begin(sid, source, proof, "a" * 64, reuse=True)
    assert cached
    with pytest.raises(StaleAttempt):
        store.verification.publish(sid, token, "measured")
    store.verification.publish(sid, new, "measured")
    new, cached = store.verification.begin(sid, source, proof, "b" * 64, reuse=True)
    assert cached
    assert store.submissions.get(sid).static_verified_at is not None
    assert store.submissions.get(sid).lean_verified_at is not None


def test_full_verification_writes_both_milestones_only_when_complete(store):
    sid, source, proof = submission(store)
    token, cached = store.verification.begin(sid, source, proof, "a" * 64)
    assert not cached
    before = store.submissions.get(sid)
    assert before.static_verified_at is None and before.lean_verified_at is None
    assert before.verifier_fingerprint is None
    store.verification.publish(sid, token, "full", "a" * 64)
    after = store.submissions.get(sid)
    assert after.static_verified_at == after.lean_verified_at
    assert after.verifier_fingerprint == "a" * 64
    _, cached = store.verification.begin(sid, source, proof, "b" * 64, reuse=True)
    assert cached


def test_wrong_source_and_missing_predecessor_are_refused(store):
    sid, source, proof = submission(store)
    with pytest.raises(ValueError, match="digest"):
        store.verification.begin(sid, b"replacement", proof, "a" * 64)
    with pytest.raises(ValueError, match="static"):
        store.verification.begin(sid, source, proof, "a" * 64, lean_only=True)


def test_scoring_requires_both_current_verification_and_trusted_measurement(store):
    sid, source, proof = submission(store)
    with store.engine.begin() as conn:
        conn.execute(
            text(
                "UPDATE submissions SET state='accepted', bytes=10, raw_bytes=100, "
                "parse_seconds=1, compression_seconds=1, incumbent_bytes=15, "
                "incumbent_seconds=1 WHERE id=:id"
            ),
            {"id": sid},
        )
    assert store.scoring.best_per_hotkey() == []
    token, _ = store.verification.begin(sid, source, proof, fingerprint())
    store.verification.publish(sid, token, "static")
    assert store.scoring.best_per_hotkey() == []
    store.verification.publish(sid, token, "lean")
    assert store.scoring.best_per_hotkey() == []
    store.verification.publish(sid, token, "measured")
    assert [s.submission_id for s in store.scoring.best_per_hotkey()] == [sid]
    store.verification.begin(sid, source, proof, "b" * 64)
    assert [s.submission_id for s in store.scoring.best_per_hotkey()] == [sid]


@needs_toolchain
@pytest.mark.slow
def test_printing_is_rejected_even_though_aeneas_models_it_as_noop(tmp_path):
    source = 'pub fn parse(_input: &[u8], _out: &mut [u32]) -> usize { println!("forged"); 0 }'
    assert verify.scan_rust(source)
    result, path = compile_source(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "_print" in path.read_text()
    with pytest.raises(resolved.Unsupported):
        resolved.check(path)
    # The policy must not rely on all native effects lacking a Lean model.
    model = VALIDATOR / ".work/aeneas/backends/lean/Aeneas/Std/Std/Io.lean"
    assert "def std.io.stdio._print" in model.read_text()
    assert ":= .ok ()" in model.read_text()


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize(
    "body",
    [
        (
            "struct X; impl Drop for X { fn drop(&mut self) { let _ = "
            'std::fs::read("secret"); } } let _x = X;'
        ),
        (
            "use std::ops::Drop as D; struct X; impl D for X { fn drop(&mut "
            "self) { std::thread::yield_now(); } } let _x = X;"
        ),
        (
            "trait T { fn f(&self); } struct X; impl T for X { fn f(&self) { "
            "std::process::exit(1); } } X.f();"
        ),
        'let f = || { let _ = std::env::var("SECRET"); }; f();',
        'fn unused() { let _ = std::fs::read("secret"); }',
    ],
)
def test_implicit_and_unused_effects_are_not_admitted(tmp_path, body):
    result, path = compile_source(
        tmp_path, "pub fn parse(_input: &[u8], _out: &mut [u32]) -> usize {" + body + " 0 }"
    )
    assert result.returncode == 0, result.stdout + result.stderr
    with pytest.raises(resolved.Unsupported):
        resolved.check(path)


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize("path", sorted((VALIDATOR.parent / "miner").glob("**/parse.rs")))
def test_all_shipped_parsers_pass_resolved_checks(tmp_path, path):
    result, ir = compile_source(tmp_path, path.read_text())
    assert result.returncode == 0, result.stdout + result.stderr
    resolved.check(ir)


def test_stale_queue_worker_cannot_start_a_new_verification(store, clock):
    sid, source, proof = submission(store)
    first = store.submissions.claim_next("first")
    clock["tick"](100)
    store.submissions.requeue_stale(10)
    second = store.submissions.claim_next("second")
    assert first is not None and second is not None
    with pytest.raises(StaleAttempt):
        store.verification.begin(sid, source, proof, "a" * 64, expected_claim=first.claimed_at)


def test_new_identity_keeps_completed_measurement(store):
    sid, source, proof = submission(store)
    token, _ = store.verification.begin(sid, source, proof, "a" * 64)
    for stage in ("static", "lean", "measured"):
        store.verification.publish(sid, token, stage)
    store.verification.begin(sid, source, proof, "b" * 64)
    assert store.submissions.get(sid).measured_source_sha256 is not None


@pytest.mark.parametrize(
    "output,target",
    [
        ("Proof", "Slot/Funs.olean"),
        ("Proof", "Verify/Obligation.olean"),
        ("Verify", "Proof/Parse.olean"),
        ("", "Verify/Obligation.olean"),
    ],
)
def test_proof_stages_cannot_replace_other_modules(tmp_path, monkeypatch, output, target):
    workspace = Workspace(VALIDATOR, tmp_path)
    monkeypatch.setattr(verify, "work_root", workspace.path)
    monkeypatch.setattr(verify, "lean_root", workspace.path / "lean")
    monkeypatch.setattr(verify, "LEAN_MEMORY_MB", 0)
    protected = workspace.path / "lean/.lake/build/lib/lean" / target
    protected.parent.mkdir(parents=True, exist_ok=True)
    protected.write_text("trusted")
    result = bwrap.run(
        verify.sandbox_spec(output=output),
        ["sh", "-c", 'echo forged > "$1"', "test", str(protected)],
        cwd=workspace.path,
        timeout=10,
        env=verify.tool_environment(),
    )
    assert result.returncode != 0
    assert protected.read_text() == "trusted"
    workspace.finish(0, "never")


def test_failed_static_stage_does_not_invoke_lean(tmp_path):
    inputs = tmp_path / "submission"
    inputs.mkdir()
    (inputs / "parse.rs").write_bytes((VALIDATOR / "tests/parsers/syscalls.rs").read_bytes())
    (inputs / "Parse.lean").write_bytes((TEMPLATE / "Parse.lean").read_bytes())
    result = subprocess.run(
        [
            sys.executable,
            str(VALIDATOR / "verifier/verify.py"),
            str(inputs),
            "--no-score",
            "--keep",
            "always",
        ],
        env=dict(os.environ, VERIFY_LEAN_MEMORY_MB="0"),
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 1 and "1 (policy)" in result.stdout
    from pathlib import Path

    workspace = Path(result.stdout.split("workspace: ")[1].splitlines()[0])
    assert not list((workspace / "logs").iterdir())
    assert not list(workspace.rglob("*.olean"))
    import json

    report = json.loads((workspace / "report.json").read_text())
    assert report["stages"][-1]["status"] == "rejected"
    cleanup(workspace.parent, 0, apply=False)  # Preview must not remove evidence.
    assert workspace.exists()


def test_cleanup_can_reclaim_an_abandoned_lock(tmp_path):
    workspace = Workspace(VALIDATOR, tmp_path)
    workspace.lock.close()  # Simulate the OS closing descriptors after a worker dies.
    assert cleanup(tmp_path, 0, apply=True) == [workspace.path]


@needs_toolchain
@pytest.mark.slow
def test_db_commands_verify_once_then_benchmark_twice(store, database_url, tmp_path):
    source = (TEMPLATE / "parse.rs").read_bytes()
    proof = (TEMPLATE / "Parse.lean").read_bytes()
    sid, _ = store.submissions.add("local-test", hashlib.sha256(source + proof).hexdigest())
    directory = tmp_path / "submissions" / str(sid)
    directory.mkdir(parents=True)
    (directory / "parse.rs").write_bytes(source)
    (directory / "Parse.lean").write_bytes(proof)
    corpus = tmp_path / "corpus"
    corpus.mkdir()
    (corpus / "input").write_bytes(bytes(range(256)) * 512)
    env = dict(
        os.environ,
        DATABASE_URL=database_url,
        SERVICE_FILES=str(directory.parent),
        VERIFY_CORPUS=str(corpus),
        VERIFY_LEAN_MEMORY_MB="0",
        VERIFY_BENCH_MEMORY_MB="0",
        VERIFY_BENCH_BUILD_MEMORY_MB="0",
        VERIFY_BENCH_REPS="3",
        VERIFY_BENCH_WARMUP="1",
    )
    command = [
        sys.executable,
        str(VALIDATOR / "verifier/verify.py"),
        "--submission-id",
        str(sid),
        "--keep",
        "never",
    ]

    def stage(name):
        return subprocess.run(
            command + ["--stage", name], env=env, capture_output=True, text=True, timeout=600
        )

    premature = stage("lean")
    assert premature.returncode == 2 and "static prevalidation" in premature.stdout
    static = stage("static")
    assert static.returncode == 0, static.stdout + static.stderr
    assert store.submissions.get(sid).lean_verified_at is None
    lean = stage("lean")
    assert lean.returncode == 0, lean.stdout + lean.stderr
    verified_at = store.submissions.get(sid).lean_verified_at
    assert verified_at is not None
    for index in range(2):
        # Corpus identity is deliberately not part of the Rust/proof cache key.
        selected = tmp_path / f"corpus-{index}"
        selected.mkdir()
        (selected / "input").write_bytes(bytes(range(256)) * (512 + index))
        env["VERIFY_CORPUS"] = str(selected)
        result = stage("full")
        assert result.returncode == 0, result.stdout + result.stderr
        assert "reusing matching static and Lean verification" in result.stdout
        row = store.submissions.get(sid)
        assert row.lean_verified_at == verified_at
        assert row.measured_source_sha256 == hashlib.sha256(source).hexdigest()


def test_changed_snapshot_is_rejected_before_native_compilation(tmp_path, monkeypatch):
    workspace = Workspace(VALIDATOR, tmp_path / "work")
    source = "slot/generated/parse.rs"
    workspace.snapshot("parse.rs", b"original", source)
    path = workspace.path / source
    path.chmod(0o644)
    path.write_bytes(b"replacement")
    monkeypatch.setattr(verify, "work_root", workspace.path)
    monkeypatch.setattr(verify, "active_workspace", workspace)
    corpus = tmp_path / "corpus"
    corpus.mkdir()
    (corpus / "input").write_text("data")
    monkeypatch.setenv("VERIFY_CORPUS", str(corpus))
    with pytest.raises(SystemExit) as exc:
        verify.stage_score(None)
    assert exc.value.code == 1
    assert workspace.events[-1]["detail"] == "source changed after intake"
    workspace.finish(1, "never")


def test_claim_tokens_prevent_stale_writes_even_when_timestamps_match(store):
    from db import SubmissionState

    sid, source, proof = submission(store)
    first = store.submissions.claim_next("first")
    store.submissions.requeue(sid)
    second = store.submissions.claim_next("second")
    assert first is not None and second is not None
    assert first.claimed_at == second.claimed_at  # The test clock is deliberately frozen.
    assert first.verification_attempt != second.verification_attempt
    with pytest.raises(StaleAttempt):
        store.verification.begin(
            sid,
            source,
            proof,
            "a" * 64,
            expected_claim=first.claimed_at,
            expected_attempt=first.verification_attempt,
        )
    with pytest.raises(RuntimeError, match="stale"):
        store.submissions.finish(
            sid,
            SubmissionState.ACCEPTED,
            expected_claim=first.claimed_at,
            expected_attempt=first.verification_attempt,
        )
    store.submissions.requeue(
        sid, expected_claim=first.claimed_at, expected_attempt=first.verification_attempt
    )
    assert store.submissions.get(sid).state == "verifying"


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize(
    "mutation", ["truncated", "version", "errors", "opaque", "unknown", "partial_methods"]
)
def test_malformed_or_unreviewed_ir_fails_closed(tmp_path, mutation):
    import json

    result, path = compile_source(tmp_path, GOOD)
    assert result.returncode == 0, result.stdout + result.stderr
    resolved.check(path)
    data = json.loads(path.read_text())
    if mutation == "truncated":
        path.write_text('{"charon_version":')
    else:
        if mutation == "version":
            data["charon_version"] = "new-unreviewed-version"
        elif mutation == "errors":
            data["has_errors"] = True
        elif mutation == "partial_methods":
            data["translated"]["options"]["translate_all_methods"] = False
        elif mutation == "opaque":
            data["translated"]["fun_decls"][0]["body"] = "Opaque"
        else:
            data["translated"]["fun_decls"][0]["body"]["Structured"]["body"]["statements"][0][
                "kind"
            ] = "NewEffect"
        path.write_text(json.dumps(data))
    with pytest.raises(resolved.Unsupported):
        resolved.check(path)


@needs_toolchain
@pytest.mark.slow
def test_static_db_command_is_independent_of_lean_source_policy(store, database_url, tmp_path):
    source = GOOD.encode()
    proof = b'#eval IO.println "this proof must be rejected"'
    sid, _ = store.submissions.add("local-test", hashlib.sha256(source + proof).hexdigest())
    directory = tmp_path / "submissions" / str(sid)
    directory.mkdir(parents=True)
    (directory / "parse.rs").write_bytes(source)
    (directory / "Parse.lean").write_bytes(proof)
    env = dict(
        os.environ,
        DATABASE_URL=database_url,
        SERVICE_FILES=str(directory.parent),
        VERIFY_LEAN_MEMORY_MB="0",
    )
    command = [
        sys.executable,
        str(VALIDATOR / "verifier/verify.py"),
        "--submission-id",
        str(sid),
        "--keep",
        "never",
        "--stage",
    ]
    static = subprocess.run(
        command + ["static"], env=env, capture_output=True, text=True, timeout=60
    )
    assert static.returncode == 0, static.stdout + static.stderr
    assert store.submissions.get(sid).static_verified_at is not None
    lean = subprocess.run(command + ["lean"], env=env, capture_output=True, text=True, timeout=60)
    assert lean.returncode == 1 and "Parse.lean" in lean.stdout
    assert store.submissions.get(sid).lean_verified_at is None


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize("mutable", [False, True])
def test_reviewed_heap_storage_is_supported(tmp_path, mutable):
    mutation = "v[i] = v[i].wrapping_add(0);" if mutable else ""
    source = (
        "pub fn parse(input: &[u8], out: &mut [u32]) -> usize { "
        "let mut v = Vec::with_capacity(input.len()); let mut i=0; "
        "while i<input.len() { v.push(input[i]); i+=1; } i=0; "
        "while i<input.len() { " + mutation + "out[i]=v[i] as u32; i+=1; } i }"
    )
    assert verify.scan_rust(source) == []
    result, path = compile_source(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "alloc::vec::{impl}::push" in resolved.check(path)
    translated = subprocess.run(
        [
            str(VALIDATOR / "verifier/extract.sh"),
            str(tmp_path / "parse.rs"),
            str(path.parent),
            "translate",
        ],
        capture_output=True,
        text=True,
        timeout=90,
    )
    assert translated.returncode == 0, translated.stdout + translated.stderr
    assert "alloc.vec.Vec.push" in (path.parent / "Slot/Funs.lean").read_text()


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize(
    "effect",
    [
        'let _ = std::fs::write("/tmp/must-not-execute", "data");',
        "*self.out = 999;",  # Pure mutation on drop is also erased by this Aeneas preset.
    ],
)
def test_vec_does_not_hide_custom_drop_behavior(tmp_path, effect):
    source = (
        "struct D<'a> { out: &'a mut u32 } "
        "impl Drop for D<'_> { fn drop(&mut self) { " + effect + " } } "
        "pub fn parse(_input: &[u8], out: &mut [u32]) -> usize { "
        "let mut v = Vec::new(); v.push(D { out: &mut out[0] }); 0 }"
    )
    result, path = compile_source(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    with pytest.raises(resolved.Unsupported):
        resolved.check(path)


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize(
    "declarations",
    [
        "trait Mix { fn mix(self)->u8; } impl Mix for u8 { fn mix(self)->u8 {self} }",
        "trait Mix: Sized { fn mix(self)->u8 { 7 } fn unused(&self)->u8 { 9 } } impl Mix for u8 {}",
        "trait Base { fn base(&self)->u8; } trait Mix: Base { fn mix(&self)->u8 { self.base() } } "
        "impl Base for u8 { fn base(&self)->u8 {*self} } impl Mix for u8 {}",
        "trait Mix: Sized { type Value; fn mix(self)->Self::Value; } "
        "impl Mix for u8 { type Value=u8; fn mix(self)->u8 {self} }",
    ],
)
def test_pure_generic_traits_translate(tmp_path, declarations):
    bound = "Mix<Value=u8>" if "type Value" in declarations else "Mix"
    source = (
        declarations
        + f"fn helper<T:{bound}>(x:T)->u8 {{x.mix()}}"
        + GOOD.replace("input[i] as u32", "helper(input[i]) as u32")
    )
    assert verify.scan_rust(source) == []
    result, path = compile_source(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    resolved.check(path)
    result = subprocess.run(
        [
            str(VALIDATOR / "verifier/extract.sh"),
            str(tmp_path / "parse.rs"),
            str(path.parent),
            "translate",
        ],
        capture_output=True,
        text=True,
        timeout=90,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert (path.parent / "Slot/Funs.lean").is_file()


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize(
    "declarations",
    [
        "trait Mix: Sized { fn mix(self)->u8 { std::process::exit(1) } } impl Mix for u8 {}",
        "trait Mix: Sized { fn mix(self)->u8 { 0 } "
        'fn unused(&self) { println!("forged"); } } impl Mix for u8 {}',
        "trait Mix { fn mix(self)->u8; } impl Mix for u8 { fn mix(self)->u8 { "
        'use std::fs::read as r; let _ = r("secret"); self } }',
    ],
)
def test_trait_methods_cannot_hide_effects(tmp_path, declarations):
    source = (
        declarations
        + "fn helper<T:Mix>(x:T)->u8 {x.mix()}"
        + GOOD.replace("input[i] as u32", "helper(input[i]) as u32")
    )
    result, path = compile_source(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    # Exercise the resolved boundary, with the syntax filter deliberately bypassed.
    with pytest.raises(
        resolved.Unsupported,
        match="unapproved external operation/model|unreviewed trait/destructor: core::",
    ):
        resolved.check(path)


def test_legacy_cleanup_preserves_templates_and_archives_proof(tmp_path):
    for relative in LEGACY:
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(relative)
    template = tmp_path / "validator/slot/generated/parse.rs"
    template.parent.mkdir(parents=True)
    template.write_text("required template")
    assert len(archive_legacy(tmp_path)) == len(LEGACY)
    assert all((tmp_path / relative).is_file() for relative in LEGACY)
    archive_legacy(tmp_path, apply=True)
    assert template.read_text() == "required template"
    archives = list((tmp_path / "data/verification-workspace").glob("legacy-*"))
    assert len(archives) == 1
    for relative in LEGACY:
        assert not (tmp_path / relative).exists()
        assert (archives[0] / relative).read_text() == relative
    assert cleanup(tmp_path / "data/verification-workspace", 0, apply=True) == []


def test_legacy_cleanup_does_not_follow_parent_symlinks(tmp_path):
    outside = tmp_path / "outside"
    outside.mkdir()
    (outside / "slot.llbc").write_text("preserve")
    (tmp_path / "validator").mkdir()
    (tmp_path / "validator/lean").symlink_to(outside, target_is_directory=True)
    assert archive_legacy(tmp_path, apply=True) == []
    assert (outside / "slot.llbc").read_text() == "preserve"


@needs_toolchain
@pytest.mark.slow
@pytest.mark.parametrize(
    "mutation", ["missing_body", "missing_default", "missing_impl", "unknown_dictionary"]
)
def test_generic_dispatch_requires_complete_inspected_targets(tmp_path, mutation):
    import json

    source = (
        "trait Mix: Sized { fn mix(self)->u8 { 1 } } impl Mix for u8 {} "
        "fn helper<T:Mix>(x:T)->u8 {x.mix()} "
        + GOOD.replace("input[i] as u32", "helper(input[i]) as u32")
    )
    result, path = compile_source(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    resolved.check(path)
    data = json.loads(path.read_text())
    crate = data["translated"]
    trait = next(t for t in crate["trait_decls"] if t and t["item_meta"]["is_local"])
    default = trait["methods"][0]["skip_binder"]["default"]
    if mutation == "missing_body":
        function = next(f for f in crate["fun_decls"] if f and f["def_id"] == default["id"])
        function["body"] = "Opaque"
    elif mutation == "missing_default":
        default["id"] = 999999
    elif mutation == "missing_impl":
        crate["trait_impls"][0]["methods"] = []
    else:

        def mutate(value):
            if isinstance(value, list):
                for child in value:
                    mutate(child)
            elif isinstance(value, dict):
                if "trait_decl_ref" in value and "Clause" in value["kind"]:
                    value["kind"] = {"UnknownDispatch": 0}
                for child in value.values():
                    mutate(child)

        mutate(crate)
    path.write_text(json.dumps(data))
    with pytest.raises(resolved.Unsupported):
        resolved.check(path)
