"""Negative tests for the gate - each stage, and the attack it stops.

    pytest validator/tests            # stages 0-1 run anywhere, in seconds
    just test-fast                    # the same, skipping slow tests even if the toolchain is there
    just test                         # everything, including stages 3-5 if `just doctor` passes

Every test runs `verify.py` against a throwaway copy of `validator/`, so the real
tree is never touched. Stages 3-5 need Charon, Aeneas and Lean; those tests skip
themselves when `init.sh --check` says the toolchain is absent, and are marked
`slow` so an unrelated change doesn't have to pay for a Lean build to check.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import cast

import pytest

VALIDATOR = Path(__file__).resolve().parent.parent
REPO = VALIDATOR.parent
TEMPLATE = REPO / "miner/template"
HASH_CHAINS = REPO / "miner/examples/hash-chains"
LAZY = REPO / "miner/examples/lazy"
OPTIMAL = REPO / "miner/examples/optimal"
MO_LAZY = REPO / "miner/examples/mo-lazy"

sys.path.insert(0, str(VALIDATOR / "verifier"))
import verify  # noqa: E402 - the verifier is a script, not a package

#: Not copied into the throwaway tree, but symlinked back so a build can reuse them.
SHARED = [".work", "lean/.lake", "slot/target", "measure/target"]

FORGED_REPORT = "'accepted' depends on axioms: [propext, Classical.choice, Quot.sound]"


def toolchain_present() -> bool:
    # `init.sh --check` installs nothing and exits 0 only when everything is there.
    r = subprocess.run([str(VALIDATOR / "verifier/init.sh"), "--check"], capture_output=True)
    return r.returncode == 0


needs_toolchain = pytest.mark.skipif(
    not toolchain_present(), reason="Charon, Aeneas or Lean missing - run `just init`"
)


@pytest.fixture
def tree(tmp_path: Path) -> Path:
    # A private copy of validator/ to verify against, sharing only the heavy build outputs.
    dst = tmp_path / "validator"
    shutil.copytree(
        VALIDATOR,
        dst,
        symlinks=True,
        ignore=shutil.ignore_patterns(".work", ".lake", "target", "tests", "__pycache__"),
    )
    for rel in SHARED:
        src = VALIDATOR / rel
        if src.exists():
            (dst / rel).parent.mkdir(parents=True, exist_ok=True)
            (dst / rel).symlink_to(src, target_is_directory=True)
    return dst


@pytest.fixture
def submission(tmp_path: Path) -> Path:
    # A copy of the template to mutate; it passes the whole gate unmodified.
    dst = tmp_path / "submission"
    shutil.copytree(TEMPLATE, dst)
    return dst


def check(tree: Path, submission: Path) -> subprocess.CompletedProcess[str]:
    # The proof gate on `submission`, stages 0-5, never the score.
    return subprocess.run(
        [sys.executable, str(tree / "verifier/verify.py"), str(submission), "--no-score"],
        capture_output=True,
        text=True,
    )


def rejected_at(r: subprocess.CompletedProcess[str], stage: str) -> bool:
    # Exit 1 and the rejection banner naming `stage` - never a validator error (exit 2).
    return r.returncode == 1 and f"REJECTED at stage {stage}" in r.stdout


def check_pins(tree: Path) -> subprocess.CompletedProcess[str]:
    # The pin-integrity check alone: CI and setup run this, never a submission.
    return subprocess.run(
        [sys.executable, str(tree / "verifier/pins.py"), "--check"],
        capture_output=True,
        text=True,
    )


def edit(path: Path, old: str, new: str) -> None:
    # Substitute exactly once, so a test cannot silently mutate the wrong thing.
    text = path.read_text()
    assert text.count(old) == 1, f"{old!r} occurs {text.count(old)} times in {path.name}"
    path.write_text(text.replace(old, new))


# ── Stage 0: intake ──────────────────────────────────────────────────────


def test_intake_rejects_a_third_file(tree: Path, submission: Path):
    # A smuggled contract or a pre-baked extraction is a rejection, not an ignore.
    (submission / "Lz77.lean").write_text("-- not mine to supply\n")
    assert rejected_at(check(tree, submission), "0 (intake)")


def test_intake_rejects_a_missing_proof(tree: Path, submission: Path):
    (submission / "Parse.lean").unlink()
    assert rejected_at(check(tree, submission), "0 (intake)")


def test_intake_rejects_an_oversized_proof(tree: Path, submission: Path):
    # The size cap runs before anything is elaborated.
    with (submission / "Parse.lean").open("a") as f:
        f.write("-- " + "x" * verify.MAX_FILE_BYTES + "\n")
    assert rejected_at(check(tree, submission), "0 (intake)")


# ── Stage 1: policy ──────────────────────────────────────────────────────


@pytest.mark.parametrize(
    "d",
    [TEMPLATE, HASH_CHAINS, LAZY, MO_LAZY, OPTIMAL],
    ids=["template", "hash-chains", "lazy", "mo-lazy", "optimal"],
)
def test_policy_accepts_the_reference_submissions(d: Path):
    # The reference proofs mention several rules in prose; none may trip the scanner.
    assert verify.scan_rust((d / "parse.rs").read_text()) == []
    assert verify.scan_lean((d / "Parse.lean").read_text()) == []


@pytest.mark.parametrize(
    "rust, why",
    [
        ("'outer: while pos < n {", "labelled loops"),
        ("unsafe { }", "`unsafe`"),
        ("for x in 0..3 { }", "Iterator"),
        ('let t = include_bytes!("corpus.bin");', "embedded data"),
        ("use crate::baseline;", "crate root"),
    ],
    ids=["labelled-loop", "unsafe", "for-in", "include_bytes", "use-crate"],
)
def test_policy_rejects_rust_outside_the_subset(tree: Path, submission: Path, rust: str, why: str):
    edit(submission / "parse.rs", "    while pos < n {", f"    {rust}\n    while pos < n {{")
    r = check(tree, submission)
    assert rejected_at(r, "1 (policy)") and why in r.stdout


@pytest.mark.slow
def test_policy_ignores_a_rule_named_in_a_rust_comment(tree: Path, submission: Path):
    # Not rejected at stage 1, so it falls through to the real proof pipeline.
    # Rust comments are stripped first: naming `unsafe` in a doc comment is fine.
    edit(
        submission / "parse.rs",
        "    while pos < n {",
        "    // never unsafe here\n    while pos < n {",
    )
    r = check(tree, submission)
    assert "1 (policy)" not in r.stdout


@pytest.mark.parametrize(
    "lean",
    [
        '#eval IO.FS.writeFile "Verify/Obligation.lean" "theorem accepted := sorry"',
        'run_cmd Lean.logInfo "x"',
        "run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| skip))",
        "initialize hook : Unit ← pure ()",
        'elab "forge" : command => Lean.logInfo "x"',
        "macro_rules | `(tactic| skip) => `(tactic| trivial)",
        'syntax "forge" : command',
        f'theorem t : True := by trace "{FORGED_REPORT}"; trivial',
        "import Lean",
    ],
    ids=[
        "eval",
        "run_cmd",
        "run_tac",
        "initialize",
        "elab",
        "macro_rules",
        "syntax",
        "trace",
        "import-Lean",
    ],
)
def test_policy_rejects_code_running_lean(tree: Path, submission: Path, lean: str):
    # The hole: Lean elaborates with full IO, so a proof that runs code is not a proof.
    edit(submission / "Parse.lean", "namespace Submission\n", f"{lean}\n\nnamespace Submission\n")
    r = check(tree, submission)
    assert rejected_at(r, "1 (policy)") and "Parse.lean" in r.stdout


def test_lean_policy_is_not_fooled_by_a_string_literal():
    # Scanned raw: a `--` inside a string must not hide the rest of the line.
    assert verify.scan_lean('def s := "--" #eval IO.println s') != []


# ── Pins: CI and setup only, never per submission ───────────────────────


def pins_drifted(r: subprocess.CompletedProcess[str]) -> bool:
    return r.returncode == 1 and "PINS DRIFTED" in r.stdout


def test_pins_reject_a_modified_contract(tree: Path):
    # Weakening `Valid` by one byte is caught by `pins.py --check`, before any deploy.
    with (tree / "lean/Lz77/Spec.lean").open("a") as f:
        f.write("\n-- weakened\n")
    r = check_pins(tree)
    assert pins_drifted(r) and "lean/Lz77/Spec.lean" in r.stdout


def test_pins_reject_a_modified_encoder(tree: Path):
    with (tree / "measure/src/deflate.rs").open("a") as f:
        f.write("\n// tuned\n")
    assert pins_drifted(check_pins(tree))


def test_pins_reject_a_modified_baseline(tree: Path):
    with (tree / "incumbent/parse.rs").open("a") as f:
        f.write("\n// nerfed\n")
    assert pins_drifted(check_pins(tree))


@pytest.mark.slow
def test_a_modified_contract_is_not_caught_per_submission(tree: Path, submission: Path):
    # The pin check moved to CI/setup on purpose: a submission no longer re-checks it.
    # Not rejected at stage 2, so it falls through to the real proof pipeline.
    with (tree / "lean/Lz77/Spec.lean").open("a") as f:
        f.write("\n-- weakened\n")
    assert "2 (pins)" not in check(tree, submission).stdout


# ── Stage 5: the axiom report ────────────────────────────────────────────


def test_axiom_report_regex_reads_exactly_the_lean_output():
    m = verify.AXIOM_REPORT.match(FORGED_REPORT)
    assert m and m.group(1) == "propext, Classical.choice, Quot.sound"
    assert verify.AXIOM_REPORT.match("'accepted' does not depend on any axioms")
    assert verify.AXIOM_REPORT.match("info: Proof/Parse.lean:3:0: " + FORGED_REPORT) is None
    assert verify.AXIOM_REPORT.match("'weak' depends on axioms: [propext]") is None


# ── Stages 3-5: need the toolchain ───────────────────────────────────────


@needs_toolchain
@pytest.mark.slow
def test_template_passes_the_proof_gate(tree: Path, submission: Path):
    r = check(tree, submission)
    assert r.returncode == 0, r.stdout + r.stderr
    assert "proof accepted" in r.stdout


@needs_toolchain
@pytest.mark.slow
def test_lazy_passes_the_proof_gate(tree: Path):
    # The emission-change submission: Pending, emitted, and the dead flush branch.
    r = check(tree, LAZY)
    assert r.returncode == 0, r.stdout + r.stderr
    assert "proof accepted" in r.stdout


@needs_toolchain
@pytest.mark.slow
def test_optimal_passes_the_proof_gate(tree: Path):
    # The DP submission: the search and the DP stay unproved, only the re-verified emission matters.
    r = check(tree, OPTIMAL)
    assert r.returncode == 0, r.stdout + r.stderr
    assert "proof accepted" in r.stdout


@needs_toolchain
@pytest.mark.slow
def test_mo_lazy_passes_the_proof_gate(tree: Path):
    # miniz level 9 in the provable subset: three emission paths, each restoring the invariant.
    r = check(tree, MO_LAZY)
    assert r.returncode == 0, r.stdout + r.stderr
    assert "proof accepted" in r.stdout


def replace_parse_spec(path: Path, post: str, proof: str) -> None:
    # Cut the template's `parse_spec` off and put a different one under the same name.
    text = path.read_text()
    head = text[: text.index("theorem parse_spec")]
    path.write_text(
        head
        + "theorem parse_spec (input : Slice Std.U8) (out : Slice Std.U32)\n"
        + "    (hlen : input.length ≤ out.length) :\n"
        + f"    slot.parse input out ⦃ {post} ⦄ := by\n  {proof}\n\nend Submission\n"
    )


OBLIGATION_POST = (
    "fun r => r.1.val ≤ input.length ∧ r.2.length = out.length ∧ "
    "LZ77.Valid (bytes input) (toks r.2 r.1.val)"
)


@needs_toolchain
@pytest.mark.slow
def test_weak_statement_rejected_at_statement(tree: Path, submission: Path):
    # Proving `⦃ fun _ => True ⦄` under the pinned name is a type error in the gate.
    replace_parse_spec(submission / "Parse.lean", "fun _ => True", "sorry")
    r = check(tree, submission)
    assert rejected_at(r, "4 (statement)"), r.stdout + r.stderr


@needs_toolchain
@pytest.mark.slow
def test_sorry_rejected_at_axioms(tree: Path, submission: Path):
    # A sorried `parse_spec` builds cleanly. Build success is not the check.
    replace_parse_spec(submission / "Parse.lean", OBLIGATION_POST, "sorry")
    r = check(tree, submission)
    assert rejected_at(r, "5 (axioms)") and "sorryAx" in r.stdout, r.stdout + r.stderr


@needs_toolchain
@pytest.mark.slow
def test_forged_axiom_report_in_the_build_log_is_ignored(tree: Path, submission: Path):
    # The hole's regression test: a forged `#print` report in the build log; verdict still sorryAx.
    replace_parse_spec(submission / "Parse.lean", OBLIGATION_POST, "sorry")
    with (submission / "Parse.lean").open("a") as f:
        f.write(f'\n#print "{FORGED_REPORT}"\n')
    r = check(tree, submission)
    assert rejected_at(r, "5 (axioms)") and "sorryAx" in r.stdout, r.stdout + r.stderr


# ── Stage 4: the sandbox and the limits ──────────────────────────────────

needs_bwrap = pytest.mark.skipif(shutil.which("bwrap") is None, reason="bubblewrap not installed")


def sandboxed(cmd: str) -> subprocess.CompletedProcess[str]:
    # A shell command inside exactly the sandbox the verifier uses for the proof.
    return subprocess.run(
        verify.sandbox_prefix() + ["sh", "-c", cmd], capture_output=True, text=True
    )


@needs_bwrap
@pytest.mark.parametrize(
    "target",
    [
        "lean/Lz77/Spec.lean",
        "lean/Verify/Obligation.lean",
        "lean/Slot/Funs.lean",
        "lean/.lake/packages/mathlib/README.md",
        "lean/.lake/build/lib/lean/Lz77.olean",
        "verifier/PINS.json",
    ],
)
def test_sandbox_blocks_writes_to_what_the_proof_is_judged_against(target: str):
    # Source, contract oleans, Mathlib and the pins are all read-only inside.
    path = VALIDATOR / target
    if not path.exists():
        pytest.skip(f"{target} not built here")
    before = path.read_bytes()
    # EROFS as a user; EACCES when root is mapped to nobody inside the namespace (CI containers).
    r = sandboxed(f"echo x >> {path}")
    assert r.returncode != 0 and ("Read-only" in r.stderr or "Permission denied" in r.stderr), (
        r.stderr
    )
    assert path.read_bytes() == before


@needs_bwrap
def test_sandbox_lets_lake_write_only_the_proof_artifacts():
    # The build directory is writable (Lake needs it), Mathlib's tree is not.
    build = VALIDATOR / "lean/.lake/build"
    if not build.exists():
        pytest.skip("lean/.lake/build not built here")
    probe = build / ".sandbox-probe"
    assert sandboxed(f"echo x > {probe} && rm {probe}").returncode == 0
    assert not probe.exists()


@needs_bwrap
def test_sandbox_has_no_network():
    # `/proc/net/dev` is namespaced; `/sys/class/net` would show the host's.
    r = sandboxed("cat /proc/net/dev")
    assert r.returncode == 0, r.stderr
    ifaces = [ln.split(":")[0].strip() for ln in r.stdout.splitlines()[2:]]
    assert ifaces == ["lo"], r.stdout


def test_missing_sandbox_is_a_validator_error_not_a_rejection(
    tree: Path, submission: Path, tmp_path: Path
):
    # Without bubblewrap a validator must stop with exit 2, before touching the submission.
    stub_bin = tmp_path / "bin"
    stub_bin.mkdir()
    bash = shutil.which("bash")
    assert bash, "bash must be on PATH to run this test"
    (stub_bin / "bash").symlink_to(bash)
    r = subprocess.run(
        [sys.executable, str(tree / "verifier/verify.py"), str(submission), "--no-score"],
        capture_output=True,
        text=True,
        env={"PATH": str(stub_bin), "HOME": str(tmp_path)},
    )
    assert r.returncode == 2 and "bubblewrap" in r.stdout and "0 intake" not in r.stdout


@needs_toolchain
@pytest.mark.slow
def test_proof_that_elaborates_too_long_is_rejected_at_statement(
    tree: Path, submission: Path, monkeypatch: pytest.MonkeyPatch
):
    # The wall-clock cap is a rejection of the submission, not a validator error.
    monkeypatch.setenv("VERIFY_LEAN_TIMEOUT", "1")
    r = check(tree, submission)
    assert rejected_at(r, "4 (statement)") and "did not finish" in r.stdout, r.stdout + r.stderr


# ── init.sh: pinned downloads ────────────────────────────────────────────


def fetch_pinned(src: Path, dest: Path, sha: str) -> subprocess.CompletedProcess[str]:
    # The helper from config.sh, against a file:// URL so the test needs no network.
    return subprocess.run(
        [
            "bash",
            "-c",
            f'. "{VALIDATOR}/verifier/config.sh" && fetch_pinned "file://{src}" "{dest}" "{sha}"',
        ],
        capture_output=True,
        text=True,
    )


def test_fetch_pinned_accepts_the_right_hash(tmp_path: Path):
    import hashlib

    src = tmp_path / "release.tar.gz"
    src.write_bytes(b"a release")
    dest = tmp_path / "out"
    r = fetch_pinned(src, dest, hashlib.sha256(b"a release").hexdigest())
    assert r.returncode == 0 and dest.read_bytes() == b"a release"


def test_fetch_pinned_rejects_and_removes_a_tampered_download(tmp_path: Path):
    # A changed release or a tampered mirror is exit 2 and no file left behind.
    src = tmp_path / "release.tar.gz"
    src.write_bytes(b"not the release")
    dest = tmp_path / "out"
    r = fetch_pinned(src, dest, "0" * 64)
    assert r.returncode == 2 and "sha256 mismatch" in r.stderr
    assert not dest.exists()


def test_every_download_pin_is_a_sha256():
    text = (VALIDATOR / "verifier/config.sh").read_text()
    pins = cast("list[tuple[str, str]]", re.findall(r'^(\w+_SHA256)="([0-9a-f]*)"$', text, re.M))
    assert {n for n, _ in pins} == {"AENEAS_SHA256", "ELAN_SHA256", "RUSTUP_SHA256"}
    assert all(len(h) == 64 for _, h in pins)


# ── The shared-Mathlib layout ────────────────────────────────────────────


@needs_toolchain
@pytest.mark.slow
def test_template_passes_when_lake_packages_is_a_symlink(tmp_path: Path, submission: Path):
    # The shared-Mathlib layout: `.lake/packages` is a symlink, and bwrap binds onto paths.
    dst = tmp_path / "validator"
    shutil.copytree(
        VALIDATOR,
        dst,
        symlinks=True,
        ignore=shutil.ignore_patterns(".work", ".lake", "target", "tests", "__pycache__"),
    )
    for rel in [".work", "slot/target", "measure/target"]:
        if (VALIDATOR / rel).exists():
            (dst / rel).symlink_to(VALIDATOR / rel, target_is_directory=True)
    # Only `packages` is shared; the contract and slot build fresh into this copy.
    (dst / "lean/.lake").mkdir()
    (dst / "lean/.lake/packages").symlink_to(
        VALIDATOR / "lean/.lake/packages", target_is_directory=True
    )
    r = check(dst, submission)
    assert r.returncode == 0, r.stdout + r.stderr
