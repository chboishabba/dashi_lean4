#!/usr/bin/env python3
"""Fail-closed original Alpöge RH admission replay.

A theorem NAME and exact Clay↔Mathlib BIDI are NOT a proof of RH.
Only the expected pinned external source tree, actual Lean executable,
successful native elaboration and transitive axiom audit may constitute
an admission receipt. This script DOES NOT prove RH by itself.

Usage with an actual checked-out external original source:
 python scripts/check_alpoge_rh_original_native_admission.py \\
   --external-root /path/to/pinned/external \\
   --main-sha256 <sha256-of-original-Main.lean> \\\n   --expected-git-head <40-hex-original-source-commit> \\
   --tree-manifest /path/to/original-source-sha256.json \\
   --lean-version v4.33.1 --lake /path/to/lake

It compares the actual Main bytes to the required hash, checks the
installed pinned Lean version, runs the actual external Main in its
own project, and asks the native kernel for an explicit original
witness plus its complete (not preselected) #print axioms report.

No input path, hash, native Lean, witness, or matching pin => FAILURE.
Results cannot certify analytic correctness beyond the native proof
and trust ledger, and must never be promoted from an empty printout.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

WHITELIST = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_VERSION = "v4.33.1"


def run(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, text=True, capture_output=True,
                          check=False, timeout=120)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--external-root", required=True, type=Path)
    p.add_argument("--main-sha256", required=True)
    p.add_argument("--expected-git-head", required=True,
                   help="Immutable external original source Git commit SHA")
    p.add_argument("--tree-manifest", required=True, type=Path,
                   help="SHA256 JSON map of every original .lean/config source file")
    p.add_argument("--lake", default="lake")
    a = p.parse_args()
    root = a.external_root.resolve()
    if not re.fullmatch("[0-9a-f]{40}", a.expected_git_head):
        print("FAIL: immutable original external Git HEAD pin missing/malformed")
        return 2
    try:
        head = run(["git", "rev-parse", "HEAD"], root)
        status = run(["git", "status", "--porcelain"], root)
    except (FileNotFoundError, subprocess.TimeoutExpired, OSError) as exc:
        print("FAIL: external original Git checkout missing/uninspectable:", exc)
        return 2
    if (head.returncode or status.returncode
            or head.stdout.strip() != a.expected_git_head
            or status.stdout.strip()):
        print("FAIL: unpinned or dirty external original Git checkout")
        return 2
    src = root / "Main.lean"
    if not src.is_file() or not (root / "lakefile.toml").is_file() and not (root / "lakefile.lean").is_file():
        print("FAIL: original Main or Lake project missing")
        return 2
    if not re.fullmatch("[0-9a-f]{64}", a.main_sha256):
        print("FAIL: SHA256 pin missing or malformed")
        return 2
    digest = hashlib.sha256(src.read_bytes()).hexdigest()
    if digest != a.main_sha256:
        print(f"FAIL: external original Main SHA mismatch: {digest}")
        return 2
    try:
        expected = json.loads(a.tree_manifest.read_text(encoding="utf8"))
        if not isinstance(expected, dict) or not expected:
            raise ValueError("empty or non-object manifest")
    except (OSError, ValueError) as exc:
        print("FAIL: source tree manifest unavailable", exc)
        return 2
    actual_paths = {
        str(f.relative_to(root).as_posix()) for f in root.rglob("*.lean")
        if ".lake" not in f.relative_to(root).parts
        and ".git" not in f.relative_to(root).parts
    }
    actual_paths |= {name for name in
        ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json")
        if (root / name).is_file()}
    if set(expected) != actual_paths:
        print("FAIL: incomplete/extra external original source manifest")
        print("unlisted:", sorted(actual_paths - set(expected))[:20])
        print("missing:", sorted(set(expected) - actual_paths)[:20])
        return 2
    for name, pinned in expected.items():
        candidate = (root / name).resolve()
        if (not candidate.is_relative_to(root)
                or not candidate.is_file()
                or not re.fullmatch("[0-9a-f]{64}", pinned)):
            print("FAIL: invalid manifest path/hash:", name)
            return 2
        if hashlib.sha256(candidate.read_bytes()).hexdigest() != pinned:
            print("FAIL: original source tree checksum mismatch:", name)
            return 2
    if expected.get("Main.lean") != digest:
        print("FAIL: pinned Main hash differs from pinned complete tree")
        return 2
    try:
        v = run([a.lake, "env", "lean", "--version"], root)
    except (FileNotFoundError, subprocess.TimeoutExpired) as e:
        print("FAIL: pinned native compiler unavailable", e)
        return 2
    print("Compiler version:", v.stdout.strip())
    if v.returncode or REQUIRED_VERSION not in v.stdout:
        print("FAIL: wrong Lean version")
        return 2
    try:
        original = run([a.lake, "env", "lean", "Main.lean"], root)
    except (FileNotFoundError, subprocess.TimeoutExpired) as e:
        print("FAIL: original proof elaboration unavailable", e)
        return 2
    if original.returncode:
        print("FAIL: original Main native elaboration rejected")
        print((original.stdout + original.stderr)[-3000:])
        return 2
    with tempfile.TemporaryDirectory(prefix="original_rh_admission_") as d:
        check = Path(d) / "OriginalRHAdmissionCheck.lean"
        # Do not rely on import Main without first building its .olean:
        # replay the actual exact pinned source together with the witness.
        check.write_text(
            src.read_text(encoding="utf8") + "\n" +
            "example : _root_.RiemannHypothesis := _root_.riemannHypothesis\n" +
            "#print axioms _root_.riemannHypothesis\n",
            encoding="utf8",
        )
        try:
            result = run([a.lake, "env", "lean", str(check)], root)
        except (FileNotFoundError, subprocess.TimeoutExpired) as e:
            print("FAIL: native witness check unavailable", e)
            return 2
    if result.returncode:
        print("FAIL: original RH witness missing/rejected")
        print((result.stdout + result.stderr)[-3000:])
        return 2
    axiom_text = result.stdout + result.stderr
    print(axiom_text[-3000:])
    # Lean emits e.g. 'theorem_name depends on axioms: [propext, ...]'.
    if "depends on axioms:" not in axiom_text and "does not depend on any axioms" not in axiom_text:
        print("FAIL: transitive axiom report missing")
        return 2
    # Exact Lean declaration required: incidental text is insufficient.
    entries = re.findall(
        r"(?m)^\\s*(?:_root_\\.)?riemannHypothesis\\s+depends on axioms:\\s*\\[([^]]*)\\]\\s*$",
        axiom_text,
    )
    empty_entries = re.findall(
        r"(?m)^\\s*(?:_root_\\.)?riemannHypothesis\\s+does not depend on any axioms\\s*$",
        axiom_text,
    )
    if len(entries) + len(empty_entries) != 1:
        print("FAIL: exactly one original-witness axiom report required")
        return 2
    actual = {token.strip() for token in entries[0].split(",")
              if token.strip()} if entries else set()
    unexpected = actual - WHITELIST
    if unexpected:
        print("FAIL: unexpected transitive axioms", sorted(unexpected))
        return 2
    print("NATIVE ORIGINAL RH ADMISSION SOURCE/AXIOM AUDIT PASS")
    print("Pinned original external Git HEAD", a.expected_git_head)
    print("Pinned Main sha256", digest)
    print("Trusted axiom dependencies:", sorted(actual))
    return 0


if __name__ == "__main__":
    sys.exit(main())
