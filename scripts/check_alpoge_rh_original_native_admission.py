#!/usr/bin/env python3
"""Fail-closed original Alpöge RH admission replay.

A theorem NAME and exact Clay↔Mathlib BIDI are NOT a proof of RH.
Only the expected pinned external source tree, actual Lean executable,
successful native elaboration and transitive axiom audit may constitute
an admission receipt. This script DOES NOT prove RH by itself.

Usage with an actual checked-out external original source:
 python scripts/check_alpoge_rh_original_native_admission.py \\
   --external-root /path/to/pinned/external \\
   --main-sha256 <sha256-of-original-Main.lean> \\
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
    p.add_argument("--lean-version", default=REQUIRED_VERSION)
    p.add_argument("--lake", default="lake")
    p.add_argument("--allow-axiom", action="append", default=[])
    a = p.parse_args()
    root = a.external_root.resolve()
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
        v = run([a.lake, "env", "lean", "--version"], root)
    except (FileNotFoundError, subprocess.TimeoutExpired) as e:
        print("FAIL: pinned native compiler unavailable", e)
        return 2
    print("Compiler version:", v.stdout.strip())
    if v.returncode or a.lean_version not in v.stdout:
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
        check.write_text(
            "import Main\n"
            "example : _root_.RiemannHypothesis := _root_.riemannHypothesis\n"
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
    match = re.search(r"depends on axioms:\s*\[([^]]*)\]", axiom_text)
    if not match:
        print("FAIL: unable to parse explicit RH axiom dependency list")
        return 2
    actual = {s.strip() for s in match.group(1).split(",") if s.strip()}
    unexpected = actual - (WHITELIST | set(a.allow_axiom))
    if unexpected:
        print("FAIL: unexpected transitive axioms", sorted(unexpected))
        return 2
    print("NATIVE ORIGINAL RH ADMISSION SOURCE/AXIOM AUDIT PASS")
    print("Pinned Main sha256", digest)
    print("Trusted axiom dependencies:", sorted(actual))
    return 0


if __name__ == "__main__":
    sys.exit(main())
