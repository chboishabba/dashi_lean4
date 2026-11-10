#!/usr/bin/env python3
"""Local, fail-closed entrypoint for external unconditional Kakeya verification.

Run on an existing clean Project Numina checkout with pinned submodule.
This wrapper does not claim to be a proof: the upstream official check.py
performs the actual kernel check, axioms and independent comparators.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

NUMINA_REVIEWED_HEAD = "a26427e3c2fcaf9f98694fbd0d4dd49e41dcf5e3"\n\nEXPECTED = {
    "toolchain": "leanprover/lean4:v4.32.0-rc1",
    "lean_githash": "b4812ae53eea93439ad5dce5a5c26591c31cb697",
    "bytedance_commit": "42f739b484fd055e0aa29601c35677ad996f2ef2",
    "mathlib_commit": "1b0782d8191b03e0001caac10e1601d17f2cd580",
    "numina_manifest_sha256": "67bbc3bdc4691e6e36325c7688e5d71dbbcf3f685e87bd94b059eb4d725f39f6",
}

def output(*cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()

def inspect(root):
    pinned = json.loads((root / "verification/unconditional/bridge-lock.json").read_text())
    for name, expected in EXPECTED.items():
        if pinned.get(name) != expected:
            raise ValueError(f"wrong {name}: {pinned.get(name)!r}")
    if (root / "lean-toolchain").read_text().strip() != EXPECTED["toolchain"]:
        raise ValueError("toolchain mismatch")
    digest = hashlib.sha256((root / "lake-manifest.json").read_bytes()).hexdigest()
    if digest != EXPECTED["numina_manifest_sha256"]:
        raise ValueError("manifest hash mismatch")
    upstream = root / "upstream/3d-sticky-kakeya"
    if output("git", "rev-parse", "HEAD", cwd=upstream) != EXPECTED["bytedance_commit"]:
        raise ValueError("sticky upstream revision mismatch")
    if output("git", "rev-parse", "HEAD", cwd=root) != NUMINA_REVIEWED_HEAD:\n        raise ValueError("Numina source HEAD differs from reviewed pin")\n    for checkout in (root, upstream):
        if output("git", "status", "--porcelain", "--untracked-files=normal", cwd=checkout):
            raise ValueError(f"dirty checkout: {checkout}")
    return upstream

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--execute", action="store_true")
    parser.add_argument("--receipt", type=Path, default=Path("kakeya-local-receipt.json"))
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("jobs must be positive")
    record = {"status": "not_run", "pins": EXPECTED, "numina_reviewed_head": NUMINA_REVIEWED_HEAD,
              "command": ["python3", "verification/check.py", "--scope", "full",
                          "--require-clean", "--jobs", str(args.jobs)]}
    try:
        root = args.checkout.resolve(strict=True)
        upstream = inspect(root)
        record["numina_head"] = output("git", "rev-parse", "HEAD", cwd=root)
        record["sticky_head"] = output("git", "rev-parse", "HEAD", cwd=upstream)
        record["status"] = "preflight_pass"
        if args.execute:
            result = subprocess.run(record["command"], cwd=root, check=False)
            record["upstream_exit_code"] = result.returncode
            record["status"] = "verification_pass" if result.returncode == 0 else "verification_fail"
    except (OSError, ValueError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
        record["status"] = "preflight_fail"
        record["error"] = str(error)
    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"{record['status']}: {args.receipt}")
    return 0 if record["status"] in ("preflight_pass", "verification_pass") else 1

if __name__ == "__main__":
    sys.exit(main())
