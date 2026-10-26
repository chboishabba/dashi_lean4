"""Fail-closed reproducibility preflight for the opt-in NS paper Lean target.

This inspects the CHECKED-IN root Lean toolchain, the Mathlib Lake
requirement and the manifest inputRev. It does not assert that a Lean
kernel accepted any theorem and does not change the repository's
toolchain or its unrelated default targets.

Typical use:
    python scripts/check_ns_paper_build_preflight.py
    LEAN_TOOLCHAIN=leanprover/lean4:v4.28.0 lake build NSPaperBridges

The second command is a *proposed focused build*, not an executed
command on this PR. Mathlib's own tag v4.28.0 pins Lean v4.28.0;
see github.com/leanprover-community/mathlib4/blob/v4.28.0/lean-toolchain.
"""
from __future__ import annotations

import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def parse_rev(lakefile: str) -> str:
    match = re.search(
        r'\[\[require\]\]\s*name = "mathlib"\s*'
        r'git = "[^"]+"\s*rev = "([^"]+)"', lakefile
    )
    if not match:
        raise ValueError("Mathlib requirement/revision not found")
    return match.group(1)


def check_preflight(root: Path = ROOT) -> dict[str, str | bool]:
    root_toolchain = (root / "lean-toolchain").read_text().strip()
    mathlib_rev = parse_rev((root / "lakefile.toml").read_text())
    manifest = json.loads((root / "lake-manifest.json").read_text())
    matches = [
        p for p in manifest.get("packages", [])
        if p.get("name") == "mathlib"
    ]
    if len(matches) != 1:
        raise ValueError("Expected exactly one locked Mathlib package")
    manifest_revision = matches[0]["inputRev"]
    pinned_toolchain = f"leanprover/lean4:{mathlib_rev}"
    if manifest_revision != mathlib_rev:
        raise ValueError(
            "Lake requirement/manifest mismatch: "
            f"{mathlib_rev} != {manifest_revision}"
        )
    build_target = 'name = "NSPaperBridges"'
    if build_target not in (root / "lakefile.toml").read_text():
        raise ValueError("Missing source-bounded NSPaperBridges target")
    return {
        "root_toolchain": root_toolchain,
        "mathlib_revision": mathlib_rev,
        "manifest_revision": manifest_revision,
        "expected_toolchain": pinned_toolchain,
        "matches": root_toolchain == pinned_toolchain,
        "scoped_build_command":
            f"LEAN_TOOLCHAIN={pinned_toolchain} lake build NSPaperBridges",
    }


def main() -> int:
    report = check_preflight()
    print(json.dumps(report, indent=2))
    if not report["matches"]:
        print(
            "MISMATCH: root toolchain and pinned Mathlib toolchain differ. "
            "Treat default-root Lean build status as UNKNOWN; run the "
            "scoped command using the matching installed toolchain."
        )
        return 2
    print("PREFLIGHT MATCH ONLY. Kernel compilation remains UNVERIFIED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
