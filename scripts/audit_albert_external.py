#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor" / "JordanAlgebra"
ALBERT = VENDOR / "Jordan" / "AlbertAlgebra.lean"
TOOLCHAIN = VENDOR / "lean-toolchain"
LAKEFILE = VENDOR / "lakefile.toml"

EXPECTED_SHA = "a4b0d58554732ced63b4217200baa56be5a2c3d5"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.31.0"

REQUIRED = {
    "Albert carrier": "abbrev AlbertAlgebra := HermitianOctonionMatrix",
    "linear decomposition": "noncomputable def albertEquiv",
    "Jordan instance producer": "def ofAlbert : JordanAlgebra",
    "trace": "def trace (x : AlbertAlgebra",
    "cubic determinant": "def det (x : AlbertAlgebra",
    "rank-three det/trace package": "noncomputable def detTrace",
    "donor cubic boundary": "What isn't proved is that `det` satisfies any further multiplicative or",
}


def fail(msg: str) -> None:
    print(f"ALBERT EXTERNAL AUDIT FAIL: {msg}", file=sys.stderr)
    raise SystemExit(1)


def main() -> None:
    if not ALBERT.exists():
        fail("vendor/JordanAlgebra is missing; checkout with submodules: recursive")
    text = ALBERT.read_text(encoding="utf-8")
    for label, needle in REQUIRED.items():
        if needle not in text:
            fail(f"missing {label}: {needle!r}")
    if TOOLCHAIN.read_text(encoding="utf-8").strip() != EXPECTED_TOOLCHAIN:
        fail("unexpected upstream Lean toolchain")
    lake = LAKEFILE.read_text(encoding="utf-8")
    if 'rev = "v4.31.0"' not in lake:
        fail("unexpected upstream mathlib pin")
    vendor_meta = (ROOT / "vendor" / "JordanAlgebra.VENDOR").read_text(encoding="utf-8")
    if EXPECTED_SHA not in vendor_meta:
        fail("VENDOR metadata does not contain exact source SHA")
    print("Albert external donor source audit: PASS")
    for label in REQUIRED:
        print(f"  paid-source-surface: {label}")


if __name__ == "__main__":
    main()
