#!/usr/bin/env bash
# P0: ORIGINAL published Main.lean -> existing DASHI RHAdmission.lean.
# User-selected local execution; NO GitHub CI, no theorem duplication,
# no 4.33.1 OLean imported into the incompatible 4.28 root toolchain.
#
# Usage:
#   bash proofs/alpoge-lean433/check_original_p0_admission.sh [source-checkout]
# Optional (separate experimental donor, NOT a prerequisite for Main P0):
#   GRH_P0_CHECK_DIRECTIONAL=1 bash proofs/alpoge-lean433/check_original_p0_admission.sh
#
# The unmodified author fork is materialized locally by the EXISTING
# checkout_fork_source.sh, which verifies commit, blob hashes, Lean
# toolchain and Mathlib revision. This script DOES NOT vendor that source.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
SIDECAR="$ROOT/proofs/alpoge-lean433"
CHECKOUT="${1:-$ROOT/.local/alpoge-rh-v4331}"
REPORT_DIR="${GRH_P0_REPORT_DIR:-$ROOT/.local/grh-p0-admission}"
# Custom paths should remain relative to the DASHI root, not the build cwd.
if [[ "$REPORT_DIR" != /* ]]; then REPORT_DIR="$ROOT/$REPORT_DIR"; fi

# Fail fast BEFORE a potentially large original source checkout.
if ! command -v lake >/dev/null 2>&1; then
  echo 'BLOCKED: local pinned Lean/lake toolchain unavailable; no kernel receipt.' >&2
  exit 12
fi
if ! command -v python3 >/dev/null 2>&1; then
  echo 'BLOCKED: Python 3 needed for independent axiom-log audit.' >&2
  exit 13
fi
if [[ ! -f "$SIDECAR/RHAdmission.lean" ]]; then
  echo 'BLOCKED: missing existing original Main admission adapter.' >&2
  exit 14
fi

mkdir -p "$REPORT_DIR"
# Already-owned provenance checker (fail closed on wrong source and dirty
# checkout). Do not clone another upstream or accept stale olean identities.
bash "$SIDECAR/checkout_fork_source.sh" "$CHECKOUT"

# Build ORIGINAL source module first. No newly postulated theorem, no
# Mathlib version drift and no claim of success from mere text presence.
(
  cd "$CHECKOUT"
  lake build Main 2>&1 | tee "$REPORT_DIR/original-main-build.log"
  lake env lean "$SIDECAR/RHAdmission.lean" 2>&1 |
    tee "$REPORT_DIR/original-admission-lean.log"
)

# Audit the actual Lean output; #print axioms in RHAdmission.lean emits
# each exact original target. A missing declaration/line or unexpected
# axiom fails. Text/source-grep alone is NOT acceptance.
python3 "$ROOT/scripts/check_exact_lean_axiom_receipts.py" \
  "$REPORT_DIR/original-admission-lean.log" \
  DASHI.AlpogeRH.original_mathlib_rh \
  DASHI.AlpogeRH.original_riemann_zero_location \
  DASHI.AlpogeRH.original_dirichlet_nonvanishing \
  DASHI.AlpogeRH.original_dirichlet_zeros \
  DASHI.AlpogeRH.original_primitive_dirichlet_zeros

if [[ "${GRH_P0_CHECK_DIRECTIONAL:-0}" == 1 ]]; then
  if [[ ! -f "$SIDECAR/RHGRHP0DirectionalSourceCut.lean" ]]; then
    echo 'BLOCKED: missing optional direct RowSrc donor adapter.' >&2
    exit 15
  fi
  (
    cd "$CHECKOUT"
    lake env lean "$SIDECAR/RHGRHP0DirectionalSourceCut.lean" 2>&1 |
      tee "$REPORT_DIR/directional-donor-lean.log"
  )
  # Check the nine exact source-directed theorem receipts, not merely build exit.
  python3 "$ROOT/scripts/check_exact_lean_axiom_receipts.py" \
    "$REPORT_DIR/directional-donor-lean.log" \
    DASHI.AlpogeRH.P0Directional.all_original_grh_and_rh_endpoints_from_galois_row \
    DASHI.AlpogeRH.P0Directional.halfplane_iff_original_all_character \
    DASHI.AlpogeRH.P0Directional.original_zeta_zeros_iff_mathlib_rh \
    DASHI.AlpogeRH.P0Directional.original_zeta_iff_rh \
    DASHI.AlpogeRH.P0Directional.every_character_of_original_galois_row \
    DASHI.AlpogeRH.P0Directional.rh_of_original_galois_row \
    DASHI.AlpogeRH.P0Directional.dirichlet_right_half_of_original_galois_row \
    DASHI.AlpogeRH.P0Directional.dirichlet_strip_of_original_galois_row \
    DASHI.AlpogeRH.P0Directional.primitive_strip_of_original_galois_row
  echo 'Optional RowSrc direct consumer: exact axiom receipt audit accepted.'
fi


# Optional independent arithmetic consumer, never a prerequisite for RH.
# Use a separately prepared, unmodified Robin1984 checkout, not a new vendored copy.
# Its full commit/tree and toolchain are checked before any optional build.
if [[ -n "${GRH_P0_ROBIN_CHECKOUT:-}" ]]; then
  ROBIN="$(cd "$GRH_P0_ROBIN_CHECKOUT" && pwd -P)"
  [[ "$(git -C "$ROBIN" rev-parse HEAD)" == 5ce18bf3487c68d9353276ef5811057f60d17808 ]]
  [[ "$(git -C "$ROBIN" rev-parse 'HEAD^{tree}')" == 7714a8e1a93a7472e6f0ddf20211a4ef9e31c633 ]]
  [[ "$(git -C "$ROBIN" rev-parse HEAD:lean-toolchain)" == a8afa7d1b02d96f0671eba854a8dc4b416beb473 ]]
  [[ -z "$(git -C "$ROBIN" status --porcelain)" ]]
  [[ "$(git -C "$ROBIN" rev-parse HEAD:lake-manifest.json)" == ce2d042a400921cd1f5af10a47d47c5e69cb0419 ]]
  python3 - "$CHECKOUT/lake-manifest.json" "$ROBIN/lake-manifest.json" <<'PY'
import json, sys
from pathlib import Path
a, b = [{p["name"]: p["rev"] for p in json.loads(Path(x).read_text())["packages"]} for x in sys.argv[1:]]
if not a or not all(b.get(name) == rev for name, rev in a.items()):
    raise SystemExit("BLOCKED: original RH dependencies do not match the arithmetic source")
PY
  (
    cd "$ROBIN"
    lake build Solution 2>&1 | tee "$REPORT_DIR/original-robin-build.log"
  )
  [[ -z "$(git -C "$ROBIN" status --porcelain)" ]]
  # Obtain the actual Lake path rather than guess extra dependency directories.
  # Normalize paths relative to the original arithmetic checkout.
  ROBIN_PATH="$(cd "$ROBIN" && lake env bash -c 'printf "%s" "$LEAN_PATH"')"
  ROBIN_PATH="$(python3 - "$ROBIN" "$ROBIN_PATH" <<'PY'
import os, sys
root, paths = sys.argv[1:]
parts = [p for p in paths.split(os.pathsep) if p]
if not parts:
    raise SystemExit("BLOCKED: no arithmetic module search path")
print(os.pathsep.join(os.path.abspath(os.path.join(root, p)) for p in parts))
PY
)"
  (
    cd "$CHECKOUT"
    lake env bash -c 'export LEAN_PATH="$LEAN_PATH:$1"; exec lean "$2"' _ \
      "$ROBIN_PATH" "$SIDECAR/RHArithmeticAdmission.lean" 2>&1 |
      tee "$REPORT_DIR/arithmetic-admission-lean.log"
  )
  python3 "$ROOT/scripts/check_exact_lean_axiom_receipts.py" \
    "$REPORT_DIR/arithmetic-admission-lean.log" \
    DASHI.AlpogeRH.Arithmetic.robin \
    DASHI.AlpogeRH.Arithmetic.lagarias \
    DASHI.AlpogeRH.Arithmetic.cyclotomic_corrected_ideal_robin \
    DASHI.AlpogeRH.Arithmetic.cyclotomic_dedekind_rh
  echo 'Optional original arithmetic consumers: exact axiom receipt audit accepted.'
fi

printf 'P0 SOURCE-ADMISSION ACCEPTED (isolated v4.33.1): %s\n' "$CHECKOUT"
printf 'Receipts: %s\n' "$REPORT_DIR"
printf 'Still OPEN: compatible root proof import and Agda all-character semantic mapping.\n'
