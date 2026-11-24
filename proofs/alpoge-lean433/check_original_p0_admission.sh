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
  echo 'Optional RowSrc direct consumer kernel ran; inspect its printed axioms.'
fi

printf 'P0 SOURCE-ADMISSION ACCEPTED (isolated v4.33.1): %s\n' "$CHECKOUT"
printf 'Receipts: %s\n' "$REPORT_DIR"
printf 'Still OPEN: compatible root proof import and Agda all-character semantic mapping.\n'
