#!/usr/bin/env bash
# Local-only pinned project; actual Lean execution, not static source grep.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build DASHILiteralClayNS
out="$(mktemp)"
trap 'rm -f "$out"' EXIT
lake env lean SubmissionAudit.lean > "$out" 2>&1 || { cat "$out"; exit 1; }
cat "$out"
python3 ../scripts/check_exact_lean_axiom_receipts.py "$out" \
  NavierStokesR3.theorem_1_1 \
  NavierStokesR3.comparator_of_breakdown \
  DASHILiteralClayNS.SubmissionAudit.directComparatorC \
  DASHILiteralClayNS.SubmissionAudit.directClayC \
  DASHILiteralClayNS.SubmissionAudit.directClayC_roundTrip \
  PeriodicPaper.periodic_corollary \
  NavierStokes.ComparatorBridge.option_D_of_paper_candidate \
  DASHILiteralClayNS.SubmissionAudit.directComparatorD \
  DASHILiteralClayNS.SubmissionAudit.directClayD \
  DASHILiteralClayNS.SubmissionAudit.directClayD_roundTrip \
  DASHILiteralClayNS.SubmissionAudit.dualRouteReceipt
echo 'Direct C/D exact axiom reports accepted; LeanDojo terminal reports are a separate check.'
