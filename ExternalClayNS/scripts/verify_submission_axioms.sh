#!/usr/bin/env bash
# Run only in the pinned ExternalClayNS project after lake build.
# Checks actual Lean's #print axioms output for direct source theorem spines.
# Exits on missing receipts or known non-foundational axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build DASHILiteralClayNS
out="$(mktemp)"
trap 'rm -f "$out"' EXIT
lake env lean SubmissionAudit.lean > "$out" 2>&1 || { cat "$out"; exit 1; }
for name in   NavierStokesR3.theorem_1_1   NavierStokesR3.comparator_of_breakdown   DASHILiteralClayNS.SubmissionAudit.directComparatorC   DASHILiteralClayNS.SubmissionAudit.directClayC   PeriodicPaper.periodic_corollary   NavierStokes.ComparatorBridge.option_D_of_paper_candidate   DASHILiteralClayNS.SubmissionAudit.directComparatorD   DASHILiteralClayNS.SubmissionAudit.directClayD
do
  if ! grep -F "$name" "$out" >/dev/null; then
    echo "Missing Lean axiom receipt: $name" >&2
    cat "$out" >&2
    exit 1
  fi
done
if grep -E 'sorryAx|syntheticOpaque|axiomOfChoice' "$out"; then
  echo 'Unexpected axiom report: manual review required' >&2
  exit 1
fi
echo "Source theorem and direct C/D axiom receipts present; inspect full log for additional trusted axioms."
cat "$out"
