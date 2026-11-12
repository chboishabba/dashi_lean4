#!/usr/bin/env bash
# Fail-closed LOCAL Lean acceptance for the selected BSD original-object cut.
# No CI dependency, Docker, network access, or branch mutation.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  echo 'BLOCKED: lake is unavailable; source-written is not kernel-accepted' >&2
  exit 12
fi
if ! command -v lean >/dev/null 2>&1; then
  echo 'NOTE: lean not on PATH; lake env lean may still supply the pinned toolchain' >&2
fi

echo "Lean toolchain: $(cat lean-toolchain)"
echo "Mathlib pin: $(grep -A3 'name = \"mathlib\"' lake-manifest.json | tr '\n' ' ' || true)"
echo 'Neither the pinned toolchain nor mathlib revision is silently changed.'

for module in \
  MillenniumBSDPinnedSquareCriterionV428Exact \
  MillenniumBSDCMTwoAdicValuationArithmeticExact \
  MillenniumBSDCMQ2ActualCurveValuationExact \
  MillenniumBSDCMQ2SquareClassValuationParityExact \
  MillenniumBSDCMQ2ActualLocalImageParityExact \
  MillenniumBSDCMAllPrimeRationalSquareSupportExact \
  MillenniumBSDCMAllPrimeLocalFirstParityExact \
  MillenniumBSDCMOddPrimeLocalSecondParityExact \
  MillenniumBSDCMOddPrimeRationalSquareSupportExact \
  MillenniumBSDCMOriginalExplicitSelmerFourTorsionExact \
  MillenniumBSDCMOriginalExplicitCokernelZeroExact
do
  echo "LOCAL KERNEL CHECK: Synthesis.$module"
  lake env lean "Synthesis/$module.lean"
done

tmp="$(mktemp "$PWD/.bsd_maxcut_axioms_XXXXXXXX.lean")"
trap 'rm -f "$tmp"' EXIT
cat > "$tmp" <<'EOF'
import Synthesis.MillenniumBSDCMOriginalExplicitCokernelZeroExact
#print axioms Synthesis.Millennium.BSD.cmPinnedRatSquare_of_nonneg_even_padicVal
#print axioms Synthesis.Millennium.BSD.cmQpLocalKummerImage_firstParity_zero
#print axioms Synthesis.Millennium.BSD.cmQpOddLocalKummerImage_secondParity_zero
#print axioms Synthesis.Millennium.BSD.cmExplicitTwoSelmer_carrier_eq_four_torsion
#print axioms Synthesis.Millennium.BSD.cmTorsionEquivOriginalExplicitSelmer
#print axioms Synthesis.Millennium.BSD.cmGlobalKummerQuotientEquivExplicitSelmer
#print axioms Synthesis.Millennium.BSD.cmExplicitTwoSelmerCokernel_subsingleton
EOF
echo 'LOCAL AXIOM INSPECTION: original source objects'
lake env lean "$tmp"

if [[ "${1:-}" == "--full" ]]; then
  echo 'LOCAL ROOT CHECK: Synthesis.lean'
  lake env lean Synthesis.lean
fi

echo 'KERNEL TYPECHECK COMPLETED. Inspect the axiom output before admission.'
echo 'Classical.choice and proof irrelevance are not substitute BSD mathematical assumptions.'
