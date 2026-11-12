#!/usr/bin/env bash
# Fail-closed LOCAL Lean acceptance for the selected BSD original-object cut.
# No CI dependency, Docker, network access, or branch mutation.
set -euo pipefail
cd "$(dirname "$0")/.."

# The root project and the pinned mathlib tag currently disagree on Lean.
# Fail CLOSED. The explicit override changes only this shell process,
# never the repository's lean-toolchain, manifest or Nix expressions.
repo_toolchain="$(tr -d '\r\n' < lean-toolchain)"
mathlib_pin="$(grep -A5 '^name = "mathlib"  echo 'BLOCKED: lake is unavailable; source-written is not kernel-accepted' >&2
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
  MillenniumBSDCMOriginalExplicitCokernelZeroExact \
  MillenniumBSDCMActualE2H1ExplicitImageWeldExact \
  MillenniumBSDCMOriginalMordellWeilModTwoCardExact \
  MillenniumBSDCMActualEBarRestrictedShaTwoTargetExact \
  MillenniumBSDCMSelectedPeriodNormalizationExact \
  MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact \
  MillenniumBSDCMShaTwoNotFullShaNegativeControlExact \
  MillenniumBSDCMLevel32EtaFinitePositivityExact \
  MillenniumBSDCMFGAbelianRankZeroFromModTwoExact \
  MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact \
  MillenniumBSDCMOriginalGeometricKummerGroupExact \
  MillenniumBSDCMOriginalGeometricKummerGaloisEquivariantExact
do
  echo "LOCAL KERNEL CHECK: Synthesis.$module"
  lake build "Synthesis.$module"
done

tmp="$(mktemp --suffix=.lean "$PWD/.bsd_maxcut_axioms_XXXXXXXX")"
trap 'rm -f "$tmp"' EXIT
cat > "$tmp" <<'EOF'
import Synthesis.MillenniumBSDCMActualEBarRestrictedShaTwoTargetExact
import Synthesis.MillenniumBSDCMSelectedPeriodNormalizationExact
import Synthesis.MillenniumBSDCMOriginalMordellWeilModTwoCardExact
import Synthesis.MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact
import Synthesis.MillenniumBSDCMShaTwoNotFullShaNegativeControlExact
import Synthesis.MillenniumBSDCMLevel32EtaFinitePositivityExact
import Synthesis.MillenniumBSDCMFGAbelianRankZeroFromModTwoExact
import Synthesis.MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact
import Synthesis.MillenniumBSDCMOriginalGeometricKummerGroupExact
import Synthesis.MillenniumBSDCMOriginalGeometricKummerGaloisEquivariantExact
#print axioms Synthesis.Millennium.BSD.cmPinnedRatSquare_of_nonneg_even_padicVal
#print axioms Synthesis.Millennium.BSD.cmQpLocalKummerImage_firstParity_zero
#print axioms Synthesis.Millennium.BSD.cmQpOddLocalKummerImage_secondParity_zero
#print axioms Synthesis.Millennium.BSD.cmExplicitTwoSelmer_carrier_eq_four_torsion
#print axioms Synthesis.Millennium.BSD.cmTorsionEquivOriginalExplicitSelmer
#print axioms Synthesis.Millennium.BSD.cmGlobalKummerQuotientEquivExplicitSelmer
#print axioms Synthesis.Millennium.BSD.cmExplicitTwoSelmerCokernel_subsingleton
#print axioms Synthesis.Millennium.BSD.cmExplicitSelmerToActualE2H1_injective
#print axioms Synthesis.Millennium.BSD.cmActualE2H1ExplicitSelmerImage_eq_torsion
#print axioms Synthesis.Millennium.BSD.cmOriginalMordellWeilModuloTwo_card_eq_four
#print axioms Synthesis.Millennium.BSD.cmSelectedEBarRestrictedShaOne_mem_iff
#print axioms Synthesis.Millennium.BSD.cmSelectedBSDPeriodNormalization
#print axioms Synthesis.Millennium.BSD.cmEveryRationalPoint_modDoubles_eq_actual_twoTorsion
#print axioms Synthesis.Millennium.BSD.cmVanishingTwoTorsion_doesNotForceTrivialGroup
#print axioms Synthesis.Millennium.BSD.cmLevel32EtaProductTruncation_pos
#print axioms Synthesis.Millennium.BSD.cmEveryRationalPoint_eq_twoTorsion_add_double
#print axioms Synthesis.Millennium.BSD.cmSelectedOriginalMordellWeil_ZRank_zero
#print axioms Synthesis.Millennium.BSD.cmLevel32EtaAnalyticExpression_ne_zero
#print axioms Synthesis.Millennium.BSD.cmLevel32EtaAnalyticExpression_differentiableAt
#print axioms Synthesis.Millennium.BSD.cmSelectedGeometricKummerShortExact_group
#print axioms Synthesis.Millennium.BSD.cmSelectedGeometricKummerShortExact_galois_equivariant
EOF
echo 'LOCAL AXIOM INSPECTION: original source objects'
lake env lean "$tmp"

if [[ "${1:-}" == "--full" ]]; then
  echo 'LOCAL ROOT CHECK: Synthesis.lean'
  lake build Synthesis
fi

echo 'KERNEL MODULE BUILD AND AXIOM COMMAND COMPLETED. Inspect all axiom output before admission.'
echo 'Classical.choice and proof irrelevance are not substitute BSD mathematical assumptions.'
 lakefile.toml | sed -n 's/^rev = "\([^"]*\)"/\1/p' | head -n1)"
case "$mathlib_pin" in
  v4.28.0) mathlib_toolchain="leanprover/lean4:v4.28.0" ;;
  *)
    echo "BLOCKED: mathlib pin '$mathlib_pin' needs exact local toolchain audit" >&2
    exit 13
    ;;
esac
active_toolchain="${LEAN_TOOLCHAIN:-$repo_toolchain}"
if [[ "$active_toolchain" != "$mathlib_toolchain" ]]; then
  if [[ "${BSD_USE_MATHLIB_TOOLCHAIN:-0}" == 1 ]]; then
    export LEAN_TOOLCHAIN="$mathlib_toolchain"
    echo "Isolated local toolchain selection: LEAN_TOOLCHAIN=$LEAN_TOOLCHAIN"
  else
    echo "BLOCKED: root $repo_toolchain vs mathlib $mathlib_toolchain" >&2
    echo 'Set BSD_USE_MATHLIB_TOOLCHAIN=1 for an isolated local run; no files are changed.' >&2
    exit 13
  fi
fi

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
  MillenniumBSDCMOriginalExplicitCokernelZeroExact \
  MillenniumBSDCMActualE2H1ExplicitImageWeldExact \
  MillenniumBSDCMOriginalMordellWeilModTwoCardExact \
  MillenniumBSDCMActualEBarRestrictedShaTwoTargetExact \
  MillenniumBSDCMSelectedPeriodNormalizationExact \
  MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact \
  MillenniumBSDCMShaTwoNotFullShaNegativeControlExact \
  MillenniumBSDCMLevel32EtaFinitePositivityExact \
  MillenniumBSDCMFGAbelianRankZeroFromModTwoExact \
  MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact \
  MillenniumBSDCMOriginalGeometricKummerGroupExact
do
  echo "LOCAL KERNEL CHECK: Synthesis.$module"
  lake build "Synthesis.$module"
done

tmp="$(mktemp --suffix=.lean "$PWD/.bsd_maxcut_axioms_XXXXXXXX")"
trap 'rm -f "$tmp"' EXIT
cat > "$tmp" <<'EOF'
import Synthesis.MillenniumBSDCMActualEBarRestrictedShaTwoTargetExact
import Synthesis.MillenniumBSDCMSelectedPeriodNormalizationExact
import Synthesis.MillenniumBSDCMOriginalMordellWeilModTwoCardExact
import Synthesis.MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact
import Synthesis.MillenniumBSDCMShaTwoNotFullShaNegativeControlExact
import Synthesis.MillenniumBSDCMLevel32EtaFinitePositivityExact
import Synthesis.MillenniumBSDCMFGAbelianRankZeroFromModTwoExact
import Synthesis.MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact
import Synthesis.MillenniumBSDCMOriginalGeometricKummerGroupExact
#print axioms Synthesis.Millennium.BSD.cmPinnedRatSquare_of_nonneg_even_padicVal
#print axioms Synthesis.Millennium.BSD.cmQpLocalKummerImage_firstParity_zero
#print axioms Synthesis.Millennium.BSD.cmQpOddLocalKummerImage_secondParity_zero
#print axioms Synthesis.Millennium.BSD.cmExplicitTwoSelmer_carrier_eq_four_torsion
#print axioms Synthesis.Millennium.BSD.cmTorsionEquivOriginalExplicitSelmer
#print axioms Synthesis.Millennium.BSD.cmGlobalKummerQuotientEquivExplicitSelmer
#print axioms Synthesis.Millennium.BSD.cmExplicitTwoSelmerCokernel_subsingleton
#print axioms Synthesis.Millennium.BSD.cmExplicitSelmerToActualE2H1_injective
#print axioms Synthesis.Millennium.BSD.cmActualE2H1ExplicitSelmerImage_eq_torsion
#print axioms Synthesis.Millennium.BSD.cmOriginalMordellWeilModuloTwo_card_eq_four
#print axioms Synthesis.Millennium.BSD.cmSelectedEBarRestrictedShaOne_mem_iff
#print axioms Synthesis.Millennium.BSD.cmSelectedBSDPeriodNormalization
#print axioms Synthesis.Millennium.BSD.cmEveryRationalPoint_modDoubles_eq_actual_twoTorsion
#print axioms Synthesis.Millennium.BSD.cmVanishingTwoTorsion_doesNotForceTrivialGroup
#print axioms Synthesis.Millennium.BSD.cmLevel32EtaProductTruncation_pos
#print axioms Synthesis.Millennium.BSD.cmEveryRationalPoint_eq_twoTorsion_add_double
#print axioms Synthesis.Millennium.BSD.cmSelectedOriginalMordellWeil_ZRank_zero
#print axioms Synthesis.Millennium.BSD.cmLevel32EtaAnalyticExpression_ne_zero
#print axioms Synthesis.Millennium.BSD.cmLevel32EtaAnalyticExpression_differentiableAt
#print axioms Synthesis.Millennium.BSD.cmSelectedGeometricKummerShortExact_group
EOF
echo 'LOCAL AXIOM INSPECTION: original source objects'
lake env lean "$tmp"

if [[ "${1:-}" == "--full" ]]; then
  echo 'LOCAL ROOT CHECK: Synthesis.lean'
  lake build Synthesis
fi

echo 'KERNEL MODULE BUILD AND AXIOM COMMAND COMPLETED. Inspect all axiom output before admission.'
echo 'Classical.choice and proof irrelevance are not substitute BSD mathematical assumptions.'
