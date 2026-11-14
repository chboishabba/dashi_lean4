#!/usr/bin/env bash
# FAIL-CLOSED, local-only selected BSD Lean kernel verifier.
# No CI, Docker, network or mutation of pinned repo files.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

repo_toolchain="$(tr -d '\r\n' < lean-toolchain)"
mathlib_rev="$(awk '
  /^name = "mathlib"$/ { in_mathlib=1; next }
  in_mathlib && /^rev = "/ {
    gsub(/"/, "", $3)
    print $3
    exit
  }
  in_mathlib && /^\[\[/ { in_mathlib=0 }
' lakefile.toml)"

if [[ "$mathlib_rev" != "v4.28.0" ]]; then
  echo "BLOCKED: unexpected pinned mathlib revision: $mathlib_rev" >&2
  exit 13
fi

expected_toolchain="leanprover/lean4:v4.28.0"
selected_toolchain="${LEAN_TOOLCHAIN:-$repo_toolchain}"
if [[ "$selected_toolchain" != "$expected_toolchain" ]]; then
  if [[ "${BSD_USE_MATHLIB_TOOLCHAIN:-0}" == "1" ]]; then
    export LEAN_TOOLCHAIN="$expected_toolchain"
    echo "Isolated toolchain override: $LEAN_TOOLCHAIN (no repo files changed)"
  else
    echo "BLOCKED: root toolchain $repo_toolchain does not match mathlib $mathlib_rev" >&2
    echo 'For an isolated local attempt use BSD_USE_MATHLIB_TOOLCHAIN=1' >&2
    exit 13
  fi
fi

if ! command -v lake >/dev/null 2>&1; then
  echo 'BLOCKED: lake unavailable; no Lean kernel acceptance performed.' >&2
  exit 12
fi

modules=(
  MillenniumBSDPinnedSquareCriterionV428Exact
  MillenniumBSDCMTwoAdicValuationArithmeticExact
  MillenniumBSDCMQ2ActualCurveValuationExact
  MillenniumBSDCMQ2SquareClassValuationParityExact
  MillenniumBSDCMQ2ActualLocalImageParityExact
  MillenniumBSDCMAllPrimeRationalSquareSupportExact
  MillenniumBSDCMAllPrimeLocalFirstParityExact
  MillenniumBSDCMOddPrimeLocalSecondParityExact
  MillenniumBSDCMOddPrimeRationalSquareSupportExact
  MillenniumBSDCMOriginalExplicitSelmerFourTorsionExact
  MillenniumBSDCMOriginalExplicitCokernelZeroExact
  MillenniumBSDCMActualE2H1ExplicitImageWeldExact
  MillenniumBSDCMOriginalMordellWeilModTwoCardExact
  MillenniumBSDCMActualEBarRestrictedShaTwoTargetExact
  MillenniumBSDCMSelectedPeriodNormalizationExact
  MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact
  MillenniumBSDCMShaTwoNotFullShaNegativeControlExact
  MillenniumBSDCMLevel32EtaFinitePositivityExact
  MillenniumBSDCMFGAbelianRankZeroFromModTwoExact
  MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact
  MillenniumBSDCMOriginalGeometricKummerGroupExact
  MillenniumBSDCMOriginalGeometricKummerGaloisEquivariantExact
  MillenniumBSDCMOriginalEbarDoublingTopRepExact
  MillenniumBSDCMUnitAreaTriangleCurveWeldExact
  MillenniumBSDCMCongruentOneRankReductionExact
  MillenniumBSDCMOriginalEbarTopRepUnderlyingExact
  MillenniumBSDCMLevel32GammaSpecialValuePositiveExact
  MillenniumBSDCMOriginalRationalToPadicH1NaturalityExact
  MillenniumBSDCMLevel32ImaginaryAxisPositivityFromRealnessExact
)

for module in "${modules[@]}"; do
  file="Synthesis/${module}.lean"
  if [[ ! -f "$file" ]]; then
    echo "BLOCKED: missing original source $file" >&2
    exit 11
  fi
  if grep -nE '(^|[[:space:]])sorry([[:space:]]|$)|(^|[[:space:]])admit([[:space:]]|$)' "$file"; then
    echo "BLOCKED: unfinished proof in $file" >&2
    exit 14
  fi
done

echo "Root toolchain: $repo_toolchain; selected: ${LEAN_TOOLCHAIN:-$repo_toolchain}; mathlib: $mathlib_rev"
echo "Checking ${#modules[@]} real original proof modules via local Lake."
for module in "${modules[@]}"; do
  echo "KERNEL BUILD: Synthesis.$module"
  lake build "Synthesis.$module"
done

audit_file="$(mktemp --tmpdir="$PWD" --suffix=.lean .bsd_axiom_audit_XXXXXXXX)"
audit_log="$(mktemp --tmpdir="$PWD" .bsd_axiom_log_XXXXXXXX)"
cleanup() {
  rm -f -- "$audit_file" "$audit_log"
}
trap cleanup EXIT
cat > "$audit_file" <<'LEAN'
import Synthesis.MillenniumBSDPinnedSquareCriterionV428Exact
import Synthesis.MillenniumBSDCMTwoAdicValuationArithmeticExact
import Synthesis.MillenniumBSDCMQ2ActualCurveValuationExact
import Synthesis.MillenniumBSDCMQ2SquareClassValuationParityExact
import Synthesis.MillenniumBSDCMQ2ActualLocalImageParityExact
import Synthesis.MillenniumBSDCMAllPrimeRationalSquareSupportExact
import Synthesis.MillenniumBSDCMAllPrimeLocalFirstParityExact
import Synthesis.MillenniumBSDCMOddPrimeLocalSecondParityExact
import Synthesis.MillenniumBSDCMOddPrimeRationalSquareSupportExact
import Synthesis.MillenniumBSDCMOriginalExplicitSelmerFourTorsionExact
import Synthesis.MillenniumBSDCMOriginalExplicitCokernelZeroExact
import Synthesis.MillenniumBSDCMActualE2H1ExplicitImageWeldExact
import Synthesis.MillenniumBSDCMOriginalMordellWeilModTwoCardExact
import Synthesis.MillenniumBSDCMActualEBarRestrictedShaTwoTargetExact
import Synthesis.MillenniumBSDCMSelectedPeriodNormalizationExact
import Synthesis.MillenniumBSDCMOriginalMWTwoTorsionRepresentativesExact
import Synthesis.MillenniumBSDCMShaTwoNotFullShaNegativeControlExact
import Synthesis.MillenniumBSDCMLevel32EtaFinitePositivityExact
import Synthesis.MillenniumBSDCMFGAbelianRankZeroFromModTwoExact
import Synthesis.MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact
import Synthesis.MillenniumBSDCMOriginalGeometricKummerGroupExact
import Synthesis.MillenniumBSDCMOriginalGeometricKummerGaloisEquivariantExact
import Synthesis.MillenniumBSDCMOriginalEbarDoublingTopRepExact
import Synthesis.MillenniumBSDCMUnitAreaTriangleCurveWeldExact
import Synthesis.MillenniumBSDCMCongruentOneRankReductionExact
import Synthesis.MillenniumBSDCMOriginalEbarTopRepUnderlyingExact
import Synthesis.MillenniumBSDCMLevel32GammaSpecialValuePositiveExact
import Synthesis.MillenniumBSDCMOriginalRationalToPadicH1NaturalityExact
import Synthesis.MillenniumBSDCMLevel32ImaginaryAxisPositivityFromRealnessExact
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
#print axioms Synthesis.Millennium.BSD.cmEbarDoublingTopRepHom_kernel_and_surjective
#print axioms Synthesis.Millennium.BSD.cmSelectedCongruentOne_iff_curve_nonTorsion
#print axioms Synthesis.Millennium.BSD.cmOriginalMordellWeil_ZRank_zero_of_noUnitAreaTriangle
#print axioms Synthesis.Millennium.BSD.cmEbarActualKummerShortExact_CLM
#print axioms Synthesis.Millennium.BSD.cmLevel32PublishedSpecialValueCandidate_pos
#print axioms Synthesis.Millennium.BSD.cmOriginalPoint_E2H1Restriction_eq_localXT
#print axioms Synthesis.Millennium.BSD.cmLevel32EtaAnalyticExpression_imaginary_pos_of_real
LEAN

echo 'AXIOM AUDIT: original selected-curve theorem declarations'
lake env lean "$audit_file" | tee "$audit_log"
if grep -E 'sorryAx|sorryAx\.|\bunsafe\b' "$audit_log"; then
  echo 'BLOCKED: suspicious axiom usage in local proof audit' >&2
  exit 15
fi

if [[ "${1:-}" == "--full" ]]; then
  echo 'ROOT KERNEL BUILD: Synthesis'
  lake build Synthesis
fi

echo 'LOCAL KERNEL COMMANDS FINISHED. Inspect standard axioms and capture exact source hashes.'
echo 'No claim is made that a passed subset proves Sha, analytic L(E,1), or universal BSD.'
