import Synthesis.RiemannConstructedSmoothShortWindowSchur
import Synthesis.RiemannHighOneZeroSchurCutset
import Synthesis.RiemannHighDeterministicSchurNoGo

/-!
# Current corrected RH high-side Schur frontier

This is the canonical status owner after the deterministic-Schur no-go and the
smooth short-window repair.

Paid:
  * deterministic pole/Gamma strict-comparison route is formally impossible;
  * C^2 even normalized windows exist below log 2;
  * localized response-ratio separation survives on those exact smooth windows;
  * the target survives exact removal of a selected distinct-height zero response;
  * the projected target carries the canonical positive energy ||T_perp||^2;
  * the exact projected literal balance is compiled to a signed residual consumer.

Still open:
  * selecting/organizing nuisance zeros on the actual same-ordinate carrier when
    useful;
  * bounding the remaining signed same-ordinate residual;
  * bounding the projected off-ordinate/Gamma/pole residual on the same tapers;
  * combining those budgets below ||T_perp||^2 uniformly in the prize-facing
    high region.

The same-ordinate carrier is presently a summable/tsum object, not a proven finite
enumeration, so recursive deletion of every nuisance is not asserted here.
-/

noncomputable section

namespace Synthesis

structure CorrectedHighSchurFrontierStatus where
  deterministicSchurStrictGatePruned : Bool
  smoothC2EvenNormalizedWindowsConstructed : Bool
  smoothWindowsShortBelowLogTwo : Bool
  localizedWindowSeparationOnSmoothWindows : Bool
  zeroResponseTargetSurvivalCompilerPaid : Bool
  exactProjectedBalancePaid : Bool
  canonicalTargetEnergyPaid : Bool

  actualNuisanceSelectionPaid : Bool
  sameOrdSignedResidualBoundPaid : Bool
  externalProjectedResidualBoundPaid : Bool
  uniformBudgetBelowTargetEnergyPaid : Bool
  prizeFacingHighContradictionPaid : Bool

def correctedHighSchurFrontierStatus : CorrectedHighSchurFrontierStatus :=
  { deterministicSchurStrictGatePruned := true
    smoothC2EvenNormalizedWindowsConstructed := true
    smoothWindowsShortBelowLogTwo := true
    localizedWindowSeparationOnSmoothWindows := true
    zeroResponseTargetSurvivalCompilerPaid := true
    exactProjectedBalancePaid := true
    canonicalTargetEnergyPaid := true

    actualNuisanceSelectionPaid := false
    sameOrdSignedResidualBoundPaid := false
    externalProjectedResidualBoundPaid := false
    uniformBudgetBelowTargetEnergyPaid := false
    prizeFacingHighContradictionPaid := false }

theorem smoothWindowRepresentationDebtPaid :
    correctedHighSchurFrontierStatus.smoothC2EvenNormalizedWindowsConstructed = true :=
  rfl

theorem deterministicStrictGateIsNotFrontier :
    correctedHighSchurFrontierStatus.deterministicSchurStrictGatePruned = true :=
  rfl

theorem signedProjectedResidualStillOpen :
    correctedHighSchurFrontierStatus.uniformBudgetBelowTargetEnergyPaid = false :=
  rfl

end Synthesis
