import Synthesis.RiemannCanonicalReflectionCoefficientGate
import Synthesis.RiemannSupportScaledTargetRemainder
import Synthesis.RiemannCenteredNearPairSign
import Synthesis.RiemannCenteredOffExplicitFarOnly
import Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

/-!
# Current hard analytic min-cut after actual inhabitant construction

The high-side representation debt is now paid far enough to expose the genuine
analytic obstruction.

Paid:
* actual functional-equation reflection partner at the same ordinate;
* exact proof that the partner has the same two-radius response and therefore
  doubles, rather than contaminates, the target signal;
* C^2/even/short normalized window inhabitants;
* the exact quantitative canonical pole-killing taper as GateData;
* explicit positive leading signal floor on that same canonical taper;
* arbitrary-radius Taylor remainder (the old r<=1 premise was an artifact);
* support-scaled remainder bounds;
* favorable sign of the centered near off-ordinate reflection-pair core.

The remaining issue is not merely "bound a residual".  The exact height detector
has signal D(a,0) with D(0,0)=0, while the current far-shell curvature envelope is
uniform in |a|<=1/2 and does not retain that vanishing.  Therefore a fixed
a-independent positive far budget cannot be compared uniformly against the
near-line signal.

The next mathematical producer must do at least one of:
1. retain an explicit a^2 factor in the far/projective residual;
2. give a target-dependent taper/cutoff whose residual shrinks with a;
3. expose an additional exact signed cancellation eliminating the a-independent
   far term.

This file is a status firewall: it prevents the uniform curvature bound from
being mistaken for a prize-facing near-line closure.
-/

namespace Synthesis

structure ActualHighAnalyticMinCutStatus where
  reflectionPartnerInhabited : Bool
  reflectionSignalDoublingPaid : Bool
  canonicalGateDataPaid : Bool
  canonicalSignalFloorPaid : Bool
  arbitraryRadiusRemainderPaid : Bool
  supportScaledRemainderPaid : Bool
  centeredNearOffSignPaid : Bool
  centeredFarOnlyReductionPaid : Bool

  farResidualRetainsHeightSquare : Bool
  targetDependentResidualSuppressionPaid : Bool
  exactFarCancellationPaid : Bool
  uniformNearLineClosurePaid : Bool

def actualHighAnalyticMinCutStatus : ActualHighAnalyticMinCutStatus :=
  { reflectionPartnerInhabited := true
    reflectionSignalDoublingPaid := true
    canonicalGateDataPaid := true
    canonicalSignalFloorPaid := true
    arbitraryRadiusRemainderPaid := true
    supportScaledRemainderPaid := true
    centeredNearOffSignPaid := true
    centeredFarOnlyReductionPaid := true

    farResidualRetainsHeightSquare := false
    targetDependentResidualSuppressionPaid := false
    exactFarCancellationPaid := false
    uniformNearLineClosurePaid := false }

theorem highSignalVanishesAtZeroHeight
    (g : ℝ → ℝ) (r : ℝ) :
    Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect
      g r 0 0 = 0 :=
  Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect_self g r 0

theorem uniformNearLineClosureStillOpen :
    actualHighAnalyticMinCutStatus.uniformNearLineClosurePaid = false :=
  rfl

end Synthesis
