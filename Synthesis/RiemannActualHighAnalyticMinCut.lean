import Synthesis.RiemannCanonicalReflectionCoefficientGate
import Synthesis.RiemannSupportScaledTargetRemainder
import Synthesis.RiemannCenteredNearPairSign
import Synthesis.RiemannCenteredOffExplicitFarOnly
import Synthesis.RiemannFarShellDisplacementAdaptiveCutoff
import Synthesis.RiemannAdaptiveCutoffNearSignNoGo
import Synthesis.RiemannProjectiveCenteredGaugeBridge
import Synthesis.RiemannNormalizedCenteredOffTwoRadius
import Synthesis.RiemannNormalizedOffRadiusZeroAtomicMeasure
import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment
import Synthesis.RiemannNormalizedProjectiveRvMConsumer
import Synthesis.RiemannNormalizedProjectiveHorizontalQuadraticFactor
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

The displacement-adaptive real-analysis atom is now available, but it cannot be
plugged directly into the existing centered-near sign proof: the latter requires
J*Lambda <= pi/2, while the arbitrarily-large adaptive selector eventually has
pi/2 < J*Lambda.  On the canonical support Lambda=9*pi/(4*t), the sign window
forces J <= 2*t/9.

The next mathematical producer must therefore do at least one of:
1. retain an explicit a^2 factor in the literal far/projective residual while
   staying inside the cosine-sign window;
2. give a target-dependent taper whose support Lambda shrinks with a strongly
   enough that a large cutoff still satisfies J*Lambda <= pi/2;
3. expose additional exact signed cancellation beyond the first cosine sign
   change, eliminating the a-independent far term.

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
  displacementAdaptiveFarAtomPaid : Bool
  adaptiveCutoffDirectNearSignWeldPruned : Bool
  projectiveCenteredGaugeBridgePaid : Bool
  normalizedSecondRadiusAttachmentPaid : Bool
  normalizedRadiusZeroBaseAttachmentPaid : Bool
  literalInfiniteProjectiveTsumAttachmentPaid : Bool
  projectiveNormalizedHorizontalSplitPaid : Bool
  normalizedRvMProjectiveAttachmentPaid : Bool
  projectiveWholeLineZeroModePaid : Bool
  projectivePhysicalDomainTailIdentityPaid : Bool
  projectivePhysicalConstantModeCancellationPaid : Bool
  projectiveHorizontalQuadraticFactorPaid : Bool

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
    displacementAdaptiveFarAtomPaid := true
    adaptiveCutoffDirectNearSignWeldPruned := true
    projectiveCenteredGaugeBridgePaid := true
    normalizedSecondRadiusAttachmentPaid := true
    normalizedRadiusZeroBaseAttachmentPaid := true
    literalInfiniteProjectiveTsumAttachmentPaid := true
    projectiveNormalizedHorizontalSplitPaid := true
    normalizedRvMProjectiveAttachmentPaid := false
    projectiveWholeLineZeroModePaid := true
    projectivePhysicalDomainTailIdentityPaid := true
    projectivePhysicalConstantModeCancellationPaid := false
    projectiveHorizontalQuadraticFactorPaid := true

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


theorem projectiveCenteredGaugeBridgeNowPaid :
    actualHighAnalyticMinCutStatus.projectiveCenteredGaugeBridgePaid = true :=
  rfl

theorem normalizedSecondRadiusAttachmentNowPaid :
    actualHighAnalyticMinCutStatus.normalizedSecondRadiusAttachmentPaid = true :=
  rfl

theorem literalInfiniteProjectiveTsumAttachmentNowPaid :
    actualHighAnalyticMinCutStatus.literalInfiniteProjectiveTsumAttachmentPaid = true :=
  rfl

theorem projectiveNormalizedHorizontalSplitNowPaid :
    actualHighAnalyticMinCutStatus.projectiveNormalizedHorizontalSplitPaid = true :=
  rfl

theorem normalizedRvMProjectiveAttachmentStillOpen :
    actualHighAnalyticMinCutStatus.normalizedRvMProjectiveAttachmentPaid = false :=
  rfl

theorem projectiveWholeLineZeroModeNowPaid :
    actualHighAnalyticMinCutStatus.projectiveWholeLineZeroModePaid = true :=
  rfl

theorem projectivePhysicalDomainTailIdentityNowPaid :
    actualHighAnalyticMinCutStatus.projectivePhysicalDomainTailIdentityPaid = true :=
  rfl

theorem projectivePhysicalConstantModeCancellationStillOpen :
    actualHighAnalyticMinCutStatus.projectivePhysicalConstantModeCancellationPaid = false :=
  rfl

theorem projectiveHorizontalQuadraticFactorNowPaid :
    actualHighAnalyticMinCutStatus.projectiveHorizontalQuadraticFactorPaid = true :=
  rfl


theorem normalizedRadiusZeroBaseAttachmentNowPaid :
    actualHighAnalyticMinCutStatus.normalizedRadiusZeroBaseAttachmentPaid = true :=
  rfl
