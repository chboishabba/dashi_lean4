import Mathlib

namespace Integration.AntigravityR136StaticDifferentialReuse

/-!
Structural Lean mirror of the current Agda post-normalization reuse cut.

This file does not import Agda proof objects or assert physical source authority.
It mirrors only the consumer shape:

* one same-state R136/Local-C vacuum endpoint plus an affine V -> rho map can
  discharge the static metric-response consumer;
* two such endpoints under one shared affine calibration/common convention give
  Delta Lambda = a (V_on - V_off), so no extra Delta same-object theorem is
  scheduled;
* scalar Kottler modulation is not a propagating TT mode;
* the open TT donor leaves are the literal GW tangent, EM Hilbert stress, and
  localized interaction same-object welds; the first-variation pairing follows
  from the canonical metric-stress theorem after tangent/stress identification;
* Agda now has a source-attributed NIST/CODATA-2022 measured-G admission and a
  typed accepted physical Einstein-coupling receipt, so measured-G authority is
  not an open SI leaf for this consumer;
* the remaining SI leaf is the source/device stress*length^2 scale. Separate
  stress and length scales are not independently required by the consumer;
* on the preferred Agda route the R136/Local-C source is the actual typed pinned
  terminal producer, not an arbitrary proposition receipt. Lean mirrors that
  scheduling fact without claiming the Agda terminal proof object;
* experiment design uses synchronous source-state modulation with conventional
  stress/geometry rematching, null/calibration channels and preregistration;
  numerical systematics closure and a physical matched source switch remain.
-/

structure R136StaticVacuumPromotionInput where
  sourceNormalization : Rat
  lorentzianVacuumRho : Rat
  normalizationToGravityScale : Rat
  additiveGravityRenormalization : Rat
  vacuumRhoUsesAffineCalibration :
    lorentzianVacuumRho =
      normalizationToGravityScale * sourceNormalization
        + additiveGravityRenormalization
  sameStateR136LocalCReceipt : Prop
  cosmologicalRenormalizationConvention : Prop

structure CommonR136AffineVacuumPair where
  sourceOff : Rat
  sourceOn : Rat
  rhoOff : Rat
  rhoOn : Rat
  scale : Rat
  additive : Rat
  offAffine : rhoOff = scale * sourceOff + additive
  onAffine : rhoOn = scale * sourceOn + additive
  offSameStateR136Receipt : Prop
  onSameStateR136Receipt : Prop
  commonCosmologicalRenormalizationConvention : Prop

def physicalDeltaLambda (pair : CommonR136AffineVacuumPair) : Rat :=
  pair.rhoOn - pair.rhoOff

theorem r136_pair_delta_lambda_is_calibrated_source_difference
    (pair : CommonR136AffineVacuumPair) :
    physicalDeltaLambda pair = pair.scale * (pair.sourceOn - pair.sourceOff) := by
  unfold physicalDeltaLambda
  rw [pair.onAffine, pair.offAffine]
  ring

def r136VacuumReadoutCanProduceStaticPromotion : Bool := true
def independentStaticMetricResponseReceiptRequiredAfterR136Promotion : Bool := false
def r136CommonPairCanProduceDifferentialPromotion : Bool := true
def independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair : Bool := false
def sharedAffineCalibrationStillRequired : Bool := true
def commonRenormalizationConventionStillRequired : Bool := true

-- Preferred source typing parity: Agda now has a direct adapter from the actual
-- `PinnedLocalCTerminalProducers` package. These flags record scheduling only.
def softR136SameStateTokenRequiredOnTypedRoute : Bool := false
def typedPinnedLocalCTerminalProducerRequired : Bool := true

-- TT donor boundary cross-pollinated from the open Agda Schützhold/R144 lane.
-- These booleans are scheduling mirrors only.
def newMaxwellTheoryRequired : Bool := false
def newMetricDependentHodgeTheoryRequired : Bool := false
def newR144FirstVariationFrameworkRequired : Bool := false
def sameGWMetricTangentStillRequired : Bool := true
def sameEMHilbertStressInsertionStillRequired : Bool := true
def sameFirstVariationPairingStillRequired : Bool := false
def sameLocalizedInteractionStillRequired : Bool := true
def physicalReversalAndConservationReceiptsStillRequired : Bool := true
def scalarKottlerDeltaGttAloneConstructsTTMode : Bool := false

-- Least-privilege SI calibration mirror. Agda now owns the explicit consumer
-- admission of the CODATA/NIST measured-G value with uncertainty.
def vendoredCODATAEinsteinCouplingCandidateAvailable : Bool := true
def exactSpeedOfLightIsNotCalibrationBlocker : Bool := true
def newEinsteinCouplingConventionRequired : Bool := false
def acceptedMeasuredGAuthorityStillRequired : Bool := false
def acceptedPhysicalEinsteinCouplingAvailable : Bool := true
def sourceStressLengthSquaredScaleStillRequired : Bool := true
def separateStressAndLengthIdentificationRequired : Bool := false

-- Generic matched-control laboratory discipline cross-pollinated from the open
-- birthmark systematics lane without identifying birthmark history with CMP119.
def sourceStateSwitchIsSynchronousModulationChannel : Bool := true
def conventionalStressRematchingRequired : Bool := true
def massGeometryPositionControlRequired : Bool := true
def electromagneticControlRequired : Bool := true
def thermalMechanicalOpticalVibrationControlRequired : Bool := true
def nullPreparationChannelRequired : Bool := true
def calibrationSignalRequired : Bool := true
def preregisteredAnalysisRequired : Bool := true
def numericalSystematicsBudgetStillRequired : Bool := true
def physicalMatchedSourceSwitchStillRequired : Bool := true
def birthmarkHistoryIdentifiedWithCMP119VacuumCoordinate : Bool := false

end Integration.AntigravityR136StaticDifferentialReuse
