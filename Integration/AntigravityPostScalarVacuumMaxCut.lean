import Integration.AntigravityVacuumControlCoordinateMaxCut

namespace Integration.AntigravityPostScalarVacuumMaxCut

/-!
Structural mirror of the Agda post-scalar-vacuum physical frontier.

Lean does not reproduce the Agda source proof.  It mirrors the corrected
promotion boundary:

  finite vacuum scalar
    -> same extensive/local density coefficient times metric volume
    -> metric-family differentiability of the renormalized effective action
    -> same-state renormalized local stress
    -> fixed cosmological/Wald convention
    -> same-state Euclidean/Lorentzian continuation.

A scalar normalization constant by itself is not promoted to a cosmological
stress or physical Lambda.
-/

structure VacuumExtensivityBoundary where
  scalarVacuumRepresentationOwned : Bool
  betaAndNormalizationCoordinatesComplementary : Bool
  finiteScalarAloneDeterminesCosmologicalStress : Bool
  extensivityVolumeWeldStillRequired : Bool
  latticeToPhysicalVolumeNormalizationStillRequired : Bool
  deriving Repr, DecidableEq

def canonicalVacuumExtensivityBoundary : VacuumExtensivityBoundary where
  scalarVacuumRepresentationOwned := true
  betaAndNormalizationCoordinatesComplementary := true
  finiteScalarAloneDeterminesCosmologicalStress := false
  extensivityVolumeWeldStillRequired := true
  latticeToPhysicalVolumeNormalizationStillRequired := true

structure PostScalarVacuumPhysicalBoundary where
  metricFamilyDifferentiabilityStillRequired : Bool
  sameStateRenormalizedMetricResponseStillRequired : Bool
  normalizationToGravityCalibrationStillRequired : Bool
  cosmologicalWaldRenormalizationStillRequired : Bool
  sameStateEuclideanLorentzianContinuationStillRequired : Bool
  moreVacuumProjectorPlumbingCountsAsProgress : Bool
  deriving Repr, DecidableEq

def canonicalPostScalarVacuumPhysicalBoundary :
    PostScalarVacuumPhysicalBoundary where
  metricFamilyDifferentiabilityStillRequired := true
  sameStateRenormalizedMetricResponseStillRequired := true
  normalizationToGravityCalibrationStillRequired := true
  cosmologicalWaldRenormalizationStillRequired := true
  sameStateEuclideanLorentzianContinuationStillRequired := true
  moreVacuumProjectorPlumbingCountsAsProgress := false

-- Regression-friendly exports.
def finiteScalarAloneDeterminesCosmologicalStress : Bool := false
def extensivityVolumeWeldStillRequired : Bool := true
def latticeToPhysicalVolumeNormalizationStillRequired : Bool := true
def metricFamilyDifferentiabilityStillRequired : Bool := true
def sameStateRenormalizedMetricResponseStillRequired : Bool := true
def cosmologicalWaldRenormalizationStillRequired : Bool := true
def sameStateEuclideanLorentzianContinuationStillRequired : Bool := true
def moreVacuumProjectorPlumbingCountsAsProgress : Bool := false

def mirrorDoesNotPromoteVacuumScalarToGravity : Bool := true

end Integration.AntigravityPostScalarVacuumMaxCut
