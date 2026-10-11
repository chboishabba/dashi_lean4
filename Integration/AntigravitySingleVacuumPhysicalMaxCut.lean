import Integration.AntigravitySourceNativeRouteFork

namespace Integration.AntigravitySingleVacuumPhysicalMaxCut

/-!
Structural mirror of the latest Agda source-native single-vacuum recut.

Lean records scheduling/non-promotion only.  The constructive Agda proof that the
current coupling/E/R/B source view does not determine the projected vacuum
sequence remains Agda-owned, as does the positive-rational normalization proof.
-/

structure SourceVacuumInformationBoundary where
  sourceVacuumReadoutOwned : Bool
  couplingAndERBDetermineVacuumSequence : Bool
  sourceVacuumRequiresIndependentPhysicalPayment : Bool
  deriving Repr, DecidableEq

def canonicalSourceVacuumInformationBoundary : SourceVacuumInformationBoundary where
  sourceVacuumReadoutOwned := true
  couplingAndERBDetermineVacuumSequence := false
  sourceVacuumRequiresIndependentPhysicalPayment := true

structure StaticSingleVacuumRouteBoundary where
  oneSourceScaleSuffices : Bool
  secondVacuumAmplitudeRequired : Bool
  positiveSourceNormalizedStaticGeometryOwned : Bool
  rationalSquareDensityRequired : Bool
  staticRouteNeedsPositivePromotedVacuumSign : Bool
  physicalCalibrationValueStillExternal : Bool
  absoluteSIDeviceScaleStillExternal : Bool
  r136ResponseWeldRequired : Bool
  deriving Repr, DecidableEq

def canonicalStaticSingleVacuumRouteBoundary : StaticSingleVacuumRouteBoundary where
  oneSourceScaleSuffices := true
  secondVacuumAmplitudeRequired := false
  positiveSourceNormalizedStaticGeometryOwned := true
  rationalSquareDensityRequired := false
  staticRouteNeedsPositivePromotedVacuumSign := true
  physicalCalibrationValueStillExternal := true
  absoluteSIDeviceScaleStillExternal := true
  r136ResponseWeldRequired := false

structure DifferentialVacuumRouteBoundary where
  commonAdditiveCountertermCancels : Bool
  differentialRouteNeedsStaticAdditiveZero : Bool
  differentialRouteNeedsNonzeroSourceDifference : Bool
  multiplicativeCalibrationStillRequired : Bool
  scalarMetricResponseOwned : Bool
  scalarMetricResponseIsAlreadySchutzholdTTMode : Bool
  deriving Repr, DecidableEq

def canonicalDifferentialVacuumRouteBoundary : DifferentialVacuumRouteBoundary where
  commonAdditiveCountertermCancels := true
  differentialRouteNeedsStaticAdditiveZero := false
  differentialRouteNeedsNonzeroSourceDifference := true
  multiplicativeCalibrationStillRequired := true
  scalarMetricResponseOwned := true
  scalarMetricResponseIsAlreadySchutzholdTTMode := false

structure ContinuumStressRouteBoundary where
  finiteOnePointOrientationOwned : Bool
  sameR136StressPairingSurfaceOwned : Bool
  directFiniteContinuumSameObjectPaymentRequired : Bool
  euclideanLorentzianSameStateContinuationRequired : Bool
  staticVacuumGeometryRequired : Bool
  deriving Repr, DecidableEq

def canonicalContinuumStressRouteBoundary : ContinuumStressRouteBoundary where
  finiteOnePointOrientationOwned := true
  sameR136StressPairingSurfaceOwned := true
  directFiniteContinuumSameObjectPaymentRequired := true
  euclideanLorentzianSameStateContinuationRequired := true
  staticVacuumGeometryRequired := false

/-- Current three-way source-native fork. -/
inductive SourceNativeRoute where
  | staticSingleVacuum
  | differentialVacuum
  | continuumStress
  deriving Repr, DecidableEq

structure RemainingPhysicalPayments where
  sourceVacuumValueOrControlledDifference : Prop
  sameStatePhysicalContinuationOrCalibration : Prop
  absoluteSIOrSignalCalibration : Prop
  dynamicModeOrExperimentalRealisation : Prop

-- Regression-friendly exported boundaries.
def couplingAndERBDetermineVacuumSequence : Bool := false
def sourceVacuumRequiresIndependentPhysicalPayment : Bool := true
def positiveSourceNormalizedStaticGeometryOwned : Bool := true
def rationalSquareDensityRequired : Bool := false
def staticRouteNeedsPositivePromotedVacuumSign : Bool := true
def differentialRouteNeedsNonzeroSourceDifference : Bool := true
def staticRouteRequiresR136Weld : Bool := false
def differentialRouteRequiresStaticAdditiveZero : Bool := false
def continuumRouteRequiresStaticVacuumGeometry : Bool := false

/-- No source value, continuation theorem, SI calibration, or experiment is
promoted merely by this scheduling mirror. -/
def noPhysicalPaymentPromotedByMirror : Bool := true

end Integration.AntigravitySingleVacuumPhysicalMaxCut
