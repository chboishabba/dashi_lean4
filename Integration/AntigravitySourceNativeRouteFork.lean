import Integration.AntigravityOverlayZMirror

namespace Integration.AntigravitySourceNativeRouteFork

/-!
Structural mirror of the Agda source-native shortest-path recut.

The previously exposed source->Israel admission seam and finite->R136 response
same-object seam are alternative closure routes, not conjunctive obligations.
This file mirrors only that scheduling fact.  It does not manufacture source
values, R136 equality, SI calibration, or a physical antigravity theorem.
-/

structure VacuumIsraelRouteBoundary where
  sourceVacuumReadoutAlreadyOwned : Bool
  cosmologicalStressShapeAlreadyOwned : Bool
  thinWallIsraelGeometryAlreadyOwned : Bool
  sourceVacuumIsraelAdmissionRequired : Bool
  r136FiniteContinuumResponseWeldRequired : Bool
  finiteThicknessWallRequired : Bool
  sourceNativePotentialDynamicsRequired : Bool
  physicalCalibrationRequired : Bool
  deriving Repr, DecidableEq

def canonicalVacuumIsraelRouteBoundary : VacuumIsraelRouteBoundary where
  sourceVacuumReadoutAlreadyOwned := true
  cosmologicalStressShapeAlreadyOwned := true
  thinWallIsraelGeometryAlreadyOwned := true
  sourceVacuumIsraelAdmissionRequired := true
  r136FiniteContinuumResponseWeldRequired := false
  finiteThicknessWallRequired := false
  sourceNativePotentialDynamicsRequired := false
  physicalCalibrationRequired := true

structure ContinuumStressRouteBoundary where
  literalEq223MetricVariationAlreadyOwned : Bool
  r136StressRecoverySurfaceAlreadyOwned : Bool
  directFiniteContinuumResponseWeldRequired : Bool
  sourceVacuumIsraelAdmissionRequired : Bool
  fixedVacuumAmplitudePairRequired : Bool
  newIsraelGeometryRequired : Bool
  physicalContinuationCalibrationRequired : Bool
  deriving Repr, DecidableEq

def canonicalContinuumStressRouteBoundary : ContinuumStressRouteBoundary where
  literalEq223MetricVariationAlreadyOwned := true
  r136StressRecoverySurfaceAlreadyOwned := true
  directFiniteContinuumResponseWeldRequired := true
  sourceVacuumIsraelAdmissionRequired := false
  fixedVacuumAmplitudePairRequired := false
  newIsraelGeometryRequired := false
  physicalContinuationCalibrationRequired := true

def thinWallVacuumRouteRequiresR136ResponseWeld : Bool := false

def continuumStressRouteRequiresSourceVacuumIsraelAdmission : Bool := false

def sourceToGeometryAdmissionAndR136AreAlternativePayments : Bool := true

def finiteThicknessWallRequiredForThinWallClosure : Bool := false

def sourceNativePotentialDynamicsRequiredForThinWallClosure : Bool := false

structure VacuumIsraelShortestPathLeaves : Prop where
  actualSelectedSourceVacuaLandInAdmissibleIsraelRegion : Prop
  physicalControlAndSICalibration : Prop
  experimentalRealisation : Prop

structure ContinuumStressShortestPathLeaves : Prop where
  finiteEffectiveActionResponseIsSameR136Response : Prop
  euclideanLorentzianAndStressConventionCalibration : Prop
  physicalControlAndSICalibration : Prop
  experimentalRealisation : Prop

/-- The route recut is scheduling-only: physical source mathematics remains. -/
def noPhysicalPaymentPromotedByScheduler : Bool := true

end Integration.AntigravitySourceNativeRouteFork
