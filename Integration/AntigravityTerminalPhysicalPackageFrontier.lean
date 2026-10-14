import Integration.AntigravityR136StaticDifferentialReuse

namespace Integration.AntigravityTerminalPhysicalPackageFrontier

open Integration.AntigravityR136StaticDifferentialReuse

/-!
Package-level mirror of the terminal Agda antigravity frontier.

This is scheduling/parity only.  Lean does not claim the Agda pinned Local-C
terminal proof objects, measured-G authority, physical source scale, TT device
identity or laboratory receipts.

Mandatory for static and scalar differential response:
  P1 typed pinned Local-C terminal;
  P2 common gravitational calibration/renormalization;
  P3 matched experimental package.

Only a propagating Schuetzhold/GW claim adds:
  P4 TT/device same-object package.
-/

def typedLocalCTerminalPhysicalPackageStillRequired : Bool :=
  typedPinnedLocalCTerminalProducerRequired

def commonGravityCalibrationPackageStillRequired : Bool := true

def matchedExperimentPackageStillRequired : Bool := true

def ttDevicePackageRequiredForStaticOrScalarDifferentialRoute : Bool := false

def ttDevicePackageRequiredWhenPropagatingGWRouteSelected : Bool := true

def independentStaticMetricResponseTheoremStillRequired : Bool :=
  independentStaticMetricResponseReceiptRequiredAfterR136Promotion

def independentDifferentialSameObjectTheoremStillRequired : Bool :=
  independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair

def r109SignMachineryRequiredForResponseReuse : Bool := false

def representationOnlyAdapterDebtRemains : Bool := false

/-- Internal TT first-variation pairing is compiler-owned after the metric
and stress same-object identifications; it is not a fourth TT project. -/
def independentTTFirstVariationPairingProjectRequired : Bool :=
  sameFirstVariationPairingStillRequired

/-- The terminal package still contains the two genuine Agda physical producers:
boost covariance and same-object Euclidean/Lorentzian trace continuation. -/
def typedTerminalInternallyNeedsBoostAndTraceContinuation : Bool := true

def gravityCalibrationInternallyNeedsAcceptedGAndStressLengthSquared : Bool :=
  acceptedMeasuredGAuthorityStillRequired && sourceStressLengthSquaredScaleStillRequired

def matchedExperimentInternallyNeedsPhysicalSwitchAndSystematics : Bool :=
  physicalMatchedSourceSwitchStillRequired && numericalSystematicsBudgetStillRequired

def mandatoryStaticResponsePhysicalPackageCount : Nat := 3

def mandatoryScalarDifferentialPhysicalPackageCount : Nat := 3

def mandatoryPropagatingGWPhysicalPackageCount : Nat := 4

structure TerminalPhysicalPackageFrontier where
  typedLocalCTerminalOpen : Bool
  commonGravityCalibrationOpen : Bool
  matchedExperimentOpen : Bool
  ttPackageOpenForScalarRoute : Bool
  ttPackageOpenForGWRoute : Bool
  extraStaticMetricResponseOpen : Bool
  extraDifferentialSameObjectOpen : Bool
  r109SignMachineryRechargedForResponseReuse : Bool
  representationAdapterDebtOpen : Bool
  staticPackageCount : Nat
  scalarDifferentialPackageCount : Nat
  propagatingGWPackageCount : Nat
  deriving Repr, DecidableEq

def canonicalTerminalPhysicalPackageFrontier : TerminalPhysicalPackageFrontier where
  typedLocalCTerminalOpen := true
  commonGravityCalibrationOpen := true
  matchedExperimentOpen := true
  ttPackageOpenForScalarRoute := false
  ttPackageOpenForGWRoute := true
  extraStaticMetricResponseOpen := false
  extraDifferentialSameObjectOpen := false
  r109SignMachineryRechargedForResponseReuse := false
  representationAdapterDebtOpen := false
  staticPackageCount := 3
  scalarDifferentialPackageCount := 3
  propagatingGWPackageCount := 4

end Integration.AntigravityTerminalPhysicalPackageFrontier
