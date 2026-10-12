import Integration.AntigravitySingleVacuumPhysicalMaxCut

namespace Integration.AntigravityVacuumControlCoordinateMaxCut

/-!
Structural Lean mirror of the Agda vacuum experimental-coordinate/control cut.

The Agda owner proves that the current coupling+density/background/fluctuation+
E/R/B source view admits a collision separated by the projected-vacuum
coordinate.  Lean mirrors only the scheduling consequence:

* the missing coordinate is explicit;
* a useful selective control must preserve the declared current source view;
* that same control must change the calibrated vacuum coordinate;
* such a control would produce the nonzero OFF/ON source pair required by the
  differential lane;
* existence/calibration of a physical actuator/observable is not promoted.
-/

structure VacuumExperimentalCoordinateBoundary where
  missingVacuumCoordinateIdentified : Bool
  canonicalCollisionSeparatedByVacuumCoordinate : Bool
  currentSourceViewAloneCanRecoverVacuum : Bool
  formalProjectedVacuumAlreadyCalibratedLabObservable : Bool
  deriving Repr, DecidableEq

def canonicalVacuumExperimentalCoordinateBoundary :
    VacuumExperimentalCoordinateBoundary where
  missingVacuumCoordinateIdentified := true
  canonicalCollisionSeparatedByVacuumCoordinate := true
  currentSourceViewAloneCanRecoverVacuum := false
  formalProjectedVacuumAlreadyCalibratedLabObservable := false

structure VacuumSelectiveControlBoundary where
  selectiveControlMustPreserveCurrentSourceView : Bool
  selectiveControlMustChangeVacuumCoordinate : Bool
  selectiveControlWouldProduceNonzeroSourcePair : Bool
  physicalSelectiveControlAlreadyConstructed : Bool
  physicalVacuumCoordinateCalibrationStillRequired : Bool
  deriving Repr, DecidableEq

def canonicalVacuumSelectiveControlBoundary : VacuumSelectiveControlBoundary where
  selectiveControlMustPreserveCurrentSourceView := true
  selectiveControlMustChangeVacuumCoordinate := true
  selectiveControlWouldProduceNonzeroSourcePair := true
  physicalSelectiveControlAlreadyConstructed := false
  physicalVacuumCoordinateCalibrationStillRequired := true

-- Regression-friendly exports.
def vacuumSelectiveControlTargetCompiled : Bool := true
def physicalVacuumSelectiveControlStillRequired : Bool := true
def selectiveControlMustPreserveCurrentSourceView : Bool := true
def selectiveControlMustChangeVacuumCoordinate : Bool := true
def selectiveControlWouldProduceNonzeroSourcePair : Bool := true
def formalProjectedVacuumAlreadyCalibratedLabObservable : Bool := false

def mirrorDoesNotConstructPhysicalActuator : Bool := true

end Integration.AntigravityVacuumControlCoordinateMaxCut
