import Integration.AntigravitySingleVacuumPhysicalMaxCut

namespace Integration.AntigravityVacuumControlCoordinateMaxCut

/-!
Structural Lean mirror of the Agda vacuum representation + experimental-control
cut.  Lean mirrors scheduling/non-promotion only, not Agda proof objects.

The corrected Agda source-first route uses the CMP119 source carrier's separate
Vacuum type as a scalar and embeds it into the LocalizedAction constant/remainder
coordinate by construction.  The older all-LocalizedAction route remains a
compatibility path requiring a post-hoc source-encoding receipt.

The experimental consequence is unchanged but sharper:
* beta/plaquette projection cannot recover a pure vacuum constant;
* the complementary vacuum coordinate is explicit;
* a useful selective control must preserve the declared current source view;
* that same control must change the calibrated vacuum coordinate;
* such a control would produce the nonzero OFF/ON pair required downstream;
* no physical actuator, metric response or cosmological Lambda is manufactured.
-/

structure VacuumRepresentationBoundary where
  preferredVacuumTypeIsIndependentScalar : Bool
  scalarVacuumEmbeddedAsConstantRemainderByConstruction : Bool
  plaquetteProjectorUsedAsVacuumConstantReadout : Bool
  postHocEncodingReceiptRequiredOnPreferredRoute : Bool
  scalarVacuumRepresentationAloneIdentifiesPhysicalLambda : Bool
  betaPlaquetteProjectionCanRecoverPureVacuumConstant : Bool
  deriving Repr, DecidableEq

def canonicalVacuumRepresentationBoundary : VacuumRepresentationBoundary where
  preferredVacuumTypeIsIndependentScalar := true
  scalarVacuumEmbeddedAsConstantRemainderByConstruction := true
  plaquetteProjectorUsedAsVacuumConstantReadout := false
  postHocEncodingReceiptRequiredOnPreferredRoute := false
  scalarVacuumRepresentationAloneIdentifiesPhysicalLambda := false
  betaPlaquetteProjectionCanRecoverPureVacuumConstant := false

structure VacuumExperimentalCoordinateBoundary where
  missingVacuumCoordinateIdentified : Bool
  canonicalCollisionSeparatedByVacuumCoordinate : Bool
  currentSourceViewAloneCanRecoverVacuum : Bool
  selectedCoordinateIsConstantRemainderNotPlaquette : Bool
  formalProjectedVacuumAlreadyCalibratedLabObservable : Bool
  deriving Repr, DecidableEq

def canonicalVacuumExperimentalCoordinateBoundary :
    VacuumExperimentalCoordinateBoundary where
  missingVacuumCoordinateIdentified := true
  canonicalCollisionSeparatedByVacuumCoordinate := true
  currentSourceViewAloneCanRecoverVacuum := false
  selectedCoordinateIsConstantRemainderNotPlaquette := true
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
def preferredVacuumTypeIsIndependentScalar : Bool := true
def scalarVacuumEmbeddedAsConstantRemainderByConstruction : Bool := true
def plaquetteProjectorUsedAsVacuumConstantReadout : Bool := false
def postHocEncodingReceiptRequiredOnPreferredRoute : Bool := false
def scalarVacuumRepresentationAloneIdentifiesPhysicalLambda : Bool := false
def betaPlaquetteProjectionCanRecoverPureVacuumConstant : Bool := false

def vacuumSelectiveControlTargetCompiled : Bool := true
def physicalVacuumSelectiveControlStillRequired : Bool := true
def selectiveControlMustPreserveCurrentSourceView : Bool := true
def selectiveControlMustChangeVacuumCoordinate : Bool := true
def selectiveControlWouldProduceNonzeroSourcePair : Bool := true
def formalProjectedVacuumAlreadyCalibratedLabObservable : Bool := false

def mirrorDoesNotConstructPhysicalActuator : Bool := true

end Integration.AntigravityVacuumControlCoordinateMaxCut
