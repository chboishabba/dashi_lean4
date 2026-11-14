import Integration.ClinicToStreetsCausalProvenanceMaxCut

/-!
# Clinic-to-Streets evidence authority boundary

Agda owns the repository's generic causal-estimand and causal-identification
families.  This Lean branch currently has no native equivalent owner.  Rather
than maintain a second, weaker checklist here, Lean mirrors only the structural
status and explicitly fails closed on empirical causal promotion.
-/

namespace Integration.ClinicToStreetsEvidenceAcquisitionMaxCut

open Integration.ClinicToStreetsCausalProvenanceMaxCut

inductive SourceEvidenceStatus
  | unacquired
  | attributedSource
  | sourceSupported
  | independentlyReplicated
  deriving DecidableEq, Repr

structure CausalEdgeStatus where
  edge : Edge
  sourceStatus : SourceEvidenceStatus
  agdaEstimandRequired : Bool
  agdaIdentificationReceiptRequired : Bool
  magnitudeCalibrationRequired : Bool
  currentEmpiricalCausalPayment : Bool
  deriving DecidableEq, Repr

def structuralToFamilyStatus : CausalEdgeStatus :=
  ⟨.structuralToFamily, .attributedSource, true, true, true, false⟩

def familyToPsychicStatus : CausalEdgeStatus :=
  ⟨.familyToPsychic, .attributedSource, true, true, true, false⟩

def structuralToPsychicStatus : CausalEdgeStatus :=
  ⟨.structuralToPsychic, .unacquired, true, true, true, false⟩

structure ResponsibilityMappingStatus where
  independentlyMeasured : Bool
  moralFaultClaimed : Bool
  legalFaultClaimed : Bool
  deriving DecidableEq, Repr

def responsibilityMappingStatus : ResponsibilityMappingStatus :=
  ⟨false, false, false⟩

structure ActionConeMeasurementStatus where
  representedAvailabilityMeasured : Bool
  behaviourMeasured : Bool
  intentEstablished : Bool
  deriving DecidableEq, Repr

def actionConeMeasurementStatus : ActionConeMeasurementStatus :=
  ⟨false, false, false⟩

inductive StructuralMirrorImpliesEmpiricalCausalClosure : Prop
inductive ExplanatoryResponsibilityImpliesFault : Prop
inductive RepresentedConeImpliesBehaviour : Prop

theorem structuralMirrorDoesNotEstablishEmpiricalCausalClosure :
    ¬ StructuralMirrorImpliesEmpiricalCausalClosure := by
  intro h; cases h

theorem explanatoryResponsibilityDoesNotEstablishFault :
    ¬ ExplanatoryResponsibilityImpliesFault := by
  intro h; cases h

theorem representedConeDoesNotEstablishBehaviour :
    ¬ RepresentedConeImpliesBehaviour := by
  intro h; cases h

/-! Illustrative formal coordinates remain role-indexed and non-empirical. -/

inductive CoordinateRole
  | representedUpstreamSalience
  | responsibilityStructuralShare
  | responsibilityIntimateShare
  | responsibilityIndividualShare
  | representedActionConeCardinality
  deriving DecidableEq, Repr

structure ModelCoordinate where
  value : Nat
  role : CoordinateRole
  empirical : Bool
  deriving DecidableEq, Repr

def fullSalienceCoordinate : ModelCoordinate :=
  ⟨9, .representedUpstreamSalience, false⟩

def atomisedSalienceCoordinate : ModelCoordinate :=
  ⟨3, .representedUpstreamSalience, false⟩

def fullStructuralResponsibilityCoordinate : ModelCoordinate :=
  ⟨6, .responsibilityStructuralShare, false⟩

def atomisedIndividualResponsibilityCoordinate : ModelCoordinate :=
  ⟨7, .responsibilityIndividualShare, false⟩

def atomisedActionConeCoordinate : ModelCoordinate :=
  ⟨1, .representedActionConeCardinality, false⟩

inductive EqualScalarImpliesSameRole : Prop
inductive ModelCoordinateImpliesCalibratedMagnitude : Prop

theorem equalScalarDoesNotIdentifyRole : ¬ EqualScalarImpliesSameRole := by
  intro h; cases h

theorem modelCoordinateDoesNotEstablishCalibratedMagnitude :
    ¬ ModelCoordinateImpliesCalibratedMagnitude := by
  intro h; cases h

structure Boundary where
  agdaOwnsCausalEstimandSemantics : Bool
  leanReimplementsCausalIdentificationChecklist : Bool
  currentClinicCausalIdentificationPaid : Bool
  structuralMirrorMayClaimEmpiricalCausalClosure : Bool
  responsibilityRequiresIndependentMeasurement : Bool
  actionConeBehaviourRequiresMeasurement : Bool
  illustrativeNumbersAreEmpirical : Bool
  deriving DecidableEq, Repr

def canonicalBoundary : Boundary :=
  ⟨true, false, false, false, true, true, false⟩

end Integration.ClinicToStreetsEvidenceAcquisitionMaxCut
