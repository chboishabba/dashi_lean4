import Integration.ClinicToStreetsCausalProvenanceMaxCut

/-!
Final structural max-cut for the Clinic-to-Streets tranche.

The finite causal-DAG machinery is already present.  This file types the
remaining empirical/source obligations and keeps illustrative model numbers
role-indexed so scalar coincidence cannot turn them into measurements.
-/

namespace Integration.ClinicToStreetsEvidenceAcquisitionMaxCut

open Integration.ClinicToStreetsCausalProvenanceMaxCut

inductive EvidenceGrade
  | unacquired
  | attributedSource
  | sourceSupported
  | independentlyReplicated
  deriving DecidableEq, Repr

structure EdgeEvidenceReceipt (e : Edge) where
  grade : EvidenceGrade
  sameObjectPopulation : Bool
  temporallyOrdered : Bool
  alternativeExplanationsAudited : Bool
  interventionOrNaturalExperiment : Bool
  deriving Repr

structure MagnitudeCalibrationReceipt (e : Edge) where
  calibrated : Bool
  uncertaintyRepresented : Bool
  heldOutValidated : Bool
  deriving Repr

structure ResponsibilityMappingReceipt where
  explanatoryOnly : Bool
  independentlyMeasured : Bool
  moralFaultClaimed : Bool
  legalFaultClaimed : Bool
  deriving Repr

structure ActionConeEffectReceipt where
  representedAvailabilityMeasured : Bool
  behaviourMeasured : Bool
  underlyingCarrierDeleted : Bool
  intentEstablished : Bool
  deriving Repr

def structuralToFamilyCurrent : EdgeEvidenceReceipt .structuralToFamily :=
  ⟨.attributedSource, false, false, false, false⟩

def familyToPsychicCurrent : EdgeEvidenceReceipt .familyToPsychic :=
  ⟨.attributedSource, false, false, false, false⟩

def structuralToPsychicCurrent : EdgeEvidenceReceipt .structuralToPsychic :=
  ⟨.unacquired, false, false, false, false⟩

def structuralToFamilyMagnitudeCurrent : MagnitudeCalibrationReceipt .structuralToFamily :=
  ⟨false, false, false⟩

def canonicalResponsibilityMappingBoundary : ResponsibilityMappingReceipt :=
  ⟨true, false, false, false⟩

def canonicalActionConeEffectBoundary : ActionConeEffectReceipt :=
  ⟨false, false, false, false⟩

inductive AttributedEdgeImpliesEmpiricalCausality : Prop
inductive ModelCoordinateImpliesCalibratedMagnitude : Prop
inductive ExplanatoryResponsibilityImpliesFault : Prop
inductive RepresentedConeImpliesBehaviour : Prop

theorem attributedEdgeDoesNotEstablishEmpiricalCausality :
    ¬ AttributedEdgeImpliesEmpiricalCausality := by
  intro h; cases h

theorem modelCoordinateDoesNotEstablishCalibratedMagnitude :
    ¬ ModelCoordinateImpliesCalibratedMagnitude := by
  intro h; cases h

theorem explanatoryResponsibilityDoesNotEstablishFault :
    ¬ ExplanatoryResponsibilityImpliesFault := by
  intro h; cases h

theorem representedConeDoesNotEstablishBehaviour :
    ¬ RepresentedConeImpliesBehaviour := by
  intro h; cases h

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
  deriving Repr

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

theorem equalScalarDoesNotIdentifyRole : ¬ EqualScalarImpliesSameRole := by
  intro h; cases h

structure FinalMaxCutBoundary where
  finiteStructurePaid : Bool
  edgeExistenceRequiresEvidence : Bool
  magnitudeRequiresCalibration : Bool
  responsibilityMappingRequiresIndependentReceipt : Bool
  actionConeBehaviourRequiresMeasurement : Bool
  modelNumbersRoleTyped : Bool
  attributedClaimsAreEmpiricalCausalProof : Bool
  moreAbstractStructureCountsAsEmpiricalProgress : Bool
  deriving Repr

def canonicalFinalMaxCutBoundary : FinalMaxCutBoundary :=
  ⟨true, true, true, true, true, true, false, false⟩

end Integration.ClinicToStreetsEvidenceAcquisitionMaxCut
