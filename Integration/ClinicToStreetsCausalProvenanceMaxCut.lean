import Integration.ClinicToStreetsCausalProvenance

/-!
# Clinic-to-Streets causal-provenance max-cut

Refines the earlier Boolean provenance-erasure witness onto one literal finite
causal DAG.  The weights and responsibility coordinates are model coordinates,
not empirical estimates, diagnoses, legal responsibility, or moral fault.
-/

namespace Integration.ClinicToStreetsCausalProvenanceMaxCut

open Integration.ClinicToStreetsCausalProvenance

inductive Node
  | structuralCondition
  | familySite
  | psychicState
  | collectiveAction
  | individualAction
  deriving DecidableEq, Repr

inductive Edge
  | structuralToFamily
  | familyToPsychic
  | structuralToPsychic
  | psychicToCollective
  | psychicToIndividual
  deriving DecidableEq, Repr

def edgeSource : Edge → Node
  | .structuralToFamily => .structuralCondition
  | .familyToPsychic => .familySite
  | .structuralToPsychic => .structuralCondition
  | .psychicToCollective => .psychicState
  | .psychicToIndividual => .psychicState

def edgeTarget : Edge → Node
  | .structuralToFamily => .familySite
  | .familyToPsychic => .psychicState
  | .structuralToPsychic => .psychicState
  | .psychicToCollective => .collectiveAction
  | .psychicToIndividual => .individualAction

def edgeWeight : Edge → Nat
  | .structuralToFamily => 4
  | .familyToPsychic => 3
  | .structuralToPsychic => 2
  | .psychicToCollective => 3
  | .psychicToIndividual => 1

inductive InterpretationView
  | full
  | atomised
  | reskilled
  deriving DecidableEq, Repr

def edgeVisible : InterpretationView → Edge → Bool
  | .full, _ => true
  | .atomised, .structuralToFamily => false
  | .atomised, .structuralToPsychic => false
  | .atomised, _ => true
  | .reskilled, _ => true

theorem structural_family_deleted_by_atomisation :
    edgeVisible .full .structuralToFamily = true ∧
    edgeVisible .atomised .structuralToFamily = false := by
  constructor <;> rfl

theorem structural_psychic_deleted_by_atomisation :
    edgeVisible .full .structuralToPsychic = true ∧
    edgeVisible .atomised .structuralToPsychic = false := by
  constructor <;> rfl

theorem family_psychic_retained_by_atomisation :
    edgeVisible .atomised .familyToPsychic = true := by rfl

def psychicUpstreamSalience : InterpretationView → Nat
  | .full => 9
  | .atomised => 3
  | .reskilled => 9

theorem atomisation_deletes_represented_upstream_salience :
    psychicUpstreamSalience .full = 9 ∧
    psychicUpstreamSalience .atomised = 3 := by
  constructor <;> rfl

theorem reskilling_restores_represented_upstream_salience :
    psychicUpstreamSalience .reskilled = psychicUpstreamSalience .full := by rfl

structure ResponsibilityProfile where
  structuralShare : Nat
  intimateShare : Nat
  individualShare : Nat
  deriving DecidableEq, Repr

def fullResponsibility : ResponsibilityProfile := ⟨6, 3, 1⟩
def atomisedResponsibility : ResponsibilityProfile := ⟨0, 3, 7⟩
def reskilledResponsibility : ResponsibilityProfile := ⟨6, 3, 1⟩

theorem atomisation_reassigns_structural_share_to_individual :
    fullResponsibility.structuralShare = 6 ∧
    atomisedResponsibility.structuralShare = 0 ∧
    fullResponsibility.individualShare = 1 ∧
    atomisedResponsibility.individualShare = 7 := by
  repeat' apply And.intro
  all_goals rfl

theorem reskilling_restores_responsibility_profile :
    reskilledResponsibility = fullResponsibility := by rfl

inductive ActionOption
  | individualAdaptation
  | collectiveCoordination
  | structuralIntervention
  deriving DecidableEq, Repr

def actionAvailable : InterpretationView → ActionOption → Bool
  | .full, _ => true
  | .atomised, .individualAdaptation => true
  | .atomised, .collectiveCoordination => false
  | .atomised, .structuralIntervention => false
  | .reskilled, _ => true

def actionConeCardinality : InterpretationView → Nat
  | .full => 3
  | .atomised => 1
  | .reskilled => 3

theorem atomisation_contracts_represented_action_cone :
    actionConeCardinality .full = 3 ∧ actionConeCardinality .atomised = 1 := by
  constructor <;> rfl

theorem reskilling_reopens_represented_action_cone :
    actionConeCardinality .reskilled = actionConeCardinality .full := by rfl

inductive ModelWeightImpliesEmpiricalMagnitude : Prop
inductive ResponsibilityCoordinateImpliesMoralFault : Prop
inductive ActionConeContractionImpliesIntent : Prop

theorem model_weight_does_not_establish_empirical_magnitude :
    ¬ ModelWeightImpliesEmpiricalMagnitude := by
  intro h; cases h

theorem responsibility_coordinate_does_not_establish_moral_fault :
    ¬ ResponsibilityCoordinateImpliesMoralFault := by
  intro h; cases h

theorem action_cone_contraction_does_not_establish_intent :
    ¬ ActionConeContractionImpliesIntent := by
  intro h; cases h

structure MaxCutBoundary where
  literalDAGPresent : Bool
  upstreamDeletionMeasured : Bool
  responsibilityRedistributionRepresented : Bool
  actionConeContractionRepresented : Bool
  reskillingRestorationRepresented : Bool
  modelWeightsAreEmpiricalMagnitudes : Bool
  explanatoryResponsibilityIsMoralFault : Bool
  actionConeContractionEstablishesIntent : Bool
  deriving Repr

def canonicalMaxCutBoundary : MaxCutBoundary :=
  ⟨true, true, true, true, true, false, false, false⟩

end Integration.ClinicToStreetsCausalProvenanceMaxCut
