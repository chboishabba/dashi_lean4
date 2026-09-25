namespace DASHI.Biology.PMDDHistamineInterventionIdentificationBoundary

inductive H1Assignment where
  | open
  | blocked
  deriving Repr, DecidableEq

inductive H2Assignment where
  | open
  | blocked
  deriving Repr, DecidableEq

structure HistaminePerturbationArm where
  h1 : H1Assignment
  h2 : H2Assignment
  deriving Repr, DecidableEq

def baselineArm : HistaminePerturbationArm := ⟨.open, .open⟩
def h1OnlyArm : HistaminePerturbationArm := ⟨.blocked, .open⟩
def h2OnlyArm : HistaminePerturbationArm := ⟨.open, .blocked⟩
def dualBlockadeArm : HistaminePerturbationArm := ⟨.blocked, .blocked⟩

def factorialArms : List HistaminePerturbationArm :=
  [baselineArm, h1OnlyArm, h2OnlyArm, dualBlockadeArm]

inductive CycleWindow where
  | follicularReference
  | lutealSymptom
  | perimenstrualTransition
  deriving Repr, DecidableEq

inductive ResponseObservation where
  | noMaterialSymptomChange
  | symptomReductionObserved
  | symptomIncreaseObserved
  deriving Repr, DecidableEq

inductive CausalInterpretation where
  | h1DominantContribution
  | h2DominantContribution
  | jointHistamineChannelContribution
  | peripheralHistamineAmplifier
  | centralHistamineAmplifier
  | nonHistamineMediatedDrugEffect
  | mixedOrUnresolvedMechanism
  deriving Repr, DecidableEq

structure PerturbationObservation where
  arm : HistaminePerturbationArm
  cycleWindow : CycleWindow
  response : ResponseObservation
  interpretation : CausalInterpretation
  observationRecorded : Bool := true
  causalInterpretationIdentified : Bool := false
  deriving Repr, DecidableEq

def dualResponseCandidateA : PerturbationObservation :=
  { arm := dualBlockadeArm
    cycleWindow := .lutealSymptom
    response := .symptomReductionObserved
    interpretation := .jointHistamineChannelContribution }

def dualResponseCandidateB : PerturbationObservation :=
  { arm := dualBlockadeArm
    cycleWindow := .lutealSymptom
    response := .symptomReductionObserved
    interpretation := .nonHistamineMediatedDrugEffect }

theorem same_observation_different_causal_reading :
    dualResponseCandidateA.response = dualResponseCandidateB.response := rfl

structure IdentificationBoundary where
  fourArmFactorialSurfaceAvailable : Bool
  cycleWindowIndexed : Bool
  symptomResponseCanUpdateHypothesis : Bool
  responseAloneIdentifiesMechanism : Bool
  responseAloneIdentifiesHistamineSource : Bool
  responseAloneIdentifiesCompartment : Bool
  responseAloneEstablishesBiologicalSubtype : Bool
  responseAloneEstablishesTreatmentEfficacy : Bool
  h1MainEffectRequiresComparison : Bool
  h2MainEffectRequiresComparison : Bool
  h1h2InteractionRequiresComparison : Bool
  deriving Repr, DecidableEq

def canonicalBoundary : IdentificationBoundary :=
  { fourArmFactorialSurfaceAvailable := true
    cycleWindowIndexed := true
    symptomResponseCanUpdateHypothesis := true
    responseAloneIdentifiesMechanism := false
    responseAloneIdentifiesHistamineSource := false
    responseAloneIdentifiesCompartment := false
    responseAloneEstablishesBiologicalSubtype := false
    responseAloneEstablishesTreatmentEfficacy := false
    h1MainEffectRequiresComparison := true
    h2MainEffectRequiresComparison := true
    h1h2InteractionRequiresComparison := true }

theorem response_not_mechanism_identification :
    canonicalBoundary.responseAloneIdentifiesMechanism = false := rfl

theorem response_not_subtype_identification :
    canonicalBoundary.responseAloneEstablishesBiologicalSubtype = false := rfl

theorem response_not_efficacy_establishment :
    canonicalBoundary.responseAloneEstablishesTreatmentEfficacy = false := rfl

inductive SymptomResponseDeterminesMechanism : Prop
inductive DualBlockadeDeterminesHistamineSource : Prop
inductive SingleParticipantResponseDefinesSubtype : Prop

theorem symptomResponseDoesNotDetermineMechanism
    (h : SymptomResponseDeterminesMechanism) : False := by
  cases h

theorem dualBlockadeDoesNotDetermineHistamineSource
    (h : DualBlockadeDeterminesHistamineSource) : False := by
  cases h

theorem singleParticipantResponseDoesNotDefineSubtype
    (h : SingleParticipantResponseDefinesSubtype) : False := by
  cases h

end DASHI.Biology.PMDDHistamineInterventionIdentificationBoundary
