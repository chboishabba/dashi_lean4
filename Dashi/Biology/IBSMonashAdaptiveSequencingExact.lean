import Dashi.Biology.IBSResponsePredictorAtlasExact
import Dashi.Biology.IBSMechanismProbePerturbationAtlasExact

namespace Dashi.Biology.IBSMonashAdaptiveSequencingExact

inductive MonashEvidenceRole where
  | wholeDietEfficacy | luminalEcologyPerturbation | orthogonalTherapyComparison
  | nutrientChallengeRescue | digestiveGeneticModifier
  deriving Repr, DecidableEq

structure MonashIBSEvidence where
  sourceReference : String
  role : MonashEvidenceRole
  interventionOrExposure : String
  observedSurface : String
  mechanismIdentified : Bool
  participantClassifierValidated : Bool
  deriving Repr, DecidableEq

def canonicalMonashIBSProgrammeAtlas : List MonashIBSEvidence := [
  { sourceReference := "Halmos et al. 2014 DOI 10.1053/j.gastro.2013.09.046",
    role := .wholeDietEfficacy, interventionOrExposure := "low-FODMAP versus Australian diet crossover",
    observedSurface := "IBS symptom response", mechanismIdentified := false, participantClassifierValidated := false },
  { sourceReference := "Halmos et al. 2015 DOI 10.1136/gutjnl-2014-307264",
    role := .luminalEcologyPerturbation, interventionOrExposure := "controlled FODMAP-content change",
    observedSurface := "colonic luminal microbial/metabolic environment", mechanismIdentified := false, participantClassifierValidated := false },
  { sourceReference := "Peters et al. 2016 DOI 10.1111/apt.13706",
    role := .orthogonalTherapyComparison, interventionOrExposure := "gut-directed hypnotherapy versus low-FODMAP versus combination",
    observedSurface := "GI and psychological outcomes", mechanismIdentified := false, participantClassifierValidated := false },
  { sourceReference := "Tuck et al. 2018 DOI 10.1038/ajg.2017.245",
    role := .nutrientChallengeRescue, interventionOrExposure := "GOS challenge with alpha-galactosidase versus placebo",
    observedSurface := "nutrient-specific symptom provocation/rescue", mechanismIdentified := false, participantClassifierValidated := false },
  { sourceReference := "Silva et al. 2026 DOI 10.1002/ueg2.70173",
    role := .digestiveGeneticModifier, interventionOrExposure := "sucrase-isomaltase hypomorphic-variant status after FODMAP education",
    observedSurface := "long-term symptom/dietary outcome association", mechanismIdentified := false, participantClassifierValidated := false }
]

inductive TreatmentResponseIdentifiesMechanismPermission : Prop
inductive InformationGainEqualsClinicalBenefitPermission : Prop
inductive LowFODMAPResponseIdentifiesUniversalFODMAPMechanismPermission : Prop

theorem treatmentResponseDoesNotIdentifyMechanism : TreatmentResponseIdentifiesMechanismPermission → False := by intro h; cases h
theorem informationGainDoesNotEqualClinicalBenefit : InformationGainEqualsClinicalBenefitPermission → False := by intro h; cases h
theorem lowFODMAPResponseDoesNotIdentifyUniversalMechanism : LowFODMAPResponseIdentifiesUniversalFODMAPMechanismPermission → False := by intro h; cases h

inductive TherapeuticValue where | establishedTreatmentValue | boundedTreatmentValue | probeOnlyValue deriving Repr, DecidableEq
inductive DiscriminationValue where | lowDiscrimination | separatesOneFibre | separatesOrthogonalFibres | transitionSensitive deriving Repr, DecidableEq
inductive BurdenClass where | lowBurden | moderateBurden | highBurden deriving Repr, DecidableEq
inductive AdaptiveAction where
  | lowFODMAPAction | blindedFODMAPRechallengeAction | gutDirectedHypnotherapyAction
  | rifaximinAction | bileAcidProbeAction | histamineH1ProbeAction | quailCandidateProbeAction
  deriving Repr, DecidableEq

structure AdaptiveTreatmentProbe where
  action : AdaptiveAction
  therapeuticValue : TherapeuticValue
  discriminationValue : DiscriminationValue
  burden : BurdenClass
  proximalReadout : String
  distalReadout : String
  attributionBoundary : String
  deriving Repr, DecidableEq

def lowFODMAPAdaptiveProbe : AdaptiveTreatmentProbe :=
  { action := .lowFODMAPAction, therapeuticValue := .establishedTreatmentValue,
    discriminationValue := .separatesOrthogonalFibres, burden := .moderateBurden,
    proximalReadout := "diet exposure/adherence + fermentation/luminal ecology",
    distalReadout := "symptom trajectory",
    attributionBoundary := "response does not identify whether osmotic, fermentative, microbial, sensory, expectancy or mixed path dominates" }

def rechallengeAdaptiveProbe : AdaptiveTreatmentProbe :=
  { action := .blindedFODMAPRechallengeAction, therapeuticValue := .probeOnlyValue,
    discriminationValue := .transitionSensitive, burden := .moderateBurden,
    proximalReadout := "within-person class-specific challenge response and latency",
    distalReadout := "symptom recurrence/recovery trajectory",
    attributionBoundary := "trigger identification does not identify downstream mechanism or universal intolerance" }

def hypnotherapyAdaptiveProbe : AdaptiveTreatmentProbe :=
  { action := .gutDirectedHypnotherapyAction, therapeuticValue := .establishedTreatmentValue,
    discriminationValue := .separatesOrthogonalFibres, burden := .moderateBurden,
    proximalReadout := "central/interoceptive and autonomic response surface where measured",
    distalReadout := "symptom/QOL trajectory",
    attributionBoundary := "clinical response does not prove central-only maintenance" }

structure AdaptiveSequencingNode where
  label : String
  route : String
  currentEvidence : String
  informationDebt : String
  nextDesign : String
  authorityBoundary : String
  deriving Repr, DecidableEq

def canonicalAdaptiveTreatmentSequencingFrontier : List AdaptiveSequencingNode := [
  { label := "orthogonal diet versus brain-gut intervention", route := "externalKnowledgeComparison",
    currentEvidence := "Peters 2016 Monash RCT: distinct interventions with overlapping symptom benefit",
    informationDebt := "synchronized peripheral/central target-engagement measurements",
    nextDesign := "factorial or sequential design with common whole-system panel and recovery interval",
    authorityBoundary := "similar efficacy does not imply common mechanism" },
  { label := "nutrient-specific challenge-rescue", route := "externalKnowledgeComparison",
    currentEvidence := "Tuck 2018 GOS challenge plus alpha-galactosidase rescue",
    informationDebt := "transport to other FODMAP classes and explicit fermentation/osmotic/sensory readouts",
    nextDesign := "class-specific blinded challenges with matched rescue where mechanistically valid",
    authorityBoundary := "one carbohydrate-rescue result does not generalize to all FODMAPs" },
  { label := "adaptive therapy as identification experiment", route := "experimentalDesign",
    currentEvidence := "current regime/predictor/probe owners provide competing hypotheses and treatment-specific signals",
    informationDebt := "no validated policy combines therapeutic value, information value, burden and uncertainty",
    nextDesign := "prospective SMART-like or response-adaptive trial with locked switching rules and proximal target engagement",
    authorityBoundary := "an informative probe is not necessarily the clinically best treatment; clinical benefit is not information gain" },
  { label := "long-term personalized carbohydrate handling", route := "externalKnowledgeComparison",
    currentEvidence := "Silva 2026 SI genotype as candidate modifier after FODMAP education",
    informationDebt := "prospective genotype-by-diet interaction and replication",
    nextDesign := "predeclared interaction study rather than post-hoc mechanistic labeling",
    authorityBoundary := "genotype association is neither deterministic intolerance nor causal-regime identity" }
]

structure MonashAdaptiveBoundary where
  monashSourcesGroupedByProvenanceNotAuthority : Bool
  responseMechanismSeparated : Bool
  benefitInformationSeparated : Bool
  burdenRetained : Bool
  noNumericUtilityInvented : Bool
  noPatientSpecificSequenceClaimed : Bool
  deriving Repr, DecidableEq

def canonicalMonashAdaptiveBoundary : MonashAdaptiveBoundary :=
  { monashSourcesGroupedByProvenanceNotAuthority := true, responseMechanismSeparated := true,
    benefitInformationSeparated := true, burdenRetained := true, noNumericUtilityInvented := true,
    noPatientSpecificSequenceClaimed := true }

end Dashi.Biology.IBSMonashAdaptiveSequencingExact
