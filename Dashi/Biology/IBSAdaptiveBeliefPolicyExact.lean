import Dashi.Biology.IBSCausalMaintenanceRegimeExact
import Dashi.Biology.IBSMonashAdaptiveSequencingExact
import Dashi.Biology.IBSMonashLongHorizonAdaptiveExact
import Dashi.Biology.IBSTrialDesignDonorAtlasExact

namespace Dashi.Biology.IBSAdaptiveBeliefPolicyExact

open Dashi.Biology.IBSCausalMaintenanceRegimeExact
open Dashi.Biology.IBSMonashAdaptiveSequencingExact
open Dashi.Biology.IBSMonashLongHorizonAdaptiveExact
open Dashi.Biology.IBSTrialDesignDonorAtlasExact

inductive BeliefLevel where
  | unsupportedCandidate | unresolvedCandidate | comparativelyElevatedCandidate | comparativelyDowngradedCandidate
  deriving Repr, DecidableEq

inductive BeliefAuthority where
  | structuralBeliefOnly | observationConditionedBelief | perturbationConditionedBelief | validatedPosteriorModel
  deriving Repr, DecidableEq

structure IBSRegimeBeliefState where
  microbialImmune : BeliefLevel
  barrierSensory : BeliefLevel
  autonomicCentral : BeliefLevel
  bileAcidMotility : BeliefLevel
  mixedCoupled : BeliefLevel
  authority : BeliefAuthority
  populationReference : String
  historyReference : String
  numericProbabilityAssigned : Bool
  clinicalDiagnosisClaimed : Bool
  deriving Repr, DecidableEq

def canonicalInitialIBSBeliefState : IBSRegimeBeliefState := {
  microbialImmune := .unresolvedCandidate
  barrierSensory := .unresolvedCandidate
  autonomicCentral := .unresolvedCandidate
  bileAcidMotility := .unresolvedCandidate
  mixedCoupled := .unresolvedCandidate
  authority := .structuralBeliefOnly
  populationReference := "no participant-specific population instantiated"
  historyReference := "no participant-specific history instantiated"
  numericProbabilityAssigned := false
  clinicalDiagnosisClaimed := false
}

inductive ObservationKind where
  | symptomTrajectoryObservation | proximalTargetEngagementObservation | competingFibreObservation
  | challengeRecoveryObservation | burdenSafetyObservation | negativeTargetingValidationObservation
  deriving Repr, DecidableEq

structure PolicyObservation where
  kind : ObservationKind
  sourceOrExperimentReference : String
  actionReference : String
  observedSurface : String
  timingReference : String
  targetEngagementReference : String
  competingFibreReference : String
  burdenSafetyReference : String
  carryoverReference : String
  causalInterpretationClaimed : Bool
  deriving Repr, DecidableEq

inductive UpdateDirection where
  | noDirectionalUpdate | comparativelyRaiseCandidate | comparativelyLowerCandidate | reopenCompetingCandidates
  deriving Repr, DecidableEq

inductive UpdateAuthority where
  | designOnlyUpdate | associationConditionedUpdate | perturbationConditionedUpdate | externallyValidatedUpdate
  deriving Repr, DecidableEq

structure BeliefUpdateReceipt where
  before : IBSRegimeBeliefState
  observation : PolicyObservation
  candidate : MaintenanceRegimeCandidate
  direction : UpdateDirection
  updateAuthority : UpdateAuthority
  likelihoodOrDecisionRuleReference : String
  alternativeExplanationReference : String
  afterReference : String
  createsRegimeTruth : Bool
  createsDiagnosis : Bool
  deriving Repr, DecidableEq

structure BeliefUpdateObligation where
  responseDefinitionPredeclared : Bool
  timingPredeclared : Bool
  proximalTargetEngagementMeasured : Bool
  competingFibresRetained : Bool
  adherenceExposureRetained : Bool
  carryoverWashoutAudited : Bool
  burdenSafetyRetained : Bool
  alternativeExplanationsRetained : Bool
  likelihoodModelValidatedIfNumericPosteriorUsed : Bool
  deriving Repr, DecidableEq

def canonicalBeliefUpdateObligation : BeliefUpdateObligation := {
  responseDefinitionPredeclared := true, timingPredeclared := true,
  proximalTargetEngagementMeasured := true, competingFibresRetained := true,
  adherenceExposureRetained := true, carryoverWashoutAudited := true,
  burdenSafetyRetained := true, alternativeExplanationsRetained := true,
  likelihoodModelValidatedIfNumericPosteriorUsed := true
}

inductive ClinicalValueClass where
  | establishedOrGuidelineValue | boundedClinicalValue | experimentalProbeValue
  deriving Repr, DecidableEq
inductive InformationValueClass where
  | lowInformationValue | singleFibreInformation | orthogonalFibreInformation | transitionHistoryInformation
  deriving Repr, DecidableEq
inductive SafetyStatus where
  | establishedSafetyContext | requiresScreening | experimentalSafetyUncertain
  deriving Repr, DecidableEq
inductive CarryoverRisk where
  | lowCarryoverRisk | explicitWashoutNeeded | longOrUnknownCarryover
  deriving Repr, DecidableEq

structure AdaptivePolicyAction where
  actionReference : String
  clinicalValue : ClinicalValueClass
  informationValue : InformationValueClass
  burden : BurdenClass
  safety : SafetyStatus
  carryover : CarryoverRisk
  proximalReadout : String
  distalReadout : String
  foodQoLReference : String
  accessReference : String
  stopOrSwitchReference : String
  deriving Repr, DecidableEq

def lowFODMAPPolicyAction : AdaptivePolicyAction := {
  actionReference := "Monash low-FODMAP / personalized reintroduction family"
  clinicalValue := .establishedOrGuidelineValue
  informationValue := .orthogonalFibreInformation
  burden := .moderateBurden
  safety := .requiresScreening
  carryover := .explicitWashoutNeeded
  proximalReadout := "exposure/adherence + fermentation/luminal ecology where measured"
  distalReadout := "symptom/QOL trajectory"
  foodQoLReference := "minimize unnecessary restriction and retain food-related QoL"
  accessReference := "dietitian access and implementation burden retained"
  stopOrSwitchReference := "prospectively defined symptom, nutrition and burden rules"
}

def blindedChallengePolicyAction : AdaptivePolicyAction := {
  actionReference := "blinded FODMAP-class challenge / mechanistically matched rescue"
  clinicalValue := .experimentalProbeValue
  informationValue := .transitionHistoryInformation
  burden := .moderateBurden
  safety := .requiresScreening
  carryover := .explicitWashoutNeeded
  proximalReadout := "class-specific provocation/rescue timing"
  distalReadout := "symptom recurrence and recovery"
  foodQoLReference := "challenge burden retained; not indefinite restriction"
  accessReference := "standardized challenge materials and monitoring"
  stopOrSwitchReference := "stop for unacceptable symptoms/safety or after predeclared discrimination target"
}

def digitalGDHPolicyAction : AdaptivePolicyAction := {
  actionReference := "digital gut-directed hypnotherapy family"
  clinicalValue := .boundedClinicalValue
  informationValue := .orthogonalFibreInformation
  burden := .lowBurden
  safety := .establishedSafetyContext
  carryover := .longOrUnknownCarryover
  proximalReadout := "central/interoceptive/autonomic change where actually measured"
  distalReadout := "symptom and quality-of-life trajectory"
  foodQoLReference := "no dietary restriction burden"
  accessReference := "digital delivery may reduce access burden relative to therapist-only delivery"
  stopOrSwitchReference := "evaluate at predeclared programme milestones; response does not identify CNS-only regime"
}

def quailProbePolicyAction : AdaptivePolicyAction := {
  actionReference := "quail-egg mast-cell candidate probe"
  clinicalValue := .experimentalProbeValue
  informationValue := .singleFibreInformation
  burden := .moderateBurden
  safety := .experimentalSafetyUncertain
  carryover := .explicitWashoutNeeded
  proximalReadout := "mast-cell/histamine/tryptase and exposure confirmation"
  distalReadout := "whole-system symptom/barrier/metabolome/autonomic trajectory"
  foodQoLReference := "food exposure and allergy burden retained"
  accessReference := "requires quail-specific allergy screening and controlled preparation"
  stopOrSwitchReference := "no clinical sequencing until human IBS same-object experiment exists"
}

def canonicalAdaptivePolicyActionAtlas : List AdaptivePolicyAction := [
  lowFODMAPPolicyAction, blindedChallengePolicyAction, digitalGDHPolicyAction, quailProbePolicyAction
]

inductive PolicyStoppingReason where
  | therapeuticGoalMet | burdenOrSafetyDominates | discriminationTargetMet
  | carryoverPreventsInterpretation | noAdmissibleNextAction | externalValidationRequired
  deriving Repr, DecidableEq

structure AdaptivePolicyDecision where
  currentBeliefReference : String
  admissibleActions : List AdaptivePolicyAction
  selectedActionReference : String
  selectionRationale : String
  predeclaredSwitchRule : String
  stoppingReasonIfAny : PolicyStoppingReason
  numericOptimizationClaimed : Bool
  patientSpecificRecommendationClaimed : Bool
  deriving Repr, DecidableEq

inductive SingleResponseMakesRegimeTruePermission : Prop
inductive InformationOptimalActionIsClinicalOptimalPermission : Prop
inductive PostHocSwitchEqualsProspectiveAdaptivePolicyPermission : Prop
inductive BeliefStateIsClinicalDiagnosisPermission : Prop
inductive NumericPosteriorWithoutValidatedLikelihoodPermission : Prop

theorem singleResponseDoesNotMakeRegimeTrue : SingleResponseMakesRegimeTruePermission → False := by intro h; cases h
theorem informationOptimalDoesNotMeanClinicalOptimal : InformationOptimalActionIsClinicalOptimalPermission → False := by intro h; cases h
theorem postHocSwitchDoesNotEqualProspectiveAdaptivePolicy : PostHocSwitchEqualsProspectiveAdaptivePolicyPermission → False := by intro h; cases h
theorem beliefStateDoesNotBecomeClinicalDiagnosis : BeliefStateIsClinicalDiagnosisPermission → False := by intro h; cases h
theorem numericPosteriorRequiresValidatedLikelihood : NumericPosteriorWithoutValidatedLikelihoodPermission → False := by intro h; cases h

structure AdaptivePolicyBoundary where
  regimeBeliefsRemainHypotheses : Bool
  therapeuticAndInformationValueSeparated : Bool
  burdenQoLAccessSafetyRetained : Bool
  switchingRulesMustBeProspective : Bool
  negativeEvidenceCanDowngradeCandidate : Bool
  numericPosteriorInvented : Bool
  numericUtilityInvented : Bool
  patientSpecificRecommendationMade : Bool
  donorOwnerReference : String
  longHorizonOwnerReference : String
  deriving Repr, DecidableEq

def canonicalAdaptivePolicyBoundary : AdaptivePolicyBoundary := {
  regimeBeliefsRemainHypotheses := true
  therapeuticAndInformationValueSeparated := true
  burdenQoLAccessSafetyRetained := true
  switchingRulesMustBeProspective := true
  negativeEvidenceCanDowngradeCandidate := true
  numericPosteriorInvented := false
  numericUtilityInvented := false
  patientSpecificRecommendationMade := false
  donorOwnerReference := "IBSTrialDesignDonorAtlasExact"
  longHorizonOwnerReference := "IBSMonashLongHorizonAdaptiveExact"
}

structure AdaptivePolicyParetoNode where
  label : String
  paidReference : String
  residual : String
  nextAcquisition : String
  authorityBoundary : String
  deriving Repr, DecidableEq

def canonicalAdaptivePolicyParetoFrontier : List AdaptivePolicyParetoNode := [
  { label := "prospective SMART IBS policy",
    paidReference := "SMART methodology donor plus current IBS orthogonal treatment evidence",
    residual := "no IBS-validated response state, rerandomization rule, or distal utility function",
    nextAcquisition := "pilot SMART with low-burden first-line options and preregistered stage-2 choices",
    authorityBoundary := "prospective design evaluates a policy; it does not reveal a true regime label by fiat" },
  { label := "Bayesian adaptive N-of-1 policy",
    paidReference := "Senarathne 2020 donor plus IBS crossover/challenge evidence",
    residual := "likelihood, carryover and prior structure unvalidated across heterogeneous IBS actions",
    nextAcquisition := "begin with reversible short-latency challenge/rescue actions and validate carryover/stopping model",
    authorityBoundary := "no numeric posterior before likelihood/model validation" },
  { label := "minimal-effective restriction policy",
    paidReference := "Monash long-horizon burden evidence plus 2026 external personalized-FODMAP trial",
    residual := "optimal reintroduction/switch timing unvalidated",
    nextAcquisition := "randomized protocolized personalized-reintroduction policy versus usual dietetic care",
    authorityBoundary := "food-QoL/nutritional burden remain co-primary decision coordinates" },
  { label := "mechanistic targeting validation gate",
    paidReference := "Balsiger 2026 negative CLE targeting trial",
    residual := "candidate biomarkers still lack guided-vs-sham/usual treatment-selection validation",
    nextAcquisition := "admit targeting rule only after prospective guided selection improves relevant outcome",
    authorityBoundary := "mechanistic signal and actionable selector are separate claims" },
  { label := "quail candidate admission",
    paidReference := "preclinical quail ladder + human non-IBS exposure + independent IBS mast-cell mechanisms",
    residual := "human IBS same-object target-engagement and safety evidence absent",
    nextAcquisition := "first-in-IBS controlled exposure before any clinical adaptive-policy branch",
    authorityBoundary := "candidate information value does not create treatment authority" }
]

end Dashi.Biology.IBSAdaptiveBeliefPolicyExact
