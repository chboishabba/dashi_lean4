import Dashi.Biology.IBSAdaptiveBeliefPolicyExact

namespace Dashi.Biology.IBSPersonalizationValidationExact

inductive PersonalizationStrategyKind where
  | selectiveDiaryGuidedFODMAP | microbiomeAIGuidedDiet | biomarkerGuidedExclusion | dietitianReintroductionPersonalization
  deriving Repr, DecidableEq

inductive PersonalizationValidationStatus where
  | randomizedNoSuperiority | randomizedComparableImprovement | linkedLongTermDurabilitySignal
  | targetingSignalFailedSham | observationalLongTermBurdenEvidence
  deriving Repr, DecidableEq

structure PersonalizationValidationEvidence where
  sourceReference : String
  strategy : PersonalizationStrategyKind
  status : PersonalizationValidationStatus
  comparatorReference : String
  paidObservation : String
  selectorExternallyValidated : Bool
  clinicalUtilityValidated : Bool
  mechanismIdentified : Bool
  transportEstablished : Bool
  deriving Repr, DecidableEq

def canonicalIBSPersonalizationValidationAtlas : List PersonalizationValidationEvidence := [
  { sourceReference := "Garcia-Cedillo et al. 2026 DOI 10.1111/apt.70601",
    strategy := .selectiveDiaryGuidedFODMAP, status := .randomizedComparableImprovement,
    comparatorReference := "NICE dietary advice",
    paidObservation := "selective patient-specific FODMAP reduction was feasible and improved symptoms without represented evidence of superior primary clinical outcome",
    selectorExternallyValidated := false, clinicalUtilityValidated := false, mechanismIdentified := false, transportEstablished := false },
  { sourceReference := "Tunali et al. 2024 DOI 10.14309/ajg.0000000000002862",
    strategy := .microbiomeAIGuidedDiet, status := .randomizedNoSuperiority,
    comparatorReference := "standard low-FODMAP diet",
    paidObservation := "both groups improved; primary between-group IBS-SSS contrast was not significant",
    selectorExternallyValidated := false, clinicalUtilityValidated := false, mechanismIdentified := false, transportEstablished := false },
  { sourceReference := "Tunali et al. 2026 DOI 10.1080/19490976.2026.2719125",
    strategy := .microbiomeAIGuidedDiet, status := .linkedLongTermDurabilitySignal,
    comparatorReference := "12-month linked follow-up of low-FODMAP arm",
    paidObservation := "hypothesis-generating durability signal favoured personalized diet at 12 months",
    selectorExternallyValidated := false, clinicalUtilityValidated := false, mechanismIdentified := false, transportEstablished := false },
  { sourceReference := "Balsiger et al. 2026 DOI 10.1053/j.gastro.2026.08.026",
    strategy := .biomarkerGuidedExclusion, status := .targetingSignalFailedSham,
    comparatorReference := "sham food exclusion after CLE",
    paidObservation := "CLE-targeted exclusion did not outperform sham in the controlled crossover",
    selectorExternallyValidated := false, clinicalUtilityValidated := false, mechanismIdentified := false, transportEstablished := false },
  { sourceReference := "Silva et al. 2025 DOI 10.1111/nmo.70116",
    strategy := .dietitianReintroductionPersonalization, status := .observationalLongTermBurdenEvidence,
    comparatorReference := "observed long-term dietary patterns after FODMAP education",
    paidObservation := "symptom control often coexisted with non-strict/personalized diets; strict restriction carried lower food-related QoL",
    selectorExternallyValidated := false, clinicalUtilityValidated := false, mechanismIdentified := false, transportEstablished := false }
]

inductive PersonalizedLabelImpliesSuperiorOutcomePermission : Prop
inductive MechanisticBiomarkerIsValidatedSelectorPermission : Prop
inductive InternalPersonalizationModelAutomaticallyTransportsPermission : Prop
inductive LinkedFollowUpIsIndependentValidationPermission : Prop
inductive NegativeSelectorTrialRefutesAllFoodMechanismsPermission : Prop

theorem personalizedLabelDoesNotImplySuperiorOutcome : PersonalizedLabelImpliesSuperiorOutcomePermission → False := by intro h; cases h
theorem mechanisticBiomarkerDoesNotBecomeValidatedSelector : MechanisticBiomarkerIsValidatedSelectorPermission → False := by intro h; cases h
theorem internalPersonalizationModelDoesNotAutomaticallyTransport : InternalPersonalizationModelAutomaticallyTransportsPermission → False := by intro h; cases h
theorem linkedFollowUpDoesNotBecomeIndependentValidation : LinkedFollowUpIsIndependentValidationPermission → False := by intro h; cases h
theorem negativeSelectorDoesNotRefuteAllFoodMechanisms : NegativeSelectorTrialRefutesAllFoodMechanismsPermission → False := by intro h; cases h

structure PersonalizationValidationBoundary where
  personalizationLabelNonPromoting : Bool
  prospectiveComparatorRequiredForUtility : Bool
  selectorNeedsCalibrationAndTransport : Bool
  linkedFollowUpKeptDistinctFromIndependentReplication : Bool
  negativeTargetingEvidenceCanDowngradeSelector : Bool
  negativeTargetingEvidenceRefutesWholeDomain : Bool
  policyOwnerReference : String
  deriving Repr, DecidableEq

def canonicalPersonalizationValidationBoundary : PersonalizationValidationBoundary := {
  personalizationLabelNonPromoting := true
  prospectiveComparatorRequiredForUtility := true
  selectorNeedsCalibrationAndTransport := true
  linkedFollowUpKeptDistinctFromIndependentReplication := true
  negativeTargetingEvidenceCanDowngradeSelector := true
  negativeTargetingEvidenceRefutesWholeDomain := false
  policyOwnerReference := "IBSAdaptiveBeliefPolicyExact"
}

structure PersonalizationParetoNode where
  label : String
  paidReference : String
  residual : String
  nextAcquisition : String
  authorityBoundary : String
  deriving Repr, DecidableEq

def canonicalIBSPersonalizationParetoFrontier : List PersonalizationParetoNode := [
  { label := "guided-versus-usual clinical utility",
    paidReference := "Garcia-Cedillo 2026 and Tunali 2024 randomized comparisons",
    residual := "personalization strategies have not established universal superiority or a common selector",
    nextAcquisition := "prospective policy trial with predeclared selector, comparator, calibration and patient-centred net benefit",
    authorityBoundary := "personalized is not an efficacy endpoint" },
  { label := "locked selector transport", paidReference := "Tunali 2024 multicenter microbiome-AI diet",
    residual := "algorithm calibration/transport outside development/program lineage remains open",
    nextAcquisition := "freeze selector and threshold before held-out geographic/laboratory replication",
    authorityBoundary := "multicenter data do not automatically equal independent algorithm validation" },
  { label := "long-term durability replication", paidReference := "Tunali 2026 linked 12-month follow-up",
    residual := "follow-up is linked to original program and explicitly hypothesis-generating",
    nextAcquisition := "independent adequately powered long-horizon trial using locked selector",
    authorityBoundary := "durability signal is not independent validation" },
  { label := "targeting biomarker falsification benchmark", paidReference := "Balsiger 2026 CLE sham-controlled crossover",
    residual := "other plausible targeting biomarkers may fail once treatment selection is sham-controlled",
    nextAcquisition := "require guided-vs-sham/usual selection before policy admission",
    authorityBoundary := "negative CLE result downgrades CLE selector authority, not all food mechanisms" },
  { label := "minimal-effective restriction utility", paidReference := "Silva 2025 Monash long-horizon burden evidence",
    residual := "optimal reintroduction rule and nutrition/QoL tradeoff remain unvalidated",
    nextAcquisition := "randomized protocolized reintroduction versus usual dietetic care with symptom, nutrition and food-QoL outcomes",
    authorityBoundary := "observational burden evidence does not establish causal policy superiority" }
]

end Dashi.Biology.IBSPersonalizationValidationExact
