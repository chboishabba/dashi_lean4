namespace Dashi.Biology.IBSTrialDesignDonorAtlasExact

inductive TrialDesignKind where
  | smartSequentialRandomization | randomizedCrossover | adaptiveNOf1
  | nutrientPerturbationCrossover | protocolOnlyRepeatedChallenge
  | negativeTargetingValidation | parallelPersonalizationTrial
  deriving Repr, DecidableEq

structure TrialDesignDonor where
  sourceReference : String
  designKind : TrialDesignKind
  donorRole : String
  pays : String
  doesNotPay : String
  deriving Repr, DecidableEq

def canonicalIBSTrialDesignDonorAtlas : List TrialDesignDonor := [
  { sourceReference := "Collins/Murphy/Strecher 2007 DOI 10.1016/j.amepre.2007.01.022",
    designKind := .smartSequentialRandomization,
    donorRole := "prospective multi-stage randomization",
    pays := "design template for learning treatment sequences conditional on intermediate response",
    doesNotPay := "IBS efficacy, numeric switching threshold, or participant mechanism" },
  { sourceReference := "Senarathne/Overstall/McGree 2020 DOI 10.1002/sim.8737",
    designKind := .adaptiveNOf1,
    donorRole := "Bayesian adaptive repeated within-person allocation",
    pays := "design machinery for individual treatment choice and parameter information",
    doesNotPay := "validated IBS posterior, prior, likelihood, or decision threshold" },
  { sourceReference := "Duan et al. 2013 PMID 23849149",
    designKind := .randomizedCrossover,
    donorRole := "patient-centred N-of-1 comparative effectiveness",
    pays := "randomization/crossover/washout and repeated outcome obligations",
    doesNotPay := "automatic suitability when carryover or irreversible change dominates" },
  { sourceReference := "So et al. 2022 DOI 10.1016/j.cgh.2021.12.016",
    designKind := .nutrientPerturbationCrossover,
    donorRole := "Monash fibre/FODMAP physiological perturbation",
    pays := "within-person controlled diet periods with symptom and physiological outcomes",
    doesNotPay := "equivalence of physiological and symptom response" },
  { sourceReference := "Monash Body and Brain IBS study recruiting page, 2026",
    designKind := .protocolOnlyRepeatedChallenge,
    donorRole := "repeated fructan/control challenge protocol",
    pays := "prospective design coupling breath, gut, mental-health and dietary observations",
    doesNotPay := "completed efficacy, mediation, or validated fructan-sensitive subtype" },
  { sourceReference := "Balsiger et al. 2026 DOI 10.1053/j.gastro.2026.08.026",
    designKind := .negativeTargetingValidation,
    donorRole := "falsifier for candidate food-targeting biomarker",
    pays := "controlled evidence one plausible targeting signal failed sham validation",
    doesNotPay := "universal absence of food sensitivity or mucosal mechanisms" },
  { sourceReference := "Garcia-Cedillo et al. 2026 DOI 10.1111/apt.70601",
    designKind := .parallelPersonalizationTrial,
    donorRole := "external less-restrictive personalization comparison",
    pays := "transport evidence for selective restriction versus conventional advice",
    doesNotPay := "superiority, Monash provenance, or validated adaptive policy" }
]

inductive SMARTDesignProvesIBSEfficacyPermission : Prop
inductive NOf1ResultAutomaticallyGeneralizesPermission : Prop
inductive CLEReactionIsValidatedFoodTargetPermission : Prop
inductive RecruitingProtocolCreatesResultPermission : Prop

theorem smartDesignDoesNotProveIBSEfficacy : SMARTDesignProvesIBSEfficacyPermission → False := by intro h; cases h
theorem nOf1DoesNotAutomaticallyGeneralize : NOf1ResultAutomaticallyGeneralizesPermission → False := by intro h; cases h
theorem cleReactionDoesNotValidateFoodTarget : CLEReactionIsValidatedFoodTargetPermission → False := by intro h; cases h
theorem recruitingProtocolDoesNotCreateResult : RecruitingProtocolCreatesResultPermission → False := by intro h; cases h

structure TrialDesignDonorBoundary where
  methodologyAndIBSEvidenceSeparated : Bool
  prospectiveSwitchingRuleRequired : Bool
  washoutCarryoverMustBeAudited : Bool
  negativeValidationCanDowngradeTargetingSignal : Bool
  protocolOnlyEvidenceMarkedProtocolOnly : Bool
  noNumericPolicyInvented : Bool
  deriving Repr, DecidableEq

def canonicalTrialDesignDonorBoundary : TrialDesignDonorBoundary :=
  { methodologyAndIBSEvidenceSeparated := true, prospectiveSwitchingRuleRequired := true,
    washoutCarryoverMustBeAudited := true, negativeValidationCanDowngradeTargetingSignal := true,
    protocolOnlyEvidenceMarkedProtocolOnly := true, noNumericPolicyInvented := true }

structure TrialDesignParetoNode where
  label : String
  paidReference : String
  residual : String
  nextAcquisition : String
  attributionBoundary : String
  deriving Repr, DecidableEq

def canonicalIBSTrialDesignParetoFrontier : List TrialDesignParetoNode := [
  { label := "SMART IBS sequence trial", paidReference := "Collins/Murphy/Strecher 2007 methodology",
    residual := "IBS-specific stages and response definitions unvalidated",
    nextAcquisition := "prospectively define stage-1 choices, response states, stage-2 rerandomization and distal outcome",
    attributionBoundary := "SMART methodology is not IBS efficacy" },
  { label := "adaptive N-of-1 IBS probe", paidReference := "Senarathne 2020 + Duan 2013",
    residual := "actions differ in onset, washout, carryover, burden and reversibility",
    nextAcquisition := "start with short/reversible challenge-rescue actions and explicit carryover model",
    attributionBoundary := "within-person optimality does not automatically generalize" },
  { label := "Monash Body-and-Brain fructan challenge acquisition", paidReference := "current Monash recruiting protocol",
    residual := "results not yet available on cited study page",
    nextAcquisition := "ingest timed breath/symptom/mental-health results when published without upgrading protocol claims retroactively",
    attributionBoundary := "recruitment page is protocol provenance only" },
  { label := "targeting-signal falsification lane", paidReference := "Balsiger 2026 DOI 10.1053/j.gastro.2026.08.026",
    residual := "other proposed targeting biomarkers need comparable sham-controlled validation",
    nextAcquisition := "require biomarker-guided selection to beat sham/usual selection prospectively",
    attributionBoundary := "mechanistic plausibility is not targeting validity" }
]

end Dashi.Biology.IBSTrialDesignDonorAtlasExact
