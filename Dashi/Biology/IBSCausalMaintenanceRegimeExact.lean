import Dashi.Biology.IBSMechanismProbePerturbationAtlasExact
import Dashi.Biology.IBSLatentStateTransitionExact

namespace Dashi.Biology.IBSCausalMaintenanceRegimeExact

open Dashi.Biology.IBSGutBrainImmuneSystemsHyperfabricExact
open Dashi.Biology.IBSSystemsIdentificationParetoExact

inductive MaintenanceRegimeCandidate where
  | microbialImmuneCandidate
  | barrierSensoryCandidate
  | autonomicCentralGainCandidate
  | bileAcidMotilityCandidate
  | mixedCoupledCandidate
  deriving Repr, DecidableEq

inductive RegimeAuthority where
  | structuralHypothesisOnly
  | stratificationSupported
  | interventionPredictiveAssociation
  | causalRegimeValidated
  deriving Repr, DecidableEq

structure CandidateMaintenanceRegime where
  label : MaintenanceRegimeCandidate
  dominantFibres : List IBSSystemFibre
  supportingReference : String
  discriminatingObservation : String
  discriminatingPerturbation : String
  currentAuthority : RegimeAuthority
  participantClassifierValidated : Bool
  causalClosureClaimed : Bool
  deriving Repr, DecidableEq

def microbialImmuneRegime : CandidateMaintenanceRegime := {
  label := .microbialImmuneCandidate
  dominantFibres := [.microbiomeMetaboliteFibre, .mucosalImmuneMastCellFibre, .epithelialBarrierFibre]
  supportingReference := "Black 2026 integrated pathophysiology; existing histamine/LPS-mast-cell lanes; Mars 2020 longitudinal multi-omics"
  discriminatingObservation := "repeated microbial function + metabolome + mast-cell/immune + barrier measures around flare/recovery"
  discriminatingPerturbation := "microbiome-directed or diet/substrate perturbation with matched non-microbial fibres measured"
  currentAuthority := .structuralHypothesisOnly
  participantClassifierValidated := false
  causalClosureClaimed := false
}

def barrierSensoryRegime : CandidateMaintenanceRegime := {
  label := .barrierSensoryCandidate
  dominantFibres := [.epithelialBarrierFibre, .visceralSensoryNociceptiveFibre, .mucosalImmuneMastCellFibre]
  supportingReference := "Black 2026 review plus Gao barrier/mast-cell and H1/TRPV1 evidence lanes"
  discriminatingObservation := "barrier/permeability + visceral sensitivity + mast-cell/histamine trajectories"
  discriminatingPerturbation := "barrier- or sensory-targeted perturbation with proximal target engagement and distal symptom trajectory"
  currentAuthority := .structuralHypothesisOnly
  participantClassifierValidated := false
  causalClosureClaimed := false
}

def autonomicCentralRegime : CandidateMaintenanceRegime := {
  label := .autonomicCentralGainCandidate
  dominantFibres := [.autonomicHPAAllostaticFibre, .centralPainInteroceptiveFibre, .visceralSensoryNociceptiveFibre]
  supportingReference := "Bai 2026 ANS review; Jarrett 2015 DOI 10.5056/jnm15067; Lowen 2013 intervention/fMRI"
  discriminatingObservation := "dense autonomic + interoceptive/central + symptom trajectories with peripheral fibres retained"
  discriminatingPerturbation := "brain-gut behavioural or neuromodulatory perturbation with peripheral and central readouts"
  currentAuthority := .interventionPredictiveAssociation
  participantClassifierValidated := false
  causalClosureClaimed := false
}

def bileAcidMotilityRegime : CandidateMaintenanceRegime := {
  label := .bileAcidMotilityCandidate
  dominantFibres := [.neurochemicalMetabolicFibre, .entericMotilitySecretionFibre, .microbiomeMetaboliteFibre]
  supportingReference := "Di Ciaula 2024 bile-acid review and colesevelam mechanism-probe lane"
  discriminatingObservation := "C4/FGF19/fecal bile acids + transit + microbiome + symptom trajectory"
  discriminatingPerturbation := "bile-acid sequestration or other validated bile-acid perturbation with target engagement"
  currentAuthority := .stratificationSupported
  participantClassifierValidated := false
  causalClosureClaimed := false
}

def mixedCoupledRegime : CandidateMaintenanceRegime := {
  label := .mixedCoupledCandidate
  dominantFibres := [.microbiomeMetaboliteFibre, .epithelialBarrierFibre, .mucosalImmuneMastCellFibre,
    .autonomicHPAAllostaticFibre, .centralPainInteroceptiveFibre, .visceralSensoryNociceptiveFibre]
  supportingReference := "Black 2026 integrated DGBI model and IBS whole-system hyperfabric"
  discriminatingObservation := "multi-fibre repeated panel with transition and response data"
  discriminatingPerturbation := "orthogonal sequential perturbations; no one intervention assumed sufficient"
  currentAuthority := .structuralHypothesisOnly
  participantClassifierValidated := false
  causalClosureClaimed := false
}

def canonicalCandidateMaintenanceRegimeAtlas : List CandidateMaintenanceRegime := [
  microbialImmuneRegime, barrierSensoryRegime, autonomicCentralRegime,
  bileAcidMotilityRegime, mixedCoupledRegime
]

inductive SymptomPatternIdentifiesMaintenanceRegimePermission : Prop
inductive SingleInterventionResponseIdentifiesUniqueRegimePermission : Prop
inductive BiomarkerPanelEqualsCausalRegimePermission : Prop
inductive PredictiveBiomarkerIsMediatorPermission : Prop

theorem symptomPatternDoesNotIdentifyMaintenanceRegime :
    SymptomPatternIdentifiesMaintenanceRegimePermission → False := by intro h; cases h

theorem singleInterventionResponseDoesNotIdentifyUniqueRegime :
    SingleInterventionResponseIdentifiesUniqueRegimePermission → False := by intro h; cases h

theorem biomarkerPanelDoesNotEqualCausalRegime :
    BiomarkerPanelEqualsCausalRegimePermission → False := by intro h; cases h

theorem predictiveBiomarkerDoesNotBecomeMediator :
    PredictiveBiomarkerIsMediatorPermission → False := by intro h; cases h

structure RegimeDiscriminationPanel where
  symptomTrajectory : MeasurementAxis
  microbialFunction : MeasurementAxis
  metabolome : MeasurementAxis
  immuneMastCell : MeasurementAxis
  barrier : MeasurementAxis
  bileAcid : MeasurementAxis
  autonomic : MeasurementAxis
  visceralSensitivity : MeasurementAxis
  centralInteroception : MeasurementAxis
  exposure : MeasurementAxis
  repeatedWithinPerson : Bool
  eventTriggeredSampling : Bool
  atLeastTwoOrthogonalPerturbationsPreferred : Bool
  historyLedgerRequired : Bool
  validatedClinicalClassifier : Bool
  deriving Repr, DecidableEq

def canonicalRegimeDiscriminationPanel : RegimeDiscriminationPanel := {
  symptomTrajectory := .symptomTrajectoryAxis
  microbialFunction := .microbiomeFunctionAxis
  metabolome := .metabolomeAxis
  immuneMastCell := .histamineMastCellAxis
  barrier := .epithelialBarrierAxis
  bileAcid := .bileAcidAxis
  autonomic := .autonomicAxis
  visceralSensitivity := .visceralSensitivityAxis
  centralInteroception := .centralInteroceptivePainAxis
  exposure := .dietExposureAxis
  repeatedWithinPerson := true
  eventTriggeredSampling := true
  atLeastTwoOrthogonalPerturbationsPreferred := true
  historyLedgerRequired := true
  validatedClinicalClassifier := false
}

structure MaintenanceCausalEstimandObligation where
  targetRegime : MaintenanceRegimeCandidate
  interventionReference : String
  comparatorReference : String
  proximalOutcomeReference : String
  distalOutcomeReference : String
  timeHorizonReference : String
  mediatorIfClaimedMustBeExplicit : Bool
  populationAndIndividualEffectsRemainDistinct : Bool
  agdaOwnerReference : String
  deriving Repr, DecidableEq

def canonicalMaintenanceCausalEstimandObligation : MaintenanceCausalEstimandObligation := {
  targetRegime := .mixedCoupledCandidate
  interventionReference := "mechanism-selective perturbation, predeclared"
  comparatorReference := "matched sham/control/alternative fibre perturbation"
  proximalOutcomeReference := "proximal target-engagement coordinate"
  distalOutcomeReference := "symptom/functional trajectory plus competing-fibre responses"
  timeHorizonReference := "predeclared acute + recovery + persistence horizons"
  mediatorIfClaimedMustBeExplicit := true
  populationAndIndividualEffectsRemainDistinct := true
  agdaOwnerReference := "DASHI.Biology.CausalEffectEstimandExact"
}

inductive RegimeAcquisitionStatus where
  | boundedEvidenceAcquired
  | prospectiveDiscriminationNeeded
  | orthogonalPerturbationNeeded
  | mediatorIdentificationNeeded
  | externalTransportNeeded
  deriving Repr, DecidableEq

structure CausalMaintenanceParetoNode where
  label : String
  status : RegimeAcquisitionStatus
  discoveryRoute : String
  sourceOrOwnerReference : String
  residual : String
  acquisition : String
  attributionBoundary : String
  deriving Repr, DecidableEq

def canonicalCausalMaintenanceParetoFrontier : List CausalMaintenanceParetoNode := [
  { label := "autonomic baseline as differential-response predictor", status := .boundedEvidenceAcquired,
    discoveryRoute := "externalKnowledgeComparison", sourceOrOwnerReference := "Jarrett 2015 DOI 10.5056/jnm15067",
    residual := "prediction may reflect effect modification or correlated state rather than mediation",
    acquisition := "replicate preregistered treatment-by-autonomic interaction with gut/immune/central measurements",
    attributionBoundary := "predictive moderation is not mediation or unique regime identification" },
  { label := "multi-fibre brain-gut intervention measurement", status := .prospectiveDiscriminationNeeded,
    discoveryRoute := "experimentalDesign", sourceOrOwnerReference := "WISH 2.0 protocol DOI 10.2196/98352",
    residual := "protocol has not produced efficacy or mediation evidence",
    acquisition := "retain treatment/control and proximal/distal/mediator outcomes when results mature",
    attributionBoundary := "planned measurement is not acquired causal evidence" },
  { label := "autonomic neuromodulation as system probe", status := .boundedEvidenceAcquired,
    discoveryRoute := "externalKnowledgeComparison", sourceOrOwnerReference := "Wei et al. 2026 DOI 10.1177/17562848261436121",
    residual := "low/very-low quality evidence and heterogeneous modalities/subtypes",
    acquisition := "larger sham-controlled trials with HRV plus peripheral panel and trajectories",
    attributionBoundary := "clinical benefit does not prove autonomic-only maintenance" },
  { label := "orthogonal sequential perturbation discrimination", status := .orthogonalPerturbationNeeded,
    discoveryRoute := "experimentalDesign", sourceOrOwnerReference := "IBSMechanismProbePerturbationAtlasExact",
    residual := "one responder contrast cannot separate shared downstream pathways",
    acquisition := "within-person randomized/crossover sequence of fibre-distinct probes with washout and common panel",
    attributionBoundary := "response pattern does not identify regime without target engagement" },
  { label := "causal mediator identification", status := .mediatorIdentificationNeeded,
    discoveryRoute := "experimentalDesign", sourceOrOwnerReference := "Agda CausalEffectEstimandExact mediation surface",
    residual := "associations/predictors are not controlled direct or mediated indirect effects",
    acquisition := "predeclare mediator, intervention, comparator, population and time",
    attributionBoundary := "candidate pathway label is not a mediation receipt" },
  { label := "held-out maintenance-regime transport", status := .externalTransportNeeded,
    discoveryRoute := "externalKnowledgeComparison", sourceOrOwnerReference := "current cohorts/interventions are context-specific",
    residual := "discriminator may fail across diet, geography, sex, infection history, assay or treatment context",
    acquisition := "held-out multi-site validation of discrimination contract and treatment interactions",
    attributionBoundary := "internal discrimination does not automatically transport" }
]

structure IBSCausalMaintenanceBoundary where
  candidateRegimesAreHypotheses : Bool
  symptomSubtypeDefinesRegime : Bool
  predictiveBiomarkerDefinesMediator : Bool
  singleTreatmentResponseDefinesRegime : Bool
  causalEstimandMustRemainExplicit : Bool
  multiFibreLongitudinalPerturbationPreferred : Bool
  participantClassifierValidated : Bool
  agdaOwnerReferences : String
  deriving Repr, DecidableEq

def canonicalIBSCausalMaintenanceBoundary : IBSCausalMaintenanceBoundary := {
  candidateRegimesAreHypotheses := true
  symptomSubtypeDefinesRegime := false
  predictiveBiomarkerDefinesMediator := false
  singleTreatmentResponseDefinesRegime := false
  causalEstimandMustRemainExplicit := true
  multiFibreLongitudinalPerturbationPreferred := true
  participantClassifierValidated := false
  agdaOwnerReferences := "IBSGutBrainImmuneSystemsHyperfabricExact; IBSLatentStateTransitionExact; IBSMechanismProbePerturbationAtlasExact; CausalEffectEstimandExact"
}

end Dashi.Biology.IBSCausalMaintenanceRegimeExact
