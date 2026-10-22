import Dashi.Biology.IBSCausalMaintenanceRegimeExact

namespace Dashi.Biology.IBSResponsePredictorAtlasExact

open Dashi.Biology.IBSCausalMaintenanceRegimeExact

inductive PredictorDomain where
  | microbiomeCompositionPredictor
  | microbialFunctionPredictor
  | metabolitePredictor
  | brainConnectivityPredictor
  | autonomicPredictor
  | psychologicalPredictor
  | multimodalPredictor
  deriving Repr, DecidableEq

inductive PredictorEvidenceStatus where
  | randomizedTrialAssociatedPredictor
  | prospectiveCohortPredictor
  | internallyValidatedModel
  | reviewLevelCandidate
  | externallyValidatedModel
  deriving Repr, DecidableEq

structure TreatmentResponsePredictor where
  sourceReference : String
  treatmentReference : String
  predictorDomains : List PredictorDomain
  evidenceStatus : PredictorEvidenceStatus
  predictedOutcome : String
  validationReference : String
  mediationEstablished : Bool
  externalTransportEstablished : Bool
  participantMechanismIdentified : Bool
  deriving Repr, DecidableEq

def lowFODMAPRifaximinPredictor : TreatmentResponsePredictor := {
  sourceReference := "Lee et al. 2026 DOI 10.1016/j.cgh.2026.04.014"
  treatmentReference := "5-week low-FODMAP versus rifaximin randomized comparison in IBS-D"
  predictorDomains := [.microbiomeCompositionPredictor]
  evidenceStatus := .randomizedTrialAssociatedPredictor
  predictedOutcome := "treatment-specific pain/bloating response"
  validationReference := "distinct baseline taxa associated with response; breath testing inconsistent"
  mediationEstablished := false
  externalTransportEstablished := false
  participantMechanismIdentified := false
}

def cbtBrainGutPredictor : TreatmentResponsePredictor := {
  sourceReference := "Jacobs et al. 2021 DOI 10.1186/s40168-021-01188-6"
  treatmentReference := "cognitive behavioural therapy in IBSOS-derived cohort"
  predictorDomains := [.microbiomeCompositionPredictor, .metabolitePredictor, .brainConnectivityPredictor, .multimodalPredictor]
  evidenceStatus := .internallyValidatedModel
  predictedOutcome := "CBT response"
  validationReference := "internal analyses; reported 11-genus AUROC 0.96; no external validation imported"
  mediationEstablished := false
  externalTransportEstablished := false
  participantMechanismIdentified := false
}

def lowFODMAPPsychologicalPredictor : TreatmentResponsePredictor := {
  sourceReference := "Manning et al. 2026 DOI 10.1002/ueg2.70204"
  treatmentReference := "three-phase low-FODMAP intervention over six months"
  predictorDomains := [.psychologicalPredictor]
  evidenceStatus := .prospectiveCohortPredictor
  predictedOutcome := "symptom and quality-of-life trajectory"
  validationReference := "prospective repeated questionnaires / cross-lagged analyses"
  mediationEstablished := false
  externalTransportEstablished := false
  participantMechanismIdentified := false
}

def aiTranslationReviewPredictor : TreatmentResponsePredictor := {
  sourceReference := "Andafa et al. 2026 DOI 10.7759/cureus.109142"
  treatmentReference := "cross-study IBS brain-gut AI/ML literature"
  predictorDomains := [.multimodalPredictor]
  evidenceStatus := .reviewLevelCandidate
  predictedOutcome := "classification and treatment-response outcomes"
  validationReference := "review emphasizes small cohorts, internal validation, overfitting/data-leakage and replication gaps"
  mediationEstablished := false
  externalTransportEstablished := false
  participantMechanismIdentified := false
}

def canonicalIBSResponsePredictorAtlas : List TreatmentResponsePredictor := [
  lowFODMAPRifaximinPredictor, cbtBrainGutPredictor,
  lowFODMAPPsychologicalPredictor, aiTranslationReviewPredictor
]

inductive PredictorIsMediatorPermission : Prop
inductive InternalPredictionIsValidatedClinicalClassifierPermission : Prop
inductive PredictorIdentifiesMaintenanceRegimePermission : Prop
inductive ResponseAssociationTransportsAcrossTreatmentPermission : Prop

theorem predictorDoesNotBecomeMediator : PredictorIsMediatorPermission → False := by intro h; cases h
theorem internalPredictionDoesNotBecomeClinicalClassifier : InternalPredictionIsValidatedClinicalClassifierPermission → False := by intro h; cases h
theorem predictorDoesNotIdentifyMaintenanceRegime : PredictorIdentifiesMaintenanceRegimePermission → False := by intro h; cases h
theorem responseAssociationDoesNotTransportAcrossTreatment : ResponseAssociationTransportsAcrossTreatmentPermission → False := by intro h; cases h

structure ResponsePredictionWeld where
  treatmentSpecificityRetained : Bool
  predictorMediatorSeparationRetained : Bool
  internalExternalValidationSeparated : Bool
  participantMechanismNotInferredFromPrediction : Bool
  causalRegimeOwnerReference : String
  deriving Repr, DecidableEq

def canonicalResponsePredictionWeld : ResponsePredictionWeld := {
  treatmentSpecificityRetained := true
  predictorMediatorSeparationRetained := true
  internalExternalValidationSeparated := true
  participantMechanismNotInferredFromPrediction := true
  causalRegimeOwnerReference := "IBSCausalMaintenanceRegimeExact; Agda CausalEffectEstimandExact"
}

inductive PredictorAcquisitionStatus where
  | acquiredTreatmentSpecificSignal
  | externalReplicationNeeded
  | calibrationNeeded
  | prospectiveUtilityTrialNeeded
  | causalMediationNeeded
  deriving Repr, DecidableEq

structure ResponsePredictionParetoNode where
  label : String
  status : PredictorAcquisitionStatus
  discoveryRoute : String
  paidReference : String
  residual : String
  nextAcquisition : String
  attributionBoundary : String
  deriving Repr, DecidableEq

def canonicalIBSResponsePredictionParetoFrontier : List ResponsePredictionParetoNode := [
  { label := "treatment-specific microbial response prediction", status := .acquiredTreatmentSpecificSignal,
    discoveryRoute := "externalKnowledgeComparison", paidReference := "Lee 2026 DOI 10.1016/j.cgh.2026.04.014",
    residual := "taxa associations may be cohort/diet/pipeline/treatment-specific",
    nextAcquisition := "external replication with harmonized endpoints, functional omics and adherence",
    attributionBoundary := "associated taxa are neither mediator nor regime classifier" },
  { label := "brain-gut-microbiome CBT response model", status := .externalReplicationNeeded,
    discoveryRoute := "externalKnowledgeComparison", paidReference := "Jacobs 2021 DOI 10.1186/s40168-021-01188-6",
    residual := "small microbiome subset and internal model validation",
    nextAcquisition := "locked-model held-out multi-site replication with calibration and decision threshold",
    attributionBoundary := "reported AUROC is internal prediction evidence, not clinical utility" },
  { label := "psychological modifiers of dietary response", status := .acquiredTreatmentSpecificSignal,
    discoveryRoute := "externalKnowledgeComparison", paidReference := "Manning 2026 DOI 10.1002/ueg2.70204",
    residual := "predictors can be modifiers, mediators, adherence determinants or correlated state",
    nextAcquisition := "joint model with exposure/adherence, biological fibres and treatment interaction",
    attributionBoundary := "association does not establish a purely psychological mechanism" },
  { label := "prospective predictor-guided treatment selection", status := .prospectiveUtilityTrialNeeded,
    discoveryRoute := "experimentalDesign", paidReference := "current predictors mostly exploratory/internal",
    residual := "unknown whether using predictor improves outcomes versus standard selection",
    nextAcquisition := "randomize predictor-guided versus standard allocation with locked model and patient-centred outcomes",
    attributionBoundary := "prediction accuracy alone is not clinical utility" },
  { label := "predictor-to-mediator promotion", status := .causalMediationNeeded,
    discoveryRoute := "experimentalDesign", paidReference := "IBSCausalMaintenanceRegimeExact / Agda CausalEffectEstimandExact",
    residual := "predictive feature may not lie on causal treatment path",
    nextAcquisition := "predeclare mediator and use intervention/comparator/time-specific mediation estimand",
    attributionBoundary := "feature importance or association is not mediation" }
]

structure IBSResponsePredictorBoundary where
  predictorMayAidTreatmentSelectionResearch : Bool
  predictorEqualsMediator : Bool
  internalValidationEqualsExternalValidation : Bool
  predictorEqualsParticipantMechanism : Bool
  predictorAccuracyEqualsClinicalUtility : Bool
  treatmentSpecificityRetained : Bool
  deriving Repr, DecidableEq

def canonicalIBSResponsePredictorBoundary : IBSResponsePredictorBoundary := {
  predictorMayAidTreatmentSelectionResearch := true
  predictorEqualsMediator := false
  internalValidationEqualsExternalValidation := false
  predictorEqualsParticipantMechanism := false
  predictorAccuracyEqualsClinicalUtility := false
  treatmentSpecificityRetained := true
}

end Dashi.Biology.IBSResponsePredictorAtlasExact
