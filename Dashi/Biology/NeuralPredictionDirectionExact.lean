import Dashi.Biology.GABANeuroAIContextSnowballExact

namespace Dashi.Biology.NeuralPredictionDirectionExact

open Dashi.Biology.GABAPhenotypeEvidenceExact
open Dashi.Biology.GABANeuroAIContextSnowballExact

inductive NeuralPredictionDirection where
  | stimulusToBrainEncoding
  | brainToLanguageDecoding
  | brainToActionDecoding
  | brainResponseToPopulationOutcome
  deriving Repr, DecidableEq

inductive PredictionScope where
  | withinSubjectScope
  | heldOutSubjectScope
  | heldOutStimulusScope
  | crossPopulationScope
  | populationAggregateScope
  deriving Repr, DecidableEq

structure DirectionalPredictionReceipt where
  direction : NeuralPredictionDirection
  source : AttributedSource
  scope : PredictionScope
  inputReference : String
  outputReference : String
  validationReference : String
  authorityBoundary : String
  deriving Repr, DecidableEq

def metaTRIBEDirectionalReceipt : DirectionalPredictionReceipt := {
  direction := .stimulusToBrainEncoding
  source := metaTRIBEv2Source
  scope := .heldOutSubjectScope
  inputReference := "naturalistic visual/audio/language stimuli plus model/context inputs"
  outputReference := "predicted high-resolution fMRI response"
  validationReference := "Meta-reported zero-shot prediction across new subjects, languages and tasks in its evaluation"
  authorityBoundary := "encoding prediction is not thought identity, diagnosis, or unrestricted decoding"
}

def metaBrain2QwertyDirectionalReceipt : DirectionalPredictionReceipt := {
  direction := .brainToLanguageDecoding
  source := metaBrain2QwertySource
  scope := .withinSubjectScope
  inputReference := "non-invasive neural recordings during the reported sentence-decoding protocol"
  outputReference := "decoded natural-language sentence/text representation"
  validationReference := "reported end-to-end real-time decoding evaluation"
  authorityBoundary := "task-bounded decoding is not unrestricted mind reading"
}

def neuralinkActionDirectionalReceipt : DirectionalPredictionReceipt := {
  direction := .brainToActionDecoding
  source := neuralink2026PretrainingSource
  scope := .withinSubjectScope
  inputReference := "participant-specific intracortical neural activity"
  outputReference := "intended computer-control action / cursor decoder output"
  validationReference := "company-reported participant-specific self-supervised pretraining and longitudinal decoder-use result"
  authorityBoundary := "company result; within-participant BCI decoding is not cross-participant universality or general thought decoding"
}

def scholzNeuroforecastDirectionalReceipt : DirectionalPredictionReceipt := {
  direction := .brainResponseToPopulationOutcome
  source := scholz2017ViralitySource
  scope := .populationAggregateScope
  inputReference := "fMRI responses to health-news articles in laboratory participants"
  outputReference := "objective population-level article-sharing outcome"
  validationReference := "population neuroforecasting analysis reported by Scholz et al."
  authorityBoundary := "scoped sharing prediction is not an intrinsic universal virality score and is not Meta-authored"
}

def metaBackpropMisalignmentSource : AttributedSource :=
  mkNoDOISource
    "Josephine Raugel; Max Seitzer; Marc Szafraniec; Huy V. Vo; Jérémy Rapin; Patrick Labatut; Piotr Bojanowski; Valentin Wyart; Jean Remi King"
    "Misalignment Between Backpropagation and the Hierarchy of Brain Responses to Images"
    "AI at Meta Research / arXiv" "2026"
    "https://ai.meta.com/research/publications/misalignment-between-backpropagation-and-the-hierarchy-of-brain-responses-to-images/"
    "Meta reports that backpropagated gradients can predict selected fMRI/MEG signals while spatial/temporal organization diverges from biologically plausible backpropagation; predictivity is not mechanistic identity."

structure BrainModelMechanismBoundary where
  representationalSimilarityImpliesMechanisticIdentity : Bool
  gradientPredictivityImpliesBiologicalBackprop : Bool
  commonBenchmarkImpliesMeasurementEquivalence : Bool
  encodingAccuracyImpliesDecodingAuthority : Bool
  deriving Repr, DecidableEq

def canonicalBrainModelMechanismBoundary : BrainModelMechanismBoundary := {
  representationalSimilarityImpliesMechanisticIdentity := false
  gradientPredictivityImpliesBiologicalBackprop := false
  commonBenchmarkImpliesMeasurementEquivalence := false
  encodingAccuracyImpliesDecodingAuthority := false
}

def motoki2020Source : AttributedSource :=
  Dashi.Biology.GABAPhenotypeEvidenceExact.mkDOISource
    "Kosuke Motoki; Shinsuke Suzuki; Ryuta Kawashima; Motoaki Sugiura"
    "A Combination of Self-Reported Data and Social-Related Neural Measures Forecasts Viral Marketing Success on Social Media"
    "Journal of Interactive Marketing 52(1)" "2020"
    "10.1016/j.intmar.2020.06.003"
    "https://doi.org/10.1016/j.intmar.2020.06.003"
    "Commercial-video neuroforecasting study; scoped to its video ads, sample, platform outcome and model."

def motoki2020VideoNeuroforecastReceipt : DirectionalPredictionReceipt := {
  direction := .brainResponseToPopulationOutcome
  source := motoki2020Source
  scope := .populationAggregateScope
  inputReference := "fMRI/social-related neural measures and self-report while participants viewed video advertisements"
  outputReference := "aggregate social-media sharing / viral-marketing outcome"
  validationReference := "reported forecasting model combining self-report and social-related neural measures"
  authorityBoundary := "commercial-video result is not a general-purpose virality oracle"
}

def insideBCI2026CalibrationSource : AttributedSource :=
  mkNoDOISource
    "Inside BCI"
    "Neuralink cuts some implant users' calibration from 10 minutes a day to 10 minutes a week"
    "Inside BCI" "2026"
    "https://insidebci.com/news/2026-10-03-neuralink-pretraining-50000-hours-brain-data-calibration-decoder-11-bps/"
    "Secondary report of exact calibration-burden figures attributed to Neuralink's October 2026 update; not independent validation."

structure NeuralinkProvenanceSplit where
  primarySource : AttributedSource
  secondaryExactBurdenSource : AttributedSource
  primaryPaidClaim : String
  secondaryPaidClaim : String
  exactBurdenNumbersAttributedToSecondary : Bool
  independentReplicationEstablished : Bool
  deriving Repr, DecidableEq

def canonicalNeuralinkProvenanceSplit : NeuralinkProvenanceSplit := {
  primarySource := neuralink2026PretrainingSource
  secondaryExactBurdenSource := insideBCI2026CalibrationSource
  primaryPaidClaim := ">50,000 hours unlabeled neural data; participant-specific self-supervised encoders; weeks without recalibration; 11.32 BPS reported"
  secondaryPaidClaim := "prior routine about 10 min/day, average 55 min/week; some participants about 10 min/week"
  exactBurdenNumbersAttributedToSecondary := true
  independentReplicationEstablished := false
}

inductive ExperimentalDesignSlot where
  | sourcePopulationSlot
  | baselineMeasurementSlot
  | endpointMeasurementSlot
  | timeSlot
  | assaySlot
  | nuisanceControlSlot
  | transportSlot
  deriving Repr, DecidableEq

structure PeripheralCentralPKDesignBridge where
  agdaPKPDDonorReference : String
  transportSlot : ExperimentalDesignSlot
  timeSlot : ExperimentalDesignSlot
  assaySlot : ExperimentalDesignSlot
  sourcePopulationSlot : ExperimentalDesignSlot
  doseExposureOrEndogenousLevelRequired : Bool
  pairedCompartmentOrValidatedTransportRequired : Bool
  donorChemistryTransferredAsIdentity : Bool
  deriving Repr, DecidableEq

def canonicalPeripheralCentralPKDesignBridge : PeripheralCentralPKDesignBridge := {
  agdaPKPDDonorReference := "DASHI.Wikimedia.IbrahimCannabisTerpeneEntourageMoleculeCrossPollinationExact.fourthParetoStep: explicit human PK/PD exposure/composition/comparator obligation only; chemistry not transferred"
  transportSlot := .transportSlot
  timeSlot := .timeSlot
  assaySlot := .assaySlot
  sourcePopulationSlot := .sourcePopulationSlot
  doseExposureOrEndogenousLevelRequired := true
  pairedCompartmentOrValidatedTransportRequired := true
  donorChemistryTransferredAsIdentity := false
}

structure CrossParticipantBCIDesignMap where
  sourcePopulationSlot : ExperimentalDesignSlot
  baselineSlot : ExperimentalDesignSlot
  endpointSlot : ExperimentalDesignSlot
  timeSlot : ExperimentalDesignSlot
  nuisanceSlot : ExperimentalDesignSlot
  agdaBackpropOwnerReference : String
  heldOutParticipantRequired : Bool
  matchedCalibrationBudgetRequired : Bool
  longitudinalDriftEndpointRequired : Bool
  deriving Repr, DecidableEq

def canonicalCrossParticipantBCIDesignMap : CrossParticipantBCIDesignMap := {
  sourcePopulationSlot := .sourcePopulationSlot
  baselineSlot := .baselineMeasurementSlot
  endpointSlot := .endpointMeasurementSlot
  timeSlot := .timeSlot
  nuisanceSlot := .nuisanceControlSlot
  agdaBackpropOwnerReference := "DASHI.Reasoning.BlockedImplicationExperimentBackpropExact.canonicalBlockedImplicationBackpropBoundary"
  heldOutParticipantRequired := true
  matchedCalibrationBudgetRequired := true
  longitudinalDriftEndpointRequired := true
}

structure NeuralPredictionDirectionBoundary where
  encodingAndDecodingAreDistinct : Bool
  languageAndActionDecodingAreDistinct : Bool
  decodingAndNeuroforecastingAreDistinct : Bool
  fMRIProxyGovernanceRetained : Bool
  neuralinkPrimarySecondaryProvenanceSplit : Bool
  blockedTransfersBackpropagateToExactDesignSlots : Bool
  deriving Repr, DecidableEq

def canonicalNeuralPredictionDirectionBoundary : NeuralPredictionDirectionBoundary := {
  encodingAndDecodingAreDistinct := true
  languageAndActionDecodingAreDistinct := true
  decodingAndNeuroforecastingAreDistinct := true
  fMRIProxyGovernanceRetained := true
  neuralinkPrimarySecondaryProvenanceSplit := true
  blockedTransfersBackpropagateToExactDesignSlots := true
}

end Dashi.Biology.NeuralPredictionDirectionExact
