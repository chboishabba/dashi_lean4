import Dashi.Biology.NeuralPredictionDirectionExact
import Dashi.Biology.GABANeuroAIContextParetoSnowballExact

namespace Dashi.Biology.NeuralPredictionAcquisitionParetoExact

open Dashi.Biology.GABAPhenotypeEvidenceExact
open Dashi.Biology.NeuralPredictionDirectionExact

inductive PredictionAcquisitionStatus where
  | acquiredBounded
  | acquiredMechanismBoundary
  | independentReplicationRequired
  | benchmarkExpansionRequired
  | crossModalValidationRequired
  deriving Repr, DecidableEq

inductive PredictionAcquisitionAxis where
  | directionAxis
  | provenanceAxis
  | modalityAxis
  | subjectTransferAxis
  | stimulusTransferAxis
  | populationOutcomeAxis
  | mechanismIdentityAxis
  | calibrationBurdenAxis
  deriving Repr, DecidableEq

inductive DiscoveryRoute where
  | experimentalDesign
  | residualObservation
  | externalKnowledgeComparison
  deriving Repr, DecidableEq

structure PredictionAcquisitionNode where
  label : String
  status : PredictionAcquisitionStatus
  discoveryRoute : DiscoveryRoute
  axis : PredictionAcquisitionAxis
  currentReceiptReference : String
  nextEvidenceShape : String
  authorityBoundary : String
  deriving Repr, DecidableEq

def metaMechanismSeparationAcquisition : PredictionAcquisitionNode := {
  label := "brain-model representation / learning-mechanism separation"
  status := .acquiredMechanismBoundary
  discoveryRoute := .externalKnowledgeComparison
  axis := .mechanismIdentityAxis
  currentReceiptReference := "Meta brain-model convergence 2025 + backprop-gradient misalignment 2026 receipts"
  nextEvidenceShape := "Replicate across architectures, sensory domains and recording modalities while preserving representational-similarity != learning-mechanism identity."
  authorityBoundary := "Meta-authored model/brain comparison; no biological implementation authority."
}

def videoNeuroforecastAcquisition : PredictionAcquisitionNode := {
  label := "dynamic commercial-video neuroforecasting"
  status := .acquiredBounded
  discoveryRoute := .externalKnowledgeComparison
  axis := .stimulusTransferAxis
  currentReceiptReference := "Motoki et al. 2020 video-advertising fMRI/social-sharing receipt"
  nextEvidenceShape := "Cross-platform held-out video sets with frozen feature/ROI definition and independently logged sharing outcomes; compare neural-only, self-report-only, and joint models."
  authorityBoundary := "Forecasting remains stimulus/platform/sample/outcome scoped."
}

def neuralinkIndependentReplicationAcquisition : PredictionAcquisitionNode := {
  label := "Neuralink calibration-burden independent replication"
  status := .independentReplicationRequired
  discoveryRoute := .experimentalDesign
  axis := .calibrationBurdenAxis
  currentReceiptReference := "Primary Neuralink >50k-hour/weeks-without-recalibration source plus secondary exact-burden report"
  nextEvidenceShape := "Independent per-participant calibration-time distribution, decoder-drift survival curve, task-normalized throughput, and adverse/missing-session accounting."
  authorityBoundary := "Company result remains company result until independent clinical/academic replication."
}

def crossParticipantBCIAcquisition : PredictionAcquisitionNode := {
  label := "held-out-participant BCI transfer"
  status := .independentReplicationRequired
  discoveryRoute := .experimentalDesign
  axis := .subjectTransferAxis
  currentReceiptReference := "Cross-participant superiority currently unpaid in acquired Neuralink evidence"
  nextEvidenceShape := "Frozen encoder/decoder evaluated on held-out participants with matched calibration budget, same task definition, longitudinal drift endpoint and explicit failure distribution."
  authorityBoundary := "Within-participant success cannot promote to cross-participant decoder universality."
}

def metaNeuralBenchExpansionAcquisition : PredictionAcquisitionNode := {
  label := "NeuralBench multimodal benchmark expansion"
  status := .benchmarkExpansionRequired
  discoveryRoute := .externalKnowledgeComparison
  axis := .modalityAxis
  currentReceiptReference := "Meta NeuralBench EEG v1.0: 36 tasks, 14 architectures, 94 datasets; preliminary MEG/fMRI extensions"
  nextEvidenceShape := "Common frozen benchmark slices for EEG, MEG, fMRI and spike-model families with modality-specific preprocessing and non-collapsed endpoint semantics."
  authorityBoundary := "Unified benchmark infrastructure does not make modalities equivalent."
}

def neuralinkDatarepoSource : AttributedSource :=
  Dashi.Biology.GABANeuroAIContextSnowballExact.mkNoDOISource
    "Neuralink"
    "datarepo - Neuralink's platform for complex data"
    "Neuralink Updates" "2025"
    "https://neuralink.com/updates/datarepo/"
    "Company-described uniform data-catalog/query interface over heterogeneous operational and scientific data including neural signals, histopathology, surgery video/telemetry and 3D brain scans; software unification is not measurement identity."

structure MultimodalInterfaceBoundary where
  metaNeuralSetReference : String
  neuralinkDatarepoSource : AttributedSource
  commonInterfaceEnablesJointQuery : Bool
  commonInterfaceImpliesMeasurementIdentity : Bool
  crossModalJoinImpliesCausalBridge : Bool
  provenanceMustSurviveJoin : Bool
  assayAndModalitySemanticsRemainTyped : Bool
  deriving Repr, DecidableEq

def canonicalMultimodalInterfaceBoundary : MultimodalInterfaceBoundary := {
  metaNeuralSetReference := "Meta NeuralSet 2026: unified scalable interface for fMRI, M/EEG, spikes and naturalistic stimuli"
  neuralinkDatarepoSource := neuralinkDatarepoSource
  commonInterfaceEnablesJointQuery := true
  commonInterfaceImpliesMeasurementIdentity := false
  crossModalJoinImpliesCausalBridge := false
  provenanceMustSurviveJoin := true
  assayAndModalitySemanticsRemainTyped := true
}

def multimodalInterfaceAcquisition : PredictionAcquisitionNode := {
  label := "multimodal neural data interface with typed measurement semantics"
  status := .crossModalValidationRequired
  discoveryRoute := .externalKnowledgeComparison
  axis := .modalityAxis
  currentReceiptReference := "Meta NeuralSet + Neuralink datarepo infrastructure sources"
  nextEvidenceShape := "Define join receipts preserving modality acquisition protocol, assay semantics, clock/alignment, participant identity boundary and source provenance across shared query surfaces."
  authorityBoundary := "Software interoperability is not measurement equivalence, causal identification, or clinical authority."
}

def canonicalPredictionAcquisitionFrontier : List PredictionAcquisitionNode := [
  metaMechanismSeparationAcquisition,
  videoNeuroforecastAcquisition,
  neuralinkIndependentReplicationAcquisition,
  crossParticipantBCIAcquisition,
  metaNeuralBenchExpansionAcquisition,
  multimodalInterfaceAcquisition
]

structure NeuralPredictionAcquisitionBoundary where
  inheritedParetoOwnerReference : String
  frontier : List PredictionAcquisitionNode
  directionRemainsExplicit : Bool
  provenanceRemainsExplicit : Bool
  softwareUnificationDoesNotCollapseMeasurementTypes : Bool
  mechanismIdentityRemainsSeparateFromPredictivity : Bool
  independentReplicationIsSeparateAcquisitionAxis : Bool
  deriving Repr, DecidableEq

def canonicalNeuralPredictionAcquisitionBoundary : NeuralPredictionAcquisitionBoundary := {
  inheritedParetoOwnerReference := "DASHI.Biology.GABANeuroAIContextParetoSnowballExact.canonicalGABANeuroAIParetoSnowballBoundary"
  frontier := canonicalPredictionAcquisitionFrontier
  directionRemainsExplicit := true
  provenanceRemainsExplicit := true
  softwareUnificationDoesNotCollapseMeasurementTypes := true
  mechanismIdentityRemainsSeparateFromPredictivity := true
  independentReplicationIsSeparateAcquisitionAxis := true
}

end Dashi.Biology.NeuralPredictionAcquisitionParetoExact
