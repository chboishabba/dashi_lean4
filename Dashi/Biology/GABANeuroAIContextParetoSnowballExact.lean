import Dashi.Biology.GABANeuroAIContextSnowballExact

namespace Dashi.Biology.GABANeuroAIContextParetoSnowballExact

open Dashi.Biology.GABANeuroAIContextSnowballExact

inductive AcquisitionStatus where
  | paidAndWelded
  | boundedEvidenceOnly
  | experimentRequired
  | sourceAcquisitionRequired
  | unresolvedTransfer
  deriving Repr, DecidableEq

inductive AuthorityCeiling where
  | theoremOwnerCeiling
  | sourceBoundAssociationCeiling
  | companyReportCeiling
  | proposalOnlyCeiling
  | noPromotionCeiling
  deriving Repr, DecidableEq

inductive DiscoveryRoute where
  | proofSearch
  | failedFactorsThrough
  | experimentalDesign
  | residualObservation
  | affectedSubjectVoice
  | sourceProvenanceMismatch
  | externalKnowledgeComparison
  deriving Repr, DecidableEq

structure AcquisitionNode where
  label : String
  status : AcquisitionStatus
  discoveryRoute : DiscoveryRoute
  authorityCeiling : AuthorityCeiling
  paidReference : String
  residualOrNextEvidenceShape : String
  feedsFutureLens : Bool
  deriving Repr, DecidableEq

def metaNeuroAIAcquisition : AcquisitionNode := {
  label := "Meta NeuroAI predictive/decoding infrastructure"
  status := .paidAndWelded
  discoveryRoute := .externalKnowledgeComparison
  authorityCeiling := .sourceBoundAssociationCeiling
  paidReference := "TRIBE v2 + Brain2Qwerty v2 + NeuralSet + NeuralBench receipts; Agda side attaches these to FMRIConnectomeProxyGovernance"
  residualOrNextEvidenceShape := "Benchmark generalization across modality, task, subject and naturalistic stimulus while retaining reverse-inference/mind-reading boundaries."
  feedsFutureLens := true
}

def neuroforecastingAcquisition : AcquisitionNode := {
  label := "independent fMRI neuroforecasting of population sharing"
  status := .paidAndWelded
  discoveryRoute := .externalKnowledgeComparison
  authorityCeiling := .sourceBoundAssociationCeiling
  paidReference := "Scholz 2017 plus Chan 2023 preregistered cross-cultural generalization"
  residualOrNextEvidenceShape := "Held-out stimulus families, dynamic content classes, explicit baseline/self-report comparator, and external population outcome."
  feedsFutureLens := true
}

def neuralinkCalibrationAcquisition : AcquisitionNode := {
  label := "Neuralink self-supervised longitudinal decoder stabilization"
  status := .boundedEvidenceOnly
  discoveryRoute := .residualObservation
  authorityCeiling := .companyReportCeiling
  paidReference := "October 2026 company update: >50,000 hours unlabeled neural data, participant-specific pretraining and weeks-without-recalibration; precise weekly burden numbers remain secondary-reported."
  residualOrNextEvidenceShape := "Independent calibration-time distribution, per-participant durability curve, decoder drift metric, and cross-participant transfer benchmark."
  feedsFutureLens := true
}

def crossParticipantDecoderTransferAcquisition : AcquisitionNode := {
  label := "cross-participant BCI decoder transfer"
  status := .unresolvedTransfer
  discoveryRoute := .experimentalDesign
  authorityCeiling := .proposalOnlyCeiling
  paidReference := "Current acquired live results are participant-specific; cross-participant superiority is not established."
  residualOrNextEvidenceShape := "Held-out-participant transfer test with frozen encoder/decoder, matched calibration budget, and longitudinal degradation endpoint."
  feedsFutureLens := true
}

def peripheralCentralTransportAcquisition : AcquisitionNode := {
  label := "peripheral-to-central neurochemical transport"
  status := .experimentRequired
  discoveryRoute := .experimentalDesign
  authorityCeiling := .proposalOnlyCeiling
  paidReference := "GABA ADHD atlas contains peripheral serum and brain-MRS rows that remain non-collapsed."
  residualOrNextEvidenceShape := "Paired central/peripheral measurements or a validated PK/transport/biological model with timing, exposure, assay, compartment and population controls."
  feedsFutureLens := true
}

def dyadicObserverAcquisition : AcquisitionNode := {
  label := "dyadic synchrony with observer plurality"
  status := .paidAndWelded
  discoveryRoute := .affectedSubjectVoice
  authorityCeiling := .sourceBoundAssociationCeiling
  paidReference := "Nguyen synchrony/attachment receipt cross-pollinated with the Agda Alice Brown adult-observation != child-experience and capability/agency boundaries."
  residualOrNextEvidenceShape := "Dyad-indexed participant-specific reports and neural/behavioral synchrony measures without replacing either participant's situated evidence."
  feedsFutureLens := true
}

def levinMultiscaleAcquisition : AcquisitionNode := {
  label := "multiscale bioelectric context"
  status := .paidAndWelded
  discoveryRoute := .externalKnowledgeComparison
  authorityCeiling := .theoremOwnerCeiling
  paidReference := "Agda Levin SI bioelectric-network owner reused as a multiscale signal/control anchor."
  residualOrNextEvidenceShape := "Add CNS-specific bridge only for a selected consumer; do not identify organismal bioelectric control with neural decoding."
  feedsFutureLens := true
}

def canonicalAcquisitionFrontier : List AcquisitionNode := [
  metaNeuroAIAcquisition,
  neuroforecastingAcquisition,
  neuralinkCalibrationAcquisition,
  crossParticipantDecoderTransferAcquisition,
  peripheralCentralTransportAcquisition,
  dyadicObserverAcquisition,
  levinMultiscaleAcquisition
]

structure AcquisitionParetoBoundary where
  agdaParetoOwnerReference : String
  agdaSnowballOwnerReference : String
  frontier : List AcquisitionNode
  numericScientificRankingInvented : Bool
  discoveryDoesNotEqualAdmission : Bool
  experimentPlanDoesNotCreateEvidence : Bool
  authorityCeilingRetainedPerNode : Bool
  deriving Repr, DecidableEq

def canonicalAcquisitionParetoBoundary : AcquisitionParetoBoundary := {
  agdaParetoOwnerReference := "DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact.canonicalRecursiveParetoCompatibility"
  agdaSnowballOwnerReference := "DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact.canonicalDiscoveryAdmissionPolicy"
  frontier := canonicalAcquisitionFrontier
  numericScientificRankingInvented := false
  discoveryDoesNotEqualAdmission := true
  experimentPlanDoesNotCreateEvidence := true
  authorityCeilingRetainedPerNode := true
}

structure GABANeuroAIParetoSnowballBoundary where
  paidNodesRemainSourceOrTheoremBound : Bool
  companyEvidenceStaysCompanyEvidence : Bool
  unresolvedTransportRoutesToExperiment : Bool
  crossParticipantTransferRemainsOpen : Bool
  observerPluralityRetained : Bool
  futureLensMaySnowball : Bool
  deriving Repr, DecidableEq

def canonicalGABANeuroAIParetoSnowballBoundary : GABANeuroAIParetoSnowballBoundary := {
  paidNodesRemainSourceOrTheoremBound := true
  companyEvidenceStaysCompanyEvidence := true
  unresolvedTransportRoutesToExperiment := true
  crossParticipantTransferRemainsOpen := true
  observerPluralityRetained := true
  futureLensMaySnowball := true
}

end Dashi.Biology.GABANeuroAIContextParetoSnowballExact
