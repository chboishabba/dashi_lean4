import Dashi.Biology.GABAPhenotypeEvidenceInstantiationExact

namespace Dashi.Biology.GABANeuroAIContextSnowballExact

open Dashi.Biology.GABAPhenotypeEvidenceExact
open Dashi.Biology.GABAPhenotypeEvidenceInstantiationExact

inductive NeuroAISourceRole where
  | metaAuthoredNeuroAI
  | independentNeuroforecasting
  | companyBCIUpdate
  deriving Repr, DecidableEq

inductive NeuralModality where
  | fMRI
  | fMRIMEG
  | EEGMEG
  | intracorticalSpikes
  | multimodalNeuralRecordings
  deriving Repr, DecidableEq

structure NeuroAISourceReceipt where
  source : AttributedSource
  role : NeuroAISourceRole
  modality : NeuralModality
  paidClaim : String
  boundary : String
  deriving Repr, DecidableEq

structure NeuroforecastingSourceReceipt where
  source : AttributedSource
  modality : NeuralModality
  populationOutcome : String
  paidClaim : String
  boundary : String
  deriving Repr, DecidableEq

def mkNoDOISource
    (authors title publicationContext year canonicalURL relationship : String) :
    AttributedSource := {
  authors := authors
  title := title
  publicationContext := publicationContext
  year := year
  doi := ""
  canonicalURL := canonicalURL
  relationship := relationship
  citationImportsProof := false
  citationCreatesAuthority := false
}

def metaTRIBEv2Source : AttributedSource :=
  mkNoDOISource "Meta FAIR"
    "Introducing TRIBE v2: A Predictive Foundation Model Trained to Understand How the Human Brain Processes Complex Stimuli"
    "AI at Meta" "2026"
    "https://ai.meta.com/blog/tribe-v2-brain-predictive-foundation-model"
    "Meta-authored report of high-resolution fMRI response prediction over naturalistic stimuli across a large healthy-volunteer dataset; prediction is not thought identity or clinical authority."

def metaBrain2QwertySource : AttributedSource :=
  mkNoDOISource "Meta FAIR"
    "From Brain Waves to Words: Brain2Qwerty Offers a New Path to Communication Without Surgery"
    "AI at Meta" "2026"
    "https://ai.meta.com/blog/brain2qwerty-brain-ai-human-communication/"
    "Meta-authored report of improved real-time neural-to-text decoding from non-invasive recordings; task-bounded decoding is not unrestricted mind reading."

def metaNeuralSetSource : AttributedSource :=
  mkNoDOISource "Jean Remi King et al.; Meta FAIR"
    "NeuralSet: A High-Performing Python Package for Neuro-AI"
    "AI at Meta Research" "2026"
    "https://ai.meta.com/research/publications/neuralset-a-high-performing-python-package-for-neuro-ai/"
    "Unified computational interface across fMRI, M/EEG, spikes and naturalistic stimuli; common software infrastructure does not identify modalities as semantically interchangeable."

def metaNeuralBenchSource : AttributedSource :=
  mkNoDOISource "Hubert Banville et al.; Meta FAIR"
    "NeuralBench: A Unifying Framework to Benchmark NeuroAI Models"
    "AI at Meta Research" "2026"
    "https://ai.meta.com/research/publications/neuralbench-a-unifying-framework-to-benchmark-neuroai-models/"
    "Benchmark framework for NeuroAI models; benchmark score does not create clinical or mechanistic authority."

def neuralink2026PretrainingSource : AttributedSource :=
  mkNoDOISource "Neuralink"
    "Pretraining on 50,000 Hours of Unlabeled Brain Data"
    "Neuralink Updates" "2026"
    "https://neuralink.com/updates/"
    "Company-reported self-supervised pretraining result reducing recalibration burden for some participants; not independent replication or a population-wide guarantee."

def scholz2017ViralitySource : AttributedSource :=
  Dashi.Biology.GABAPhenotypeEvidenceExact.mkDOISource
    "Christin Scholz; Elisa C Baek; Matthew Brook O'Donnell; Hyun Suk Kim; Joseph N Cappella; Emily B Falk"
    "A neural model of valuation and information virality"
    "Proceedings of the National Academy of Sciences 114(11):2881-2886"
    "2017" "10.1073/pnas.1615259114"
    "https://doi.org/10.1073/pnas.1615259114"
    "Independent academic fMRI neuroforecasting study linking value/self/social neural signals to objectively logged population sharing; not a Meta-authored virality model or universal virality oracle."

def chan2023SharingSource : AttributedSource :=
  Dashi.Biology.GABAPhenotypeEvidenceExact.mkDOISource
    "Hang-Yee Chan; Christin Scholz; Danielle Cosme; Rebecca E Martin; Christian Benitez; Anthony Resnick; Jose Carreras-Tartak; Nicole Cooper; Alexandra M Paul; Emily B Falk"
    "Neural signals predict information sharing across cultures"
    "Proceedings of the National Academy of Sciences 120(44):e2313175120"
    "2023" "10.1073/pnas.2313175120"
    "https://doi.org/10.1073/pnas.2313175120"
    "Preregistered cross-cultural generalization of a brain-based information-sharing prediction model; scope remains the studied stimuli, samples and outcome."

def metaTRIBEv2Receipt : NeuroAISourceReceipt := {
  source := metaTRIBEv2Source
  role := .metaAuthoredNeuroAI
  modality := .fMRI
  paidClaim := "predictive encoding model for high-resolution fMRI responses to complex naturalistic stimuli"
  boundary := "prediction remains a proxy/model relation, not hidden-state identity"
}

def metaBrain2QwertyReceipt : NeuroAISourceReceipt := {
  source := metaBrain2QwertySource
  role := .metaAuthoredNeuroAI
  modality := .EEGMEG
  paidClaim := "non-invasive neural-to-text decoding under the reported experimental pipeline"
  boundary := "task-bounded decoding is not unrestricted mind reading"
}

def scholz2017ViralityReceipt : NeuroforecastingSourceReceipt := {
  source := scholz2017ViralitySource
  modality := .fMRI
  populationOutcome := "objectively logged population-level sharing of New York Times articles"
  paidClaim := "value/self/social neural signals add predictive information for sharing outcomes"
  boundary := "independent academic neuroforecasting, not Meta-authored and not a universal content-virality oracle"
}

def chan2023SharingReceipt : NeuroforecastingSourceReceipt := {
  source := chan2023SharingSource
  modality := .fMRI
  populationOutcome := "population sharing of US news articles across US and Netherlands samples"
  paidClaim := "preregistered brain-based prediction generalized across samples/cultures better than self-report alone"
  boundary := "generalization remains scoped to the studied paradigm and stimuli"
}

structure DyadicObserverPluralityBridge where
  synchronyAttachmentAssociation : SynchronyAttachmentAssociationReceipt
  aliceBrownOwnerReference : String
  adultObservationDoesNotEqualChildExperience : Bool
  dyadicMeasurementDoesNotCollapseParticipantVoices : Bool
  deriving Repr, DecidableEq

def canonicalDyadicObserverPluralityBridge : DyadicObserverPluralityBridge := {
  synchronyAttachmentAssociation := nguyen2024SynchronyAttachmentAssociation
  aliceBrownOwnerReference := "DASHI.Biology.AliceBrownThreadInquirySynthesisExact: adultObservationDoesNotEqualChildExperience; capability expansion without domination"
  adultObservationDoesNotEqualChildExperience := true
  dyadicMeasurementDoesNotCollapseParticipantVoices := true
}

structure FMRIProxyAttachment where
  sourceReceipt : NeuroAISourceReceipt
  agdaGovernanceOwnerReference : String
  proxyBoundaryRetained : Bool
  mindReadingPromotionBlocked : Bool
  deriving Repr, DecidableEq

def metaTRIBEProxyAttachment : FMRIProxyAttachment := {
  sourceReceipt := metaTRIBEv2Receipt
  agdaGovernanceOwnerReference := "DASHI.Biology.FMRIConnectomeProxyGovernance.canonicalFMRIConnectomeProxyGovernance"
  proxyBoundaryRetained := true
  mindReadingPromotionBlocked := true
}

structure LevinMultiscaleSignalAnchor where
  agdaOwnerReference : String
  multiscaleBioelectricOwnerReused : Bool
  brainOnlyOntologyIntroduced : Bool
  deriving Repr, DecidableEq

def canonicalLevinMultiscaleSignalAnchor : LevinMultiscaleSignalAnchor := {
  agdaOwnerReference := "DASHI.Biology.Physical.SIBioelectricNetworkAdapterExact.canonicalSIBioelectricNetwork"
  multiscaleBioelectricOwnerReused := true
  brainOnlyOntologyIntroduced := false
}

structure BCICalibrationBurdenReceipt where
  source : AttributedSource
  baselineReference : String
  updatedReference : String
  selfSupervisedPretrainingReference : String
  participantSpecificModels : Bool
  crossParticipantSuperiorityEstablished : Bool
  independentReplicationEstablished : Bool
  deriving Repr, DecidableEq

def neuralink2026CalibrationReceipt : BCICalibrationBurdenReceipt := {
  source := neuralink2026PretrainingSource
  baselineReference := "company-reported historical calibration averaged about 55 minutes/week, typically around 10 minutes/day"
  updatedReference := "company reports some participants now calibrate about 10 minutes/week, with some decoders remaining useful for weeks"
  selfSupervisedPretrainingReference := "participant-specific self-supervised encoders pretrained on thousands of hours drawn from more than 50,000 hours of unlabeled everyday neural recordings"
  participantSpecificModels := true
  crossParticipantSuperiorityEstablished := false
  independentReplicationEstablished := false
}

inductive NeurochemicalCompartment where
  | centralBrainMeasurement
  | peripheralBloodMeasurement
  | extracellularLocalMeasurement
  deriving Repr, DecidableEq

inductive PeripheralCentralTransportPermission : Prop

theorem peripheralCentralTransportNotAutomatic : PeripheralCentralTransportPermission → False := by
  intro h
  cases h

inductive DiscoveryRoute where
  | experimentalDesign
  | residualObservation
  | sourceAcquisition
  deriving Repr, DecidableEq

structure TransportExperimentRequirement where
  sourceCompartment : NeurochemicalCompartment
  targetCompartment : NeurochemicalCompartment
  discoveryRoute : DiscoveryRoute
  transportModelRequired : Bool
  pairedMeasurementOrValidatedModelRequired : Bool
  pharmacokineticOrBiologicalMechanismRequired : Bool
  requirementReference : String
  deriving Repr, DecidableEq

def peripheralToCentralExperimentRequirement : TransportExperimentRequirement := {
  sourceCompartment := .peripheralBloodMeasurement
  targetCompartment := .centralBrainMeasurement
  discoveryRoute := .experimentalDesign
  transportModelRequired := true
  pairedMeasurementOrValidatedModelRequired := true
  pharmacokineticOrBiologicalMechanismRequired := true
  requirementReference := "Blocked peripheral-to-central inference backpropagates to paired/linked compartments or a validated transport/PK/biological model with timing, exposure, assay and population controls."
}

structure NeuroforecastExperimentRequirement where
  discoveryRoute : DiscoveryRoute
  stimulusGeneralizationRequired : Bool
  outOfSamplePopulationOutcomeRequired : Bool
  selfReportComparatorRequired : Bool
  modalityAndPipelineFrozen : Bool
  requirementReference : String
  deriving Repr, DecidableEq

def canonicalNeuroforecastExperimentRequirement : NeuroforecastExperimentRequirement := {
  discoveryRoute := .experimentalDesign
  stimulusGeneralizationRequired := true
  outOfSamplePopulationOutcomeRequired := true
  selfReportComparatorRequired := true
  modalityAndPipelineFrozen := true
  requirementReference := "Use held-out stimuli/population outcomes, frozen or preregistered neural features, and behavioral/self-report comparators before broad promotion."
}

structure GABANeuroAIContextBoundary where
  metaNeuroAIKeptDistinctFromIndependentViralityResearch : Bool
  fmriPredictionDoesNotBecomeMindReading : Bool
  dyadicSignalsDoNotCollapseObserverPlurality : Bool
  peripheralToCentralTransportAutomatic : Bool
  neuralinkWeeklyCalibrationUniversal : Bool
  blockedClaimsBackpropagateToExperimentalDesign : Bool
  levinMultiscaleOwnerReused : Bool
  deriving Repr, DecidableEq

def canonicalGABANeuroAIContextBoundary : GABANeuroAIContextBoundary := {
  metaNeuroAIKeptDistinctFromIndependentViralityResearch := true
  fmriPredictionDoesNotBecomeMindReading := false
  dyadicSignalsDoNotCollapseObserverPlurality := true
  peripheralToCentralTransportAutomatic := false
  neuralinkWeeklyCalibrationUniversal := false
  blockedClaimsBackpropagateToExperimentalDesign := true
  levinMultiscaleOwnerReused := true
}

end Dashi.Biology.GABANeuroAIContextSnowballExact
