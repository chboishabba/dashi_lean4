import Dashi.Biology.IBSSystemsIdentificationParetoExact

namespace Dashi.Biology.IBSLatentStateTransitionExact

open Dashi.Biology.IBSSystemsIdentificationParetoExact
open Dashi.Biology.IBSGutBrainImmuneSystemsHyperfabricExact

inductive TemporalEvidenceKind where
  | longitudinalMultiOmics | intensiveEMA | trajectoryClustering | flareTriggeredSampling
  deriving Repr, DecidableEq

inductive TemporalDirectionStatus where
  | contemporaneousAssociation | laggedAssociationObserved | heterogeneousLagDirection | directionUnresolved
  deriving Repr, DecidableEq

structure TemporalStateEvidence where
  sourceReference : String
  kind : TemporalEvidenceKind
  populationReference : String
  samplingReference : String
  observedTemporalSurface : String
  directionStatus : TemporalDirectionStatus
  individualHeterogeneityRetained : Bool
  causalDirectionEstablished : Bool
  attractorValidated : Bool
  hysteresisValidated : Bool
  deriving Repr, DecidableEq

def marsFlareEvidence : TemporalStateEvidence := {
  sourceReference := "Mars et al. 2020 DOI 10.1016/j.cell.2020.08.007"
  kind := .flareTriggeredSampling
  populationReference := "IBS-C / IBS-D longitudinal cohort; subset supplied self-identified flare samples"
  samplingReference := "repeated stool/multi-omics plus symptom severity; flare-triggered extra sampling"
  observedTemporalSurface := "flare samples and individual time courses showed microbial/metabolic changes, with person-specific features"
  directionStatus := .heterogeneousLagDirection
  individualHeterogeneityRetained := true
  causalDirectionEstablished := false
  attractorValidated := false
  hysteresisValidated := false
}

def chanEMAEvidence : TemporalStateEvidence := {
  sourceReference := "Chan et al. 2019 DOI 10.1111/nmo.13514"
  kind := .intensiveEMA
  populationReference := "27 IBS-D and 30 healthy controls"
  samplingReference := "8 smartphone assessments/day for 14 days"
  observedTemporalSurface := "bowel symptoms, stress and affect showed time-dependent relationships; lag direction was cohort/design specific"
  directionStatus := .laggedAssociationObserved
  individualHeterogeneityRetained := true
  causalDirectionEstablished := false
  attractorValidated := false
  hysteresisValidated := false
}

def yunusovaEMAEvidence : TemporalStateEvidence := {
  sourceReference := "Yunusova et al. 2026 DOI 10.1016/j.cgh.2026.05.008"
  kind := .intensiveEMA
  populationReference := "357 adults meeting Rome IV IBS criteria"
  samplingReference := "3 EMA surveys/day for 7 days"
  observedTemporalSurface := "within-person momentary stress and symptoms covaried; fully adjusted prospective lagged effects did not establish a universal direction"
  directionStatus := .directionUnresolved
  individualHeterogeneityRetained := true
  causalDirectionEstablished := false
  attractorValidated := false
  hysteresisValidated := false
}

def chenTrajectoryEvidence : TemporalStateEvidence := {
  sourceReference := "Chen et al. 2026 DOI 10.3389/frmbi.2026.1884540"
  kind := .trajectoryClustering
  populationReference := "62 participants with longitudinal self-management trial data"
  samplingReference := "12-week multidimensional symptom/QOL/psychoneurological trajectories with baseline microbiota features"
  observedTemporalSurface := "trajectory-defined response phenotypes and microbial signatures/predictive features"
  directionStatus := .directionUnresolved
  individualHeterogeneityRetained := true
  causalDirectionEstablished := false
  attractorValidated := false
  hysteresisValidated := false
}

def canonicalTemporalStateEvidenceAtlas : List TemporalStateEvidence :=
  [marsFlareEvidence, chanEMAEvidence, yunusovaEMAEvidence, chenTrajectoryEvidence]

inductive IBSLatentRegimeCandidate where
  | relativelyStableCandidate | flareCandidate | recoveryCandidate | interventionResponseCandidate
  deriving Repr, DecidableEq

inductive TransitionEvidenceGrade where
  | observedTrajectoryDifference | temporallyOrderedAssociation
  | controlledPerturbationTransition | replicatedStateTransition
  deriving Repr, DecidableEq

structure CandidateStateTransition where
  fromCandidate : IBSLatentRegimeCandidate
  toCandidate : IBSLatentRegimeCandidate
  grade : TransitionEvidenceGrade
  measuredAxesReference : String
  timeResolutionReference : String
  perturbationReference : String
  historyReference : String
  empiricalStatusReference : String
  deriving Repr, DecidableEq

def flareTransitionCandidate : CandidateStateTransition := {
  fromCandidate := .relativelyStableCandidate
  toCandidate := .flareCandidate
  grade := .observedTrajectoryDifference
  measuredAxesReference := "symptoms + microbiome/metabolites; Mars 2020 flare subset"
  timeResolutionReference := "study-visit longitudinal sampling plus participant-triggered flare sample"
  perturbationReference := "no randomized perturbation establishes flare entry direction"
  historyReference := "prior state/history retained; flare sample is not treated as memoryless"
  empiricalStatusReference := "candidate transition suggested by temporal observations; no attractor/hysteresis validation"
}

inductive SameSymptomsIdentifySameLatentStatePermission : Prop
inductive LagAssociationIdentifiesCausalDirectionPermission : Prop
inductive TrajectoryClusterIsValidatedAttractorPermission : Prop
inductive FlareRemissionDifferenceProvesHysteresisPermission : Prop

theorem sameSymptomsDoNotIdentifySameLatentState :
    SameSymptomsIdentifySameLatentStatePermission → False := by intro h; cases h

theorem lagAssociationDoesNotIdentifyCausalDirection :
    LagAssociationIdentifiesCausalDirectionPermission → False := by intro h; cases h

theorem trajectoryClusterDoesNotValidateAttractor :
    TrajectoryClusterIsValidatedAttractorPermission → False := by intro h; cases h

theorem flareRemissionDifferenceDoesNotProveHysteresis :
    FlareRemissionDifferenceProvesHysteresisPermission → False := by intro h; cases h

structure IBSTemporalPathBoundary where
  temporalPathOwnerReference : String
  attractorAuthorityOwnerReference : String
  currentSymptomsNeedNotEncodeHistory : Bool
  equalCurrentSymptomsNeedNotImplyEqualNextResponse : Bool
  flareRemissionLabelsAreNotValidatedAttractors : Bool
  hysteresisRequiresPathDependentResponseEvidence : Bool
  lagStructureMayBePersonAndTimescaleSpecific : Bool
  deriving Repr, DecidableEq

def canonicalIBSTemporalPathBoundary : IBSTemporalPathBoundary := {
  temporalPathOwnerReference := "DASHI.Core.TemporalValidityPathDependenceExact"
  attractorAuthorityOwnerReference := "DASHI.Cognition.PNF.AttractorMeasurementValidation"
  currentSymptomsNeedNotEncodeHistory := true
  equalCurrentSymptomsNeedNotImplyEqualNextResponse := true
  flareRemissionLabelsAreNotValidatedAttractors := true
  hysteresisRequiresPathDependentResponseEvidence := true
  lagStructureMayBePersonAndTimescaleSpecific := true
}

inductive TransitionAcquisitionStatus where
  | paidLongitudinalObservation | paidTrajectoryStratification | denseMultifibreNeeded
  | perturbationalTransitionNeeded | hysteresisTestNeeded | replicationNeeded
  deriving Repr, DecidableEq

structure TransitionParetoNode where
  label : String
  status : TransitionAcquisitionStatus
  discoveryRoute : String
  paidReference : String
  missingDiscriminator : String
  nextAcquisition : String
  attributionBoundary : String
  deriving Repr, DecidableEq

def flareDynamicsNode : TransitionParetoNode := {
  label := "within-person flare-entry and recovery dynamics"
  status := .paidLongitudinalObservation
  discoveryRoute := "externalKnowledgeComparison"
  paidReference := "Mars 2020 longitudinal multi-omics + flare-triggered sampling"
  missingDiscriminator := "dense pre-flare/post-flare immune/barrier/autonomic/sensory sampling"
  nextAcquisition := "event-triggered dense sampling plus recovery follow-up"
  attributionBoundary := "observed flare association is not a causal entry law"
}

def stressSymptomLagNode : TransitionParetoNode := {
  label := "stress-symptom lag topology"
  status := .paidLongitudinalObservation
  discoveryRoute := "externalKnowledgeComparison"
  paidReference := "Chan 2019 and Yunusova 2026 EMA provide nonidentical lag results"
  missingDiscriminator := "person- and timescale-specific direction under measured autonomic/context state"
  nextAcquisition := "high-frequency EMA plus autonomic/body-state streams and ethical perturbational context designs"
  attributionBoundary := "heterogeneous lag findings block a universal scalar stress-to-symptom transition"
}

def trajectoryPhenotypeNode : TransitionParetoNode := {
  label := "trajectory-defined response phenotype"
  status := .paidTrajectoryStratification
  discoveryRoute := "externalKnowledgeComparison"
  paidReference := "Chen et al. 2026 longitudinal trajectory clustering with microbial predictors"
  missingDiscriminator := "external replication and intervention-sensitive stability of cluster membership"
  nextAcquisition := "held-out multi-site trajectory reconstruction with common measurement contract"
  attributionBoundary := "cluster label is statistical stratification, not attractor validation"
}

def hysteresisNode : TransitionParetoNode := {
  label := "IBS path-dependence / hysteresis test"
  status := .hysteresisTestNeeded
  discoveryRoute := "experimentalDesign"
  paidReference := "Agda TemporalValidityPathDependenceExact supplies the structural obligation only"
  missingDiscriminator := "equal present measured state after different histories yielding reproducibly different future response, or separated entry/exit thresholds"
  nextAcquisition := "cross-over perturbation with washout/recovery, repeated whole-system panel and explicit history ledger"
  attributionBoundary := "no current cited IBS source is represented as already proving hysteresis"
}

def canonicalIBSTransitionParetoFrontier : List TransitionParetoNode :=
  [flareDynamicsNode, stressSymptomLagNode, trajectoryPhenotypeNode, hysteresisNode]

structure IBSLatentStateTransitionBoundary where
  longitudinalEvidenceRetained : Bool
  individualSpecificTemporalStructureRetained : Bool
  symptomProjectionEqualsHiddenState : Bool
  lagAssociationEqualsCausalDirection : Bool
  trajectoryClusterEqualsAttractor : Bool
  flareRemissionDifferenceEqualsHysteresis : Bool
  historyAndPathMustRemainExplicit : Bool
  attractorLanguageRequiresValidationReceipt : Bool
  deriving Repr, DecidableEq

def canonicalIBSLatentStateTransitionBoundary : IBSLatentStateTransitionBoundary := {
  longitudinalEvidenceRetained := true
  individualSpecificTemporalStructureRetained := true
  symptomProjectionEqualsHiddenState := false
  lagAssociationEqualsCausalDirection := false
  trajectoryClusterEqualsAttractor := false
  flareRemissionDifferenceEqualsHysteresis := false
  historyAndPathMustRemainExplicit := true
  attractorLanguageRequiresValidationReceipt := true
}

end Dashi.Biology.IBSLatentStateTransitionExact
