import Dashi.Biology.AutismVaccineClaimPromotionAuditExact

namespace Dashi.Biology.AutismVaccinePersuasionMediaExtensionExact

inductive CommunicationEvidenceKind where
  | randomizedSurveyExperiment
  | replicationStudy
  | systematicReview
  | reviewConsensus
  deriving Repr, DecidableEq

inductive CommunicationOutcome where
  | factualBeliefAccuracy
  | vaccineMisperception
  | vaccinationIntent
  | vaccinationBehaviour
  | sourceTrust
  | salience
  deriving Repr, DecidableEq

inductive CommunicationDirection where
  | improves
  | worsens
  | noDetectableChange
  | mixedOrSubgroupDependent
  deriving Repr, DecidableEq

structure CommunicationEvidenceReceipt where
  sourceKey : String
  evidenceKind : CommunicationEvidenceKind
  targetOutcome : CommunicationOutcome
  direction : CommunicationDirection
  paidReading : String
  scopeBoundary : String
  deriving Repr, DecidableEq

def nyhan2014MMRTrial : CommunicationEvidenceReceipt := {
  sourceKey := "nyhan-reifler-richey-freed-2014-mmr-messaging"
  evidenceKind := .randomizedSurveyExperiment
  targetOutcome := .vaccinationIntent
  direction := .mixedOrSubgroupDependent
  paidReading := "A nationally representative US survey experiment of 1,759 parents tested MMR-promotion messages; interventions did not increase intent overall and some messages produced counterproductive responses on selected outcomes/subgroups."
  scopeBoundary := "Trial-specific message/outcome result; does not establish universal correction backfire or identify belief accuracy with vaccination intent."
}

def laterBackfireReplicationBoundary : CommunicationEvidenceReceipt := {
  sourceKey := "later-correction-backfire-replication-boundary"
  evidenceKind := .replicationStudy
  targetOutcome := .factualBeliefAccuracy
  direction := .improves
  paidReading := "Later correction studies generally find improved belief accuracy and often fail to reproduce a general backfire effect."
  scopeBoundary := "Context-dependent backfire remains possible; neither universal backfire nor universal no-backfire is promoted."
}

def communicationReviewBoundary : CommunicationEvidenceReceipt := {
  sourceKey := "correction-effectiveness-review-boundary"
  evidenceKind := .reviewConsensus
  targetOutcome := .factualBeliefAccuracy
  direction := .improves
  paidReading := "Review-level evidence supports corrections as usually at least somewhat effective for accuracy."
  scopeBoundary := "Accuracy, durability, intent and behaviour remain distinct outcomes."
}

inductive AccurateBeliefAutomaticallyCreatesVaccinationPermission : Prop
inductive TrialCounterproductiveResponseCreatesUniversalBackfirePermission : Prop
inductive MediaExposureAutomaticallyCreatesBeliefPermission : Prop
inductive BeliefAutomaticallyCreatesBehaviourPermission : Prop

theorem accuracyDoesNotDefinitionallyCreateVaccination : AccurateBeliefAutomaticallyCreatesVaccinationPermission → False := by intro h; cases h
theorem trialBackfireDoesNotCreateUniversalBackfire : TrialCounterproductiveResponseCreatesUniversalBackfirePermission → False := by intro h; cases h
theorem mediaExposureDoesNotDefinitionallyCreateBelief : MediaExposureAutomaticallyCreatesBeliefPermission → False := by intro h; cases h
theorem beliefDoesNotDefinitionallyCreateBehaviour : BeliefAutomaticallyCreatesBehaviourPermission → False := by intro h; cases h

inductive PropagationStage where
  | propositionContent
  | sourcePublication
  | mediaAmplification
  | audienceExposure
  | salienceOrAvailability
  | beliefState
  | behaviouralIntent
  | observedBehaviour
  | populationHealthOutcome
  deriving Repr, DecidableEq

structure PropagationEdgeRequirement where
  fromStage : PropagationStage
  toStage : PropagationStage
  edgeReference : String
  automatic : Bool
  deriving Repr, DecidableEq

def publicationToAmplification : PropagationEdgeRequirement := {
  fromStage := .sourcePublication
  toStage := .mediaAmplification
  edgeReference := "Publication alone does not determine media uptake."
  automatic := false
}

def amplificationToExposure : PropagationEdgeRequirement := {
  fromStage := .mediaAmplification
  toStage := .audienceExposure
  edgeReference := "Broadcast volume does not establish individual exposure without reach measurement."
  automatic := false
}

def exposureToBelief : PropagationEdgeRequirement := {
  fromStage := .audienceExposure
  toStage := .beliefState
  edgeReference := "Exposure can affect belief but does not automatically set belief state."
  automatic := false
}

def beliefToIntent : PropagationEdgeRequirement := {
  fromStage := .beliefState
  toStage := .behaviouralIntent
  edgeReference := "Belief accuracy and vaccination intention are empirically distinct endpoints."
  automatic := false
}

def intentToBehaviour : PropagationEdgeRequirement := {
  fromStage := .behaviouralIntent
  toStage := .observedBehaviour
  edgeReference := "Intention does not definitionally equal observed uptake."
  automatic := false
}

def behaviourToPopulationOutcome : PropagationEdgeRequirement := {
  fromStage := .observedBehaviour
  toStage := .populationHealthOutcome
  edgeReference := "Population outcomes require coverage, transmission, susceptibility and epidemiologic context."
  automatic := false
}

structure PersuasionCrossPollination where
  mainAuditReference : String
  cognitiveWarfareReference : String
  traumaMemoryDecisionReference : String
  sourceProvenanceReference : String
  observerReference : String
  reading : String
  deriving Repr, DecidableEq

def canonicalPersuasionCrossPollination : PersuasionCrossPollination := {
  mainAuditReference := "DASHI.Biology.AutismVaccineClaimPromotionAuditExact"
  cognitiveWarfareReference := "existing cognitive-warfare/FIMI propagation and provenance machinery"
  traumaMemoryDecisionReference := "existing trauma-memory-learning-decision machinery"
  sourceProvenanceReference := "DASHI.Core.AttributedSourceCore"
  observerReference := "existing multi-observer / participant-voice machinery"
  reading := "Treat content -> publication -> amplification -> exposure -> belief -> intent -> behaviour -> population outcome as separately payable edges."
}

structure PersuasionMediaBoundary where
  nyhanTrialRepresented : Bool
  universalBackfireLawPaid : Bool
  correctionUsuallyImprovesAccuracyRepresented : Bool
  accuracyCollapsedWithIntent : Bool
  intentCollapsedWithBehaviour : Bool
  mediaNarrativePromotedToCausalLaw : Bool
  propositionTruthSeparatedFromPropagation : Bool
  deriving Repr, DecidableEq

def canonicalPersuasionMediaBoundary : PersuasionMediaBoundary := {
  nyhanTrialRepresented := true
  universalBackfireLawPaid := false
  correctionUsuallyImprovesAccuracyRepresented := true
  accuracyCollapsedWithIntent := false
  intentCollapsedWithBehaviour := false
  mediaNarrativePromotedToCausalLaw := false
  propositionTruthSeparatedFromPropagation := true
}

end Dashi.Biology.AutismVaccinePersuasionMediaExtensionExact
