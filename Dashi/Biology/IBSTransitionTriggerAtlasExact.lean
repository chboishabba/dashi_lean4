import Dashi.Biology.IBSLatentStateTransitionExact

namespace Dashi.Biology.IBSTransitionTriggerAtlasExact

inductive TriggerKind where
  | acuteEntericInfection | dietChallenge | microbiomeDirectedIntervention | bileAcidPerturbation
  | psychosocialContextPerturbation | sleepCircadianPerturbation | candidateLocalImmunePerturbation
  deriving Repr, DecidableEq

inductive TriggerEvidenceClass where
  | naturalExperiment | randomizedProbe | intensiveObservational | reviewBoundedCandidate | proposedExperiment
  deriving Repr, DecidableEq

structure TransitionTrigger where
  kind : TriggerKind
  evidenceClass : TriggerEvidenceClass
  sourceReference : String
  proximalFibres : String
  downstreamFibres : String
  persistenceReference : String
  uniqueMechanismIdentified : Bool
  latentStateTransitionProved : Bool
  deriving Repr, DecidableEq

def postInfectiousTrigger : TransitionTrigger := {
  kind := .acuteEntericInfection
  evidenceClass := .naturalExperiment
  sourceReference := "Lupu et al. 2023 DOI 10.3748/wjg.v29.i21.3241"
  proximalFibres := "microbiome, epithelial barrier, mucosal immune and neuromuscular perturbation"
  downstreamFibres := "visceral sensitivity, motility/secretion and gut-brain symptom state"
  persistenceReference := "persistent post-infectious symptoms after acute infection are documented; persistence does not identify one maintaining mechanism"
  uniqueMechanismIdentified := false
  latentStateTransitionProved := false
}

def sleepCircadianTrigger : TransitionTrigger := {
  kind := .sleepCircadianPerturbation
  evidenceClass := .reviewBoundedCandidate
  sourceReference := "Fowler et al. 2025 DOI 10.1111/nmo.70133"
  proximalFibres := "sleep/circadian context with autonomic, endocrine and immune coupling"
  downstreamFibres := "GI symptoms, fatigue, quality of life and potentially visceral-sensitivity state"
  persistenceReference := "association/bidirectionality are discussed; transition thresholds are not paid"
  uniqueMechanismIdentified := false
  latentStateTransitionProved := false
}

def wearableObservationTrigger : TransitionTrigger := {
  kind := .psychosocialContextPerturbation
  evidenceClass := .intensiveObservational
  sourceReference := "Veldman et al. 2026 DOI 10.1111/nmo.70232"
  proximalFibres := "wearable HRV/sleep/GI myoelectric proxies"
  downstreamFibres := "candidate synchronized autonomic/GI trajectories"
  persistenceReference := "measurement feasibility/heterogeneity evidence only; wearable readout is not a perturbation or latent-state identifier"
  uniqueMechanismIdentified := false
  latentStateTransitionProved := false
}

def canonicalIBSTransitionTriggerAtlas : List TransitionTrigger :=
  [postInfectiousTrigger, sleepCircadianTrigger, wearableObservationTrigger]

inductive NaturalTriggerIdentifiesUniqueMechanismPermission : Prop
inductive WearableProxyIdentifiesLatentStatePermission : Prop
inductive PostInfectiousPersistenceValidatesAttractorPermission : Prop

theorem naturalTriggerDoesNotIdentifyUniqueMechanism :
    NaturalTriggerIdentifiesUniqueMechanismPermission → False := by intro h; cases h

theorem wearableProxyDoesNotIdentifyLatentState :
    WearableProxyIdentifiesLatentStatePermission → False := by intro h; cases h

theorem postInfectiousPersistenceDoesNotValidateAttractor :
    PostInfectiousPersistenceValidatesAttractorPermission → False := by intro h; cases h

structure TransitionTriggerParetoNode where
  label : String
  discoveryRoute : String
  paidReference : String
  systemValue : String
  nextAcquisition : String
  attributionBoundary : String
  deriving Repr, DecidableEq

def postInfectiousNaturalProbeNode : TransitionTriggerParetoNode := {
  label := "post-infectious onset as natural whole-system perturbation"
  discoveryRoute := "externalKnowledgeComparison"
  paidReference := "PI-IBS literature: acute infection can precede persistent IBS phenotype in a subset"
  systemValue := "trigger time is comparatively localized and several fibres are plausibly perturbed together"
  nextAcquisition := "prospective pre/post infection or outbreak cohorts with repeated barrier, immune, microbial-function, autonomic, visceral-sensitivity and symptom measurements"
  attributionBoundary := "natural perturbation does not isolate which fibre is necessary or sufficient"
}

def wearableDenseSamplingNode : TransitionTriggerParetoNode := {
  label := "wearable-assisted dense temporal sampling"
  discoveryRoute := "experimentalDesign"
  paidReference := "Veldman 2026 review/meta-analysis supports candidate HRV/sleep/GI wearable surfaces with substantial heterogeneity"
  systemValue := "raises temporal resolution between sparse lab visits and EMA"
  nextAcquisition := "prospective standardized wearable+EMA+stool/event-triggered protocol with device calibration and missingness ledger"
  attributionBoundary := "wearable signals are proxies; validation and synchronization errors remain explicit"
}

def sleepCircadianNode : TransitionTriggerParetoNode := {
  label := "sleep/circadian modulation of IBS state"
  discoveryRoute := "externalKnowledgeComparison"
  paidReference := "Fowler 2025 review supports sleep/fatigue/GI severity association with immune/circadian context"
  systemValue := "adds time-of-day/recovery coordinates potentially conditioning autonomic, immune and sensory gain"
  nextAcquisition := "intervention or natural schedule-shift studies with objective sleep/circadian measurement and next-day multi-fibre outcomes"
  attributionBoundary := "association is not a causal sleep-to-IBS transition law"
}

def historyAwareProbeNode : TransitionTriggerParetoNode := {
  label := "history-aware repeated perturbation"
  discoveryRoute := "experimentalDesign"
  paidReference := "Agda TemporalValidityPathDependenceExact supplies the structural obligation"
  systemValue := "tests whether response depends on how the same apparent present state was reached"
  nextAcquisition := "counterbalanced repeated challenge with entry/recovery/washout periods and matched present-state measurements"
  attributionBoundary := "only reproducible path-dependent response would support hysteresis; design alone does not"
}

def canonicalTransitionTriggerParetoFrontier : List TransitionTriggerParetoNode :=
  [postInfectiousNaturalProbeNode, wearableDenseSamplingNode, sleepCircadianNode, historyAwareProbeNode]

structure IBSTransitionTriggerBoundary where
  naturalPerturbationsRetained : Bool
  sleepCircadianContextRetained : Bool
  wearablesMayIncreaseTemporalResolution : Bool
  naturalTriggerEqualsUniqueMechanism : Bool
  wearableProxyEqualsLatentState : Bool
  persistentPostInfectiousPhenotypeEqualsAttractorProof : Bool
  historyAwarePerturbationPreferredForHysteresisTest : Bool
  deriving Repr, DecidableEq

def canonicalIBSTransitionTriggerBoundary : IBSTransitionTriggerBoundary := {
  naturalPerturbationsRetained := true
  sleepCircadianContextRetained := true
  wearablesMayIncreaseTemporalResolution := true
  naturalTriggerEqualsUniqueMechanism := false
  wearableProxyEqualsLatentState := false
  persistentPostInfectiousPhenotypeEqualsAttractorProof := false
  historyAwarePerturbationPreferredForHysteresisTest := true
}

end Dashi.Biology.IBSTransitionTriggerAtlasExact
