import Dashi.Biology.IBSSystemsIdentificationParetoExact

namespace Dashi.Biology.IBSMechanismProbePerturbationAtlasExact

open Dashi.Biology.IBSSystemsIdentificationParetoExact
open Dashi.Biology.IBSGutBrainImmuneSystemsHyperfabricExact

inductive ProbeFibre where
  | dietaryFermentationProbe | microbiomeAntibioticProbe | bileAcidProbe
  | centralInteroceptiveProbe | histamineH1Probe | quailMastCellCandidateProbe
  deriving Repr, DecidableEq

inductive ProbeEvidenceClass where
  | randomizedComparative | randomizedBlindedChallenge | randomizedMechanistic
  | interventionWithImaging | adjacentBoundedEvidence
  deriving Repr, DecidableEq

structure MechanismProbe where
  fibre : ProbeFibre
  evidenceClass : ProbeEvidenceClass
  sourceReference : String
  perturbation : String
  proximalReadout : String
  distalReadout : String
  interpretation : String
  uniqueMechanismIdentified : Bool
  deriving Repr, DecidableEq

def lowFODMAPProbe : MechanismProbe := {
  fibre := .dietaryFermentationProbe
  evidenceClass := .randomizedComparative
  sourceReference := "Lee et al. 2026 DOI 10.1016/j.cgh.2026.04.014"
  perturbation := "low-FODMAP dietary substrate restriction"
  proximalReadout := "microbiome composition / fermentation-linked ecological response"
  distalReadout := "pain, bloating and IBS severity trajectory"
  interpretation := "diet/substrate-microbiome probe whose effects can propagate through several fibres"
  uniqueMechanismIdentified := false
}

def rifaximinProbe : MechanismProbe := {
  fibre := .microbiomeAntibioticProbe
  evidenceClass := .randomizedComparative
  sourceReference := "Lee et al. 2026 DOI 10.1016/j.cgh.2026.04.014"
  perturbation := "rifaximin"
  proximalReadout := "microbial ecological response"
  distalReadout := "pain, bloating and IBS severity trajectory"
  interpretation := "mechanistically distinct from dietary substrate restriction despite overlapping endpoints"
  uniqueMechanismIdentified := false
}

def fodmapChallengeProbe : MechanismProbe := {
  fibre := .dietaryFermentationProbe
  evidenceClass := .randomizedBlindedChallenge
  sourceReference := "Gastroenterology 2024 DOI 10.1053/j.gastro.2024.02.008"
  perturbation := "blinded individual FODMAP-class reintroduction"
  proximalReadout := "within-person trigger response"
  distalReadout := "IBS-SSS and symptom trajectory"
  interpretation := "high information value for individual exposure sensitivity but downstream mechanism remains ambiguous"
  uniqueMechanismIdentified := false
}

def bileAcidSequestrationProbe : MechanismProbe := {
  fibre := .bileAcidProbe
  evidenceClass := .randomizedMechanistic
  sourceReference := "Camilleri et al. 2020 randomized colesevelam study"
  perturbation := "colesevelam bile-acid sequestration"
  proximalReadout := "fecal bile acids, C4/FGF19 and mucosal bile-acid receptor gene expression"
  distalReadout := "stool, transit and permeability endpoints"
  interpretation := "target-engagement probe for a selected bile-acid fibre; target engagement is not whole-system closure"
  uniqueMechanismIdentified := false
}

def centralInteroceptiveMechanismProbe : MechanismProbe := {
  fibre := .centralInteroceptiveProbe
  evidenceClass := .interventionWithImaging
  sourceReference := "Lowen et al. 2013 DOI 10.1111/apt.12319"
  perturbation := "gut-directed hypnotherapy / educational intervention"
  proximalReadout := "fMRI response during expected and delivered rectal distension"
  distalReadout := "symptom response"
  interpretation := "central pain/interoception change can accompany response without unique upstream-cause identification"
  uniqueMechanismIdentified := false
}

def canonicalIBSMechanismProbeAtlas : List MechanismProbe := [
  lowFODMAPProbe, rifaximinProbe, fodmapChallengeProbe,
  bileAcidSequestrationProbe, centralInteroceptiveMechanismProbe
]

inductive ResponseIdentifiesUniqueMechanismPermission : Prop
inductive EqualSymptomResponseMeansSamePathwayPermission : Prop
inductive TargetEngagementMeansWholeSystemClosurePermission : Prop

theorem responseDoesNotIdentifyUniqueMechanism :
    ResponseIdentifiesUniqueMechanismPermission → False := by intro h; cases h

theorem equalSymptomResponseDoesNotMeanSamePathway :
    EqualSymptomResponseMeansSamePathwayPermission → False := by intro h; cases h

theorem targetEngagementDoesNotMeanWholeSystemClosure :
    TargetEngagementMeansWholeSystemClosurePermission → False := by intro h; cases h

structure ProbeParetoNode where
  label : String
  discoveryRoute : String
  separatesFibre : IBSSystemFibre
  proximalMeasurement : MeasurementAxis
  distalMeasurement : MeasurementAxis
  currentValue : String
  nextAcquisition : String
  deriving Repr, DecidableEq

def canonicalIBSProbeParetoFrontier : List ProbeParetoNode := [
  { label := "diet-vs-rifaximin differential response", discoveryRoute := "externalKnowledgeComparison",
    separatesFibre := .microbiomeMetaboliteFibre, proximalMeasurement := .microbiomeFunctionAxis,
    distalMeasurement := .symptomTrajectoryAxis,
    currentValue := "randomized comparative perturbation with distinct baseline microbial response associations",
    nextAcquisition := "replicate with metatranscriptome/metabolome, barrier/immune and autonomic readouts" },
  { label := "within-person blinded dietary challenge", discoveryRoute := "externalKnowledgeComparison",
    separatesFibre := .dietExposureFibre, proximalMeasurement := .dietExposureAxis,
    distalMeasurement := .symptomTrajectoryAxis,
    currentValue := "randomized challenge identifies person-specific trigger classes",
    nextAcquisition := "add fermentation/metabolite, mast-cell/barrier and autonomic measurements" },
  { label := "bile-acid target-engagement probe", discoveryRoute := "externalKnowledgeComparison",
    separatesFibre := .neurochemicalMetabolicFibre, proximalMeasurement := .bileAcidAxis,
    distalMeasurement := .bowelHabitTransitAxis,
    currentValue := "direct biochemical target engagement with physiological readouts",
    nextAcquisition := "larger target-positive cohorts with symptom response and competing-fibre panel" },
  { label := "central/interoceptive perturbation probe", discoveryRoute := "externalKnowledgeComparison",
    separatesFibre := .centralPainInteroceptiveFibre, proximalMeasurement := .centralInteroceptivePainAxis,
    distalMeasurement := .symptomTrajectoryAxis,
    currentValue := "treatment-associated brain-response change under controlled visceral stimulation",
    nextAcquisition := "modern preregistered replication with autonomic, peripheral and symptom trajectories" },
  { label := "quail local mast-cell candidate as whole-system probe", discoveryRoute := "experimentalDesign",
    separatesFibre := .mucosalImmuneMastCellFibre, proximalMeasurement := .histamineMastCellAxis,
    distalMeasurement := .symptomTrajectoryAxis,
    currentValue := "preclinical/local quail evidence exists; human IBS same-object perturbation remains open",
    nextAcquisition := "pair quail exposure with mast-cell/histamine, barrier, metabolome/microbiome, autonomic, visceral-sensitivity and symptom trajectories" }
]

structure IBSMechanismProbeBoundary where
  orthogonalPerturbationsRetained : Bool
  commonClinicalEndpointsAllowComparison : Bool
  equalClinicalResponseImpliesSameMechanism : Bool
  proximalTargetEngagementImpliesWholeSystemClosure : Bool
  quailCanBeDesignedAsLocalProbeWithWholeSystemReadout : Bool
  deriving Repr, DecidableEq

def canonicalIBSMechanismProbeBoundary : IBSMechanismProbeBoundary := {
  orthogonalPerturbationsRetained := true
  commonClinicalEndpointsAllowComparison := true
  equalClinicalResponseImpliesSameMechanism := false
  proximalTargetEngagementImpliesWholeSystemClosure := false
  quailCanBeDesignedAsLocalProbeWithWholeSystemReadout := true
}

end Dashi.Biology.IBSMechanismProbePerturbationAtlasExact
