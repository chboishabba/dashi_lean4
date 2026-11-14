import Dashi.Biology.IBSMechanismProbePerturbationAtlasExact

namespace Dashi.Biology.IBSMechanismProbePerturbationRegression

open Dashi.Biology.IBSMechanismProbePerturbationAtlasExact

theorem probeAtlasRegression :
    canonicalIBSMechanismProbeAtlas = [
      lowFODMAPProbe,
      rifaximinProbe,
      fodmapChallengeProbe,
      bileAcidSequestrationProbe,
      centralInteroceptiveMechanismProbe
    ] := by
  rfl

example : lowFODMAPProbe.uniqueMechanismIdentified = false := by rfl
example : rifaximinProbe.uniqueMechanismIdentified = false := by rfl
example : fodmapChallengeProbe.uniqueMechanismIdentified = false := by rfl
example : bileAcidSequestrationProbe.uniqueMechanismIdentified = false := by rfl
example : centralInteroceptiveMechanismProbe.uniqueMechanismIdentified = false := by rfl

theorem responseNotMechanismIdentityRegression :
    ResponseIdentifiesUniqueMechanismPermission → False :=
  responseDoesNotIdentifyUniqueMechanism

theorem sameSymptomImprovementNotSamePathwayRegression :
    EqualSymptomResponseMeansSamePathwayPermission → False :=
  equalSymptomResponseDoesNotMeanSamePathway

theorem probeFrontierRegression :
    canonicalIBSProbeParetoFrontier = [
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
    ] := by
  rfl

end Dashi.Biology.IBSMechanismProbePerturbationRegression
