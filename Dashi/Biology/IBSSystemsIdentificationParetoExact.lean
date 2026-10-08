import Dashi.Biology.IBSGutBrainImmuneSystemsHyperfabricExact

namespace Dashi.Biology.IBSSystemsIdentificationParetoExact

open Dashi.Biology.IBSGutBrainImmuneSystemsHyperfabricExact

inductive MeasurementAxis where
  | symptomTrajectoryAxis | bowelHabitTransitAxis | microbiomeCompositionAxis
  | microbiomeFunctionAxis | metabolomeAxis | histamineMastCellAxis
  | immuneInflammatoryAxis | epithelialBarrierAxis | bileAcidAxis | autonomicAxis
  | endocrineHPAaxis | visceralSensitivityAxis | centralInteroceptivePainAxis
  | dietExposureAxis
  deriving Repr, DecidableEq

inductive MeasurementRole where
  | diagnosticExclusionRole | mechanismStratificationRole | longitudinalStateRole
  | perturbationResponseRole | nuisanceControlRole
  deriving Repr, DecidableEq

structure MeasurementCoordinate where
  axis : MeasurementAxis
  role : MeasurementRole
  sourceReference : String
  measuredSurface : String
  doesNotIdentify : String
  deriving Repr, DecidableEq

def canonicalIBSMeasurementAtlas : List MeasurementCoordinate := [
  { axis := .microbiomeFunctionAxis, role := .mechanismStratificationRole,
    sourceReference := "Jacobs 2023 DOI 10.1186/s40168-022-01450-5",
    measuredSurface := "metatranscriptomic microbial function",
    doesNotIdentify := "microbial function does not identify whole-system causal state" },
  { axis := .metabolomeAxis, role := .mechanismStratificationRole,
    sourceReference := "Jacobs 2023 DOI 10.1186/s40168-022-01450-5",
    measuredSurface := "untargeted fecal metabolome",
    doesNotIdentify := "metabolite profile does not identify source or causal direction" },
  { axis := .immuneInflammatoryAxis, role := .mechanismStratificationRole,
    sourceReference := "Goyal 2026 DOI 10.1007/s11894-026-01053-2 plus existing histamine/mast-cell lane",
    measuredSurface := "immune and mast-cell-related measurements",
    doesNotIdentify := "immune activation is not the complete IBS mechanism" },
  { axis := .epithelialBarrierAxis, role := .longitudinalStateRole,
    sourceReference := "Goyal 2026 plus acquired Gao IBS-D mechanism trial",
    measuredSurface := "barrier/permeability-related measures",
    doesNotIdentify := "barrier change does not identify upstream route" },
  { axis := .bileAcidAxis, role := .mechanismStratificationRole,
    sourceReference := "Di Ciaula 2024 DOI 10.1016/j.ejim.2024.07.008",
    measuredSurface := "bile-acid synthesis/transport/metabolism phenotype",
    doesNotIdentify := "bile-acid diarrhoea does not equal all IBS-D" },
  { axis := .autonomicAxis, role := .longitudinalStateRole,
    sourceReference := "Bai 2026 DOI 10.3389/fnins.2026.1832540",
    measuredSurface := "autonomic/vagal-sympathetic dynamics",
    doesNotIdentify := "autonomic proxy is not full allostatic or IBS state" },
  { axis := .visceralSensitivityAxis, role := .perturbationResponseRole,
    sourceReference := "whole-system and H1/TRPV1 lanes",
    measuredSurface := "visceral sensory gain / pain response",
    doesNotIdentify := "sensitivity does not identify upstream mediator" },
  { axis := .symptomTrajectoryAxis, role := .longitudinalStateRole,
    sourceReference := "positive symptom diagnosis plus repeated trajectory",
    measuredSurface := "pain, urgency, stool form and quality-of-life trajectory",
    doesNotIdentify := "symptom output is not a mechanism label" }
]

inductive SingleMarkerIdentifiesWholeSystemStatePermission : Prop
inductive BowelHabitSubtypeIdentifiesMechanismPermission : Prop
inductive CrossSectionIdentifiesFeedbackDirectionPermission : Prop
inductive CorrelatedOmicsIdentifiesCausalLoopPermission : Prop

theorem singleMarkerDoesNotIdentifyWholeSystemState :
    SingleMarkerIdentifiesWholeSystemStatePermission → False := by intro h; cases h

theorem bowelHabitSubtypeDoesNotIdentifyMechanism :
    BowelHabitSubtypeIdentifiesMechanismPermission → False := by intro h; cases h

theorem crossSectionDoesNotIdentifyFeedbackDirection :
    CrossSectionIdentifiesFeedbackDirectionPermission → False := by intro h; cases h

theorem correlatedOmicsDoesNotIdentifyCausalLoop :
    CorrelatedOmicsIdentifiesCausalLoopPermission → False := by intro h; cases h

structure DiscriminatingPanel where
  repeatedSymptoms : MeasurementAxis
  stoolOrTransit : MeasurementAxis
  microbialFunction : MeasurementAxis
  metabolome : MeasurementAxis
  immuneMastCell : MeasurementAxis
  barrier : MeasurementAxis
  bileAcid : MeasurementAxis
  autonomic : MeasurementAxis
  visceralSensitivity : MeasurementAxis
  exposureLedger : MeasurementAxis
  longitudinalRepeatedMeasuresRequired : Bool
  controlledPerturbationPreferredForDirection : Bool
  panelIsValidatedClinicalDiagnostic : Bool
  deriving Repr, DecidableEq

def canonicalMinimumDiscriminatingPanel : DiscriminatingPanel := {
  repeatedSymptoms := .symptomTrajectoryAxis
  stoolOrTransit := .bowelHabitTransitAxis
  microbialFunction := .microbiomeFunctionAxis
  metabolome := .metabolomeAxis
  immuneMastCell := .histamineMastCellAxis
  barrier := .epithelialBarrierAxis
  bileAcid := .bileAcidAxis
  autonomic := .autonomicAxis
  visceralSensitivity := .visceralSensitivityAxis
  exposureLedger := .dietExposureAxis
  longitudinalRepeatedMeasuresRequired := true
  controlledPerturbationPreferredForDirection := true
  panelIsValidatedClinicalDiagnostic := false
}

inductive AcquisitionStatus where
  | acquiredStructuralEvidence | acquiredCohortEvidence | longitudinalAcquisitionNeeded
  | perturbationAcquisitionNeeded | replicationAcquisitionNeeded
  deriving Repr, DecidableEq

inductive InformationValue where
  | separatesOneFibre | separatesSeveralFibres | directionSensitive | transportSensitive | stateTransitionSensitive
  deriving Repr, DecidableEq

structure SystemsAcquisitionNode where
  label : String
  status : AcquisitionStatus
  discoveryRoute : String
  value : InformationValue
  paidReference : String
  residual : String
  authorityBoundary : String
  deriving Repr, DecidableEq

def canonicalIBSSystemsParetoFrontier : List SystemsAcquisitionNode := [
  { label := "microbiome function + metabolome", status := .acquiredCohortEvidence,
    discoveryRoute := "externalKnowledgeComparison", value := .separatesSeveralFibres,
    paidReference := "Jacobs 2023 multi-omics cohort",
    residual := "repeated within-person sampling and perturbation needed for state transition/direction",
    authorityBoundary := "cohort association is not causal-loop identification" },
  { label := "composite mechanism-based biomarker panel", status := .acquiredStructuralEvidence,
    discoveryRoute := "externalKnowledgeComparison", value := .separatesSeveralFibres,
    paidReference := "Goyal 2026 review synthesis",
    residual := "prospective validation, calibration and treatment-response usefulness",
    authorityBoundary := "review synthesis is not a validated clinical classifier" },
  { label := "autonomic dynamics", status := .acquiredStructuralEvidence,
    discoveryRoute := "externalKnowledgeComparison", value := .stateTransitionSensitive,
    paidReference := "Bai 2026 ANS review plus Agda allostatic/interoception owners",
    residual := "synchronized repeated autonomic, gut and symptom measurements",
    authorityBoundary := "HRV/vagal proxies are not complete autonomic state" },
  { label := "bile-acid physiology", status := .acquiredStructuralEvidence,
    discoveryRoute := "externalKnowledgeComparison", value := .separatesOneFibre,
    paidReference := "Di Ciaula 2024 systematic review",
    residual := "explicit overlap handling against IBS-D, transit, microbiome and diet",
    authorityBoundary := "bile-acid diarrhoea is not synonymous with IBS-D" },
  { label := "within-person multi-fibre state transition", status := .longitudinalAcquisitionNeeded,
    discoveryRoute := "experimentalDesign", value := .stateTransitionSensitive,
    paidReference := "whole-system hyperfabric exposes recurrent-state ambiguity",
    residual := "dense repeated symptoms + diet + stool/metabolome + immune/barrier + autonomic measures around flares/remissions",
    authorityBoundary := "longitudinal association alone does not identify feedback direction" },
  { label := "mechanism-selective perturbation with multi-fibre readout", status := .perturbationAcquisitionNeeded,
    discoveryRoute := "experimentalDesign", value := .directionSensitive,
    paidReference := "backprop from competing feedback loops",
    residual := "randomized/crossover perturbations targeting distinct fibres with matched panel",
    authorityBoundary := "response does not prove uniqueness of mechanism" },
  { label := "external replication of system-state signatures", status := .replicationAcquisitionNeeded,
    discoveryRoute := "externalKnowledgeComparison", value := .transportSensitive,
    paidReference := "omics/biomarker signatures remain cohort and pipeline sensitive",
    residual := "held-out multi-site validation across geography, diet, sex, subtype and assay pipeline",
    authorityBoundary := "transport limited to demonstrated populations and pipelines" }
]

structure IBSSystemsIdentificationBoundary where
  wholeSystemOwner : IBSWholeSystemBoundary
  singleMarkerSufficient : Bool
  bowelHabitSubtypeSufficientMechanismLabel : Bool
  crossSectionSufficientForFeedbackDirection : Bool
  repeatedMultifibreMeasurementPreferred : Bool
  perturbationNeededForDirectionWithoutStrongIdentificationAssumptions : Bool
  clinicalPanelValidationClaimed : Bool
  numericalInformationGainInvented : Bool
  deriving Repr, DecidableEq

def canonicalIBSSystemsIdentificationBoundary : IBSSystemsIdentificationBoundary := {
  wholeSystemOwner := canonicalIBSWholeSystemBoundary
  singleMarkerSufficient := false
  bowelHabitSubtypeSufficientMechanismLabel := false
  crossSectionSufficientForFeedbackDirection := false
  repeatedMultifibreMeasurementPreferred := true
  perturbationNeededForDirectionWithoutStrongIdentificationAssumptions := true
  clinicalPanelValidationClaimed := false
  numericalInformationGainInvented := false
}

end Dashi.Biology.IBSSystemsIdentificationParetoExact
