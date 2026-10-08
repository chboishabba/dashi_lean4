import Dashi.Biology.QuailEggHistamineGutSnowballExact
import Dashi.Biology.QuailEggHumanOralTransferExact
import Dashi.Biology.QuailEggAllergySafetyBoundaryExact

namespace Dashi.Biology.QuailEggGutTransferRound2Exact

open Dashi.Biology.GABAPhenotypeEvidenceExact

def ovomucoidStability1994Source : AttributedSource :=
  mkDOISource
    "Kyoko Takahashi; Satomi Kitao; Misao Tashiro; Toshio Asao; Masao Kanamori"
    "Inhibitory Specificity against Various Trypsins and Stability of Ovomucoid from Japanese Quail Egg White"
    "Journal of Nutritional Science and Vitaminology 40(6):593-601" "1994"
    "10.3177/jnsv.40.593" "https://doi.org/10.3177/jnsv.40.593"
    "Biochemical stability/trypsin-inhibitory evidence across broad pH, heat and pepsin-digestion conditions; not human intestinal target engagement or IBS efficacy."

def gao2025Source : AttributedSource :=
  mkDOISource
    "Jun Gao; Allen A Lee; Shabnam Abtahi; Jerrold R Turner; Madhusudan Grover; Alexander Schmidt; Thomas M Schmidt; Judy W Nee; Johanna Iturrino; Anthony Lembo; William D Chey; John W Wiley; Prashant Singh"
    "Low Fermentable Oligosaccharides, Disaccharides, Monosaccharides, and Polyols Diet Improves Colonic Barrier Function and Mast Cell Activation in Patients With Diarrhea-Predominant Irritable Bowel Syndrome: A Mechanistic Trial"
    "Gastroenterology 170(1):132-147" "2026"
    "10.1053/j.gastro.2025.07.016" "https://doi.org/10.1053/j.gastro.2025.07.016"
    "Human IBS-D diet-mechanism evidence for barrier/mast-cell changes with linked LPS/TLR4 mouse mechanism; not quail-specific evidence."

structure QuailOvomucoidStabilityReceipt where
  source : AttributedSource
  broadPHStabilityObserved : Bool
  heatStabilityObserved : Bool
  pepsinResistanceObserved : Bool
  trypsinInhibitoryActivityRetained : Bool
  antiMastCellActivityAfterDigestionPaid : Bool
  humanGutTargetEngagementPaid : Bool
  deriving Repr, DecidableEq

def quailOvomucoidStability1994Receipt : QuailOvomucoidStabilityReceipt := {
  source := ovomucoidStability1994Source
  broadPHStabilityObserved := true
  heatStabilityObserved := true
  pepsinResistanceObserved := true
  trypsinInhibitoryActivityRetained := true
  antiMastCellActivityAfterDigestionPaid := false
  humanGutTargetEngagementPaid := false
}

structure IBSDietMastCellMechanismReceipt where
  source : AttributedSource
  humanIBSDPopulation : Bool
  dietIntervention : Bool
  barrierEndpoint : Bool
  mastCellEndpoint : Bool
  histamineMediatorEndpoint : Bool
  mouseTLR4Mechanism : Bool
  quailSpecificEvidence : Bool
  clinicalResponseEqualsPhysiologyChange : Bool
  deriving Repr, DecidableEq

def gao2025IBSDietMastCellReceipt : IBSDietMastCellMechanismReceipt := {
  source := gao2025Source
  humanIBSDPopulation := true
  dietIntervention := true
  barrierEndpoint := true
  mastCellEndpoint := true
  histamineMediatorEndpoint := true
  mouseTLR4Mechanism := true
  quailSpecificEvidence := false
  clinicalResponseEqualsPhysiologyChange := false
}

inductive BiochemicalStabilityPaysTargetEngagementPermission : Prop
inductive OtherDietMechanismPaysQuailEfficacyPermission : Prop

theorem biochemicalStabilityDoesNotPayTargetEngagement : BiochemicalStabilityPaysTargetEngagementPermission → False := by intro h; cases h
theorem otherDietDoesNotPayQuailEfficacy : OtherDietMechanismPaysQuailEfficacyPermission → False := by intro h; cases h

structure SameObjectQuailGutExperiment where
  agdaExperimentalDesignOwner : String
  treatmentIdentityReference : String
  digestionExposureReference : String
  histamineMastCellReference : String
  barrierReference : String
  microbiomeReference : String
  clinicalEndpointReference : String
  safetyReference : String
  deriving Repr, DecidableEq

def canonicalSameObjectQuailGutExperiment : SameObjectQuailGutExperiment := {
  agdaExperimentalDesignOwner := "DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact"
  treatmentIdentityReference := "quantified quail product with ovomucoid/albumen composition and preparation retained"
  digestionExposureReference := "measure/validate digestion survival and intestinal exposure"
  histamineMastCellReference := "mucosal or validated proxy histamine/tryptase/mast-cell activation endpoints"
  barrierReference := "barrier/permeability endpoint where justified"
  microbiomeReference := "strain-/function-resolved histamine-producing microbiome plus substrate/pH context"
  clinicalEndpointReference := "predeclared IBS symptom/pain/visceral-sensitivity outcome"
  safetyReference := "quail-specific allergy assessment and adverse-event monitoring"
}

structure QuailEggGutTransferRound2Boundary where
  preclinicalMastCellLinkPaid : Bool
  humanOralExposureLinkPaid : Bool
  ovomucoidSurvivalPlausibilityPaid : Bool
  humanIBSDietMastCellPlasticityPaid : Bool
  quailSpecificHumanGutTargetEngagementPaid : Bool
  quailSpecificIBSEfficacyPaid : Bool
  safetyGateRetained : Bool
  sameObjectExperimentSpecified : Bool
  deriving Repr, DecidableEq

def canonicalQuailEggGutTransferRound2Boundary : QuailEggGutTransferRound2Boundary := {
  preclinicalMastCellLinkPaid := true
  humanOralExposureLinkPaid := true
  ovomucoidSurvivalPlausibilityPaid := true
  humanIBSDietMastCellPlasticityPaid := true
  quailSpecificHumanGutTargetEngagementPaid := false
  quailSpecificIBSEfficacyPaid := false
  safetyGateRetained := true
  sameObjectExperimentSpecified := true
}

end Dashi.Biology.QuailEggGutTransferRound2Exact
