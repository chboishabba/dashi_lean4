import Dashi.Biology.GABAPhenotypeEvidenceExact

namespace Dashi.Biology.QuailEggHistamineGutSnowballExact

open Dashi.Biology.GABAPhenotypeEvidenceExact

def lianto2018Source : AttributedSource :=
  mkDOISource
    "Priscilia Lianto; Fredrick O Ogutu; Yani Zhang; Feng He; Huilian Che"
    "Inhibitory effects of quail egg on mast cells degranulation by suppressing PAR2-mediated MAPK and NF-kB activation"
    "Food & Nutrition Research 62:1084" "2018"
    "10.29219/fnr.v62.1084" "https://doi.org/10.29219/fnr.v62.1084"
    "Mouse PCA and HMC-1 cell evidence for quail-egg anti-degranulation activity; not human IBS efficacy or oral bioavailability."

def ovomucoid2023Source : AttributedSource :=
  mkDOISource
    "Mengzhen Hao; Shuai Yang; Shiwen Han; Huilian Che"
    "The amino acids differences in epitopes may promote the different allergenicity of ovomucoid derived from hen eggs and quail eggs"
    "Food Science and Human Wellness 12(3):861-870" "2023"
    "10.1016/j.fshw.2022.09.028" "https://doi.org/10.1016/j.fshw.2022.09.028"
    "Recombinant quail-egg ovomucoid trypsin-inhibition and RBL-2H3 degranulation evidence; not whole-food or clinical efficacy evidence."

def dePalma2022Source : AttributedSource :=
  mkDOISource
    "Giada De Palma et al."
    "Histamine production by the gut microbiota induces visceral hyperalgesia through histamine 4 receptor signaling in mice"
    "Science Translational Medicine 14(655):eabj1895" "2022"
    "10.1126/scitranslmed.abj1895" "https://doi.org/10.1126/scitranslmed.abj1895"
    "Bounded microbiome-histamine IBS mechanism including high-histamine microbiota, Klebsiella aerogenes, H4 signaling, visceral hypersensitivity and mast-cell accumulation."

def schnedl2021Source : AttributedSource :=
  mkDOISource
    "Wolfgang J Schnedl; Dietmar Enko"
    "Histamine Intolerance Originates in the Gut"
    "Nutrients 13(4):1262" "2021"
    "10.3390/nu13041262" "https://doi.org/10.3390/nu13041262"
    "Review-level gut DAO / histamine-intolerance framing; serum DAO is not established as equivalent to gut DAO activity."

def wouters2016Source : AttributedSource :=
  mkDOISource
    "Mira M Wouters et al."
    "Histamine Receptor H1-Mediated Sensitization of TRPV1 Mediates Visceral Hypersensitivity and Symptoms in Patients With Irritable Bowel Syndrome"
    "Gastroenterology 150(4):875-887.e9" "2016"
    "10.1053/j.gastro.2015.12.034" "https://doi.org/10.1053/j.gastro.2015.12.034"
    "Human biopsy plus randomized placebo-controlled ebastine evidence for an H1/TRPV1 pathway in the studied IBS cohort; not a universal IBS mechanism."

inductive EvidenceSurface where
  | inVitroMastCell | mouseAllergyModel | recombinantProteinCellModel
  | humanIBSBiopsyAndTrial | microbiomeHumanCohortPlusMouseTransfer | reviewLevelGutDAO
  deriving Repr, DecidableEq

structure QuailEggMastCellEvidenceReceipt where
  source : AttributedSource
  surfaces : List EvidenceSurface
  albumenHistamineReleaseSuppressed : Bool
  oralHumanIBSEfficacyPaid : Bool
  boundary : String
  deriving Repr, DecidableEq

def lianto2018QuailEggReceipt : QuailEggMastCellEvidenceReceipt := {
  source := lianto2018Source
  surfaces := [.mouseAllergyModel, .inVitroMastCell]
  albumenHistamineReleaseSuppressed := true
  oralHumanIBSEfficacyPaid := false
  boundary := "Mouse/cell anti-degranulation does not discharge digestion, exposure, tolerability, allergy or human IBS endpoints."
}

structure QuailOvomucoidEvidenceReceipt where
  source : AttributedSource
  recombinantProteinEvidence : Bool
  trypsinInhibitionObserved : Bool
  cellDegranulationInhibitionObserved : Bool
  wholeFoodEquivalencePaid : Bool
  humanIBSEfficacyPaid : Bool
  deriving Repr, DecidableEq

def quailOvomucoid2023Receipt : QuailOvomucoidEvidenceReceipt := {
  source := ovomucoid2023Source
  recombinantProteinEvidence := true
  trypsinInhibitionObserved := true
  cellDegranulationInhibitionObserved := true
  wholeFoodEquivalencePaid := false
  humanIBSEfficacyPaid := false
}

structure IBSMicrobialHistamineReceipt where
  source : AttributedSource
  microbialHDCSourceRetained : Bool
  humanCohortAssociationRetained : Bool
  mouseTransferMechanismRetained : Bool
  universalIBSCauseClaimed : Bool
  deriving Repr, DecidableEq

def dePalma2022IBSHistamineReceipt : IBSMicrobialHistamineReceipt := {
  source := dePalma2022Source
  microbialHDCSourceRetained := true
  humanCohortAssociationRetained := true
  mouseTransferMechanismRetained := true
  universalIBSCauseClaimed := false
}

inductive SerumDAOEqualsGutDAOPermission : Prop
inductive QuailEggTreatsIBSPermission : Prop
inductive RecombinantOvomucoidEqualsWholeFoodPermission : Prop

theorem serumDAODoesNotEqualGutDAO : SerumDAOEqualsGutDAOPermission → False := by intro h; cases h
theorem quailEggEvidenceDoesNotPayIBSTreatment : QuailEggTreatsIBSPermission → False := by intro h; cases h
theorem recombinantOvomucoidDoesNotEqualWholeFood : RecombinantOvomucoidEqualsWholeFoodPermission → False := by intro h; cases h

structure HistamineSourceSeparation where
  dietaryHistamine : String
  microbialHistamine : String
  mastCellHistamine : String
  clearanceDAO : String
  clearanceHNMT : String
  receptorSensitivity : String
  sourcesCollapsed : Bool
  deriving Repr, DecidableEq

def canonicalHistamineSourceSeparation : HistamineSourceSeparation := {
  dietaryHistamine := "food/luminal histamine input"
  microbialHistamine := "microbial HDC-dependent histamine production"
  mastCellHistamine := "host mast-cell/basophil release"
  clearanceDAO := "intestinal/extracellular DAO route"
  clearanceHNMT := "intracellular/CNS HNMT route"
  receptorSensitivity := "H1/H4 and downstream sensory signaling such as TRPV1 where supported"
  sourcesCollapsed := false
}

structure QuailEggIBSExperimentRequirement where
  agdaExperimentalDesignOwner : String
  populationRequired : Bool
  controlledExposureComparatorRequired : Bool
  symptomOrVisceralEndpointRequired : Bool
  histamineMastCellDAOAssayRequired : Bool
  allergyTolerabilitySurveillanceRequired : Bool
  practicalEffectRequired : Bool
  deriving Repr, DecidableEq

def canonicalQuailEggIBSExperimentRequirement : QuailEggIBSExperimentRequirement := {
  agdaExperimentalDesignOwner := "DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact"
  populationRequired := true
  controlledExposureComparatorRequired := true
  symptomOrVisceralEndpointRequired := true
  histamineMastCellDAOAssayRequired := true
  allergyTolerabilitySurveillanceRequired := true
  practicalEffectRequired := true
}

structure QuailEggHistamineGutBoundary where
  quailMastCellEvidenceAcquired : Bool
  ovomucoidCellEvidenceAcquired : Bool
  ibsMicrobialHistamineEvidenceAcquired : Bool
  humanHistamineIBSMechanismAcquired : Bool
  serumDAOEqualsGutDAO : Bool
  quailEggClinicalIBSEfficacyEstablished : Bool
  recombinantProteinEqualsWholeFood : Bool
  compartmentSeparationRetained : Bool
  experimentBackpropSpecified : Bool
  deriving Repr, DecidableEq

def canonicalQuailEggHistamineGutBoundary : QuailEggHistamineGutBoundary := {
  quailMastCellEvidenceAcquired := true
  ovomucoidCellEvidenceAcquired := true
  ibsMicrobialHistamineEvidenceAcquired := true
  humanHistamineIBSMechanismAcquired := true
  serumDAOEqualsGutDAO := false
  quailEggClinicalIBSEfficacyEstablished := false
  recombinantProteinEqualsWholeFood := false
  compartmentSeparationRetained := true
  experimentBackpropSpecified := true
}

end Dashi.Biology.QuailEggHistamineGutSnowballExact
