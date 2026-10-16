import Dashi.Biology.GABAPhenotypeEvidenceExact

namespace Dashi.Biology.QuailEggOralGIAnimalBridgeExact
open Dashi.Biology.GABAPhenotypeEvidenceExact

def lianto2018EoESource : AttributedSource :=
  mkDOISource
    "Priscilia Lianto; Shiwen Han; Xinrui Li; Fredrick Onyango Ogutu; Yani Zhang; Zhuoyan Fan; Huilian Che"
    "Quail egg homogenate alleviates food allergy induced eosinophilic esophagitis like disease through modulating PAR-2 transduction pathway in peanut sensitized mice"
    "Scientific Reports 8:1049" "2018"
    "10.1038/s41598-018-19309-x" "https://doi.org/10.1038/s41598-018-19309-x"
    "Daily oral whole-quail-egg intervention evidence in a peanut-sensitized mouse EoE-like food-allergy model; not human IBS efficacy."

structure QuailOralGIAnimalReceipt where
  source : AttributedSource
  oralWholeQuailExposure : Bool
  gastrointestinalInflammatoryModel : Bool
  tryptaseOrEosinophilEndpoints : Bool
  par2NFkBPathwayEvidence : Bool
  humanPopulation : Bool
  ibsPopulation : Bool
  boundary : String
  deriving Repr, DecidableEq

def lianto2018EoEReceipt : QuailOralGIAnimalReceipt := {
  source := lianto2018EoESource
  oralWholeQuailExposure := true
  gastrointestinalInflammatoryModel := true
  tryptaseOrEosinophilEndpoints := true
  par2NFkBPathwayEvidence := true
  humanPopulation := false
  ibsPopulation := false
  boundary := "Oral GI animal evidence narrows the transfer gap beyond cells; species, disease model, sensitization, dose and IBS transfer remain open."
}

inductive MouseEoEEvidencePaysHumanIBSPermission : Prop
inductive MouseOralExposurePaysHumanTargetEngagementPermission : Prop

theorem mouseEoEDoesNotPayHumanIBS : MouseEoEEvidencePaysHumanIBSPermission → False := by intro h; cases h
theorem mouseOralDoesNotPayHumanTargetEngagement : MouseOralExposurePaysHumanTargetEngagementPermission → False := by intro h; cases h

structure QuailOralGIAnimalBoundary where
  oralGIAnimalExposurePaid : Bool
  par2PathwayAnimalEvidencePaid : Bool
  humanGIExposurePaidByThisStudy : Bool
  humanIBSEfficacyPaid : Bool
  deriving Repr, DecidableEq

def canonicalQuailOralGIAnimalBoundary : QuailOralGIAnimalBoundary := {
  oralGIAnimalExposurePaid := true
  par2PathwayAnimalEvidencePaid := true
  humanGIExposurePaidByThisStudy := false
  humanIBSEfficacyPaid := false
}

end Dashi.Biology.QuailEggOralGIAnimalBridgeExact
