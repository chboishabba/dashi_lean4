import Dashi.Biology.GABAPhenotypeEvidenceExact

namespace Dashi.Biology.QuailEggAllergySafetyBoundaryExact
open Dashi.Biology.GABAPhenotypeEvidenceExact

def delgadoPrada2025Source : AttributedSource :=
  mkDOISource
    "Ana Delgado-Prada; Maria Jose Martinez-Martinez; Enrique Burches; Angel Sastre-Sastre; Fernando Pineda De La Losa; Celia Morales-Rubio"
    "Quail egg allergy with tolerance to chicken eggs: A case report"
    "Journal of Allergy and Clinical Immunology: Global 4(3):100486" "2025"
    "10.1016/j.jacig.2025.100486" "https://doi.org/10.1016/j.jacig.2025.100486"
    "Single adult case establishing the possibility of quail-egg allergy despite chicken-egg tolerance; not prevalence or population risk."

def yamashita2024Source : AttributedSource :=
  mkDOISource
    "Kosei Yamashita; Yuki Okada; Aiko Honda; Chihiro Kunigami; Mayu Maeda; Toshinori Nakamura; Taro Kamiya; Takanori Imai"
    "Clinical Features of Quail Egg Ingestion in Patients with Acquired Tolerance to Hen Eggs: A Case Series Study"
    "International Archives of Allergy and Immunology 185(2):152-157" "2024"
    "10.1159/000534825" "https://doi.org/10.1159/000534825"
    "Prospective pediatric oral-food-challenge case series with no reaction among the 59 participants completing three boiled quail eggs; not universal safety."

inductive SafetyEvidenceKind where
  | individualCaseReport | prospectiveOralChallengeCaseSeries
  deriving Repr, DecidableEq

structure QuailEggAllergyEvidenceReceipt where
  source : AttributedSource
  evidenceKind : SafetyEvidenceKind
  henEggTolerancePresent : Bool
  quailEggReactionObserved : Bool
  populationGuaranteePaid : Bool
  boundary : String
  deriving Repr, DecidableEq

def delgadoPrada2025Receipt : QuailEggAllergyEvidenceReceipt := {
  source := delgadoPrada2025Source
  evidenceKind := .individualCaseReport
  henEggTolerancePresent := true
  quailEggReactionObserved := true
  populationGuaranteePaid := false
  boundary := "Counterexample surface only: hen-egg tolerance does not guarantee quail tolerance; a case report does not quantify prevalence."
}

def yamashita2024Receipt : QuailEggAllergyEvidenceReceipt := {
  source := yamashita2024Source
  evidenceKind := .prospectiveOralChallengeCaseSeries
  henEggTolerancePresent := true
  quailEggReactionObserved := false
  populationGuaranteePaid := false
  boundary := "Bounded reassuring challenge evidence in one pediatric cohort; no universal quail-tolerance theorem."
}

inductive HenEggToleranceImpliesQuailEggTolerancePermission : Prop
inductive OneCaseDeterminesPopulationRiskPermission : Prop
inductive OneCaseSeriesDeterminesUniversalSafetyPermission : Prop

theorem henToleranceDoesNotGuaranteeQuailTolerance : HenEggToleranceImpliesQuailEggTolerancePermission → False := by intro h; cases h
theorem oneCaseDoesNotDeterminePopulationRisk : OneCaseDeterminesPopulationRiskPermission → False := by intro h; cases h
theorem caseSeriesDoesNotDetermineUniversalSafety : OneCaseSeriesDeterminesUniversalSafetyPermission → False := by intro h; cases h

structure QuailEggInterventionSafetyRequirement where
  agdaExperimentalDesignOwner : String
  quailSpecificAllergyHistoryRequired : Bool
  adverseEventSurveillanceRequired : Bool
  henEggToleranceCannotSubstituteForQuailAssessment : Bool
  stoppingCriteriaRequired : Bool
  deriving Repr, DecidableEq

def canonicalQuailEggInterventionSafetyRequirement : QuailEggInterventionSafetyRequirement := {
  agdaExperimentalDesignOwner := "DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact"
  quailSpecificAllergyHistoryRequired := true
  adverseEventSurveillanceRequired := true
  henEggToleranceCannotSubstituteForQuailAssessment := true
  stoppingCriteriaRequired := true
}

structure QuailEggAllergySafetyBoundary where
  rareDiscordantAllergyPossibilityPaid : Bool
  boundedReassuringChallengeEvidencePaid : Bool
  henEggToleranceGuaranteesQuailTolerance : Bool
  prevalenceEstablishedByCaseReport : Bool
  universalSafetyEstablishedByCaseSeries : Bool
  safetyMustRemainInInterventionDesign : Bool
  deriving Repr, DecidableEq

def canonicalQuailEggAllergySafetyBoundary : QuailEggAllergySafetyBoundary := {
  rareDiscordantAllergyPossibilityPaid := true
  boundedReassuringChallengeEvidencePaid := true
  henEggToleranceGuaranteesQuailTolerance := false
  prevalenceEstablishedByCaseReport := false
  universalSafetyEstablishedByCaseSeries := false
  safetyMustRemainInInterventionDesign := true
}

end Dashi.Biology.QuailEggAllergySafetyBoundaryExact
