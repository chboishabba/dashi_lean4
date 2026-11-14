import Dashi.Biology.QuailEggGutTransferRound2Exact
import Dashi.Biology.QuailEggAllergySafetyBoundaryExact
import Dashi.Biology.GutMastCellMechanismRouteAtlasExact

namespace Dashi.Biology.QuailEggIBSTransferLadderExact

open Dashi.Biology.QuailEggGutTransferRound2Exact
open Dashi.Biology.QuailEggAllergySafetyBoundaryExact
open Dashi.Biology.GutMastCellMechanismRouteAtlasExact

inductive TransferStage where
  | biochemicalStabilityStage | cellMastCellStage | oralGIAnimalStage
  | humanOralNonIBSStage | humanIBSMechanismStage | humanIBSQuailInterventionStage
  deriving Repr, DecidableEq
inductive TransferStatus where
  | paidBounded | paidAdjacent | openTerminal
  deriving Repr, DecidableEq

structure TransferStageReceipt where
  stage : TransferStage
  status : TransferStatus
  ownerReference : String
  paidReading : String
  residual : String
  deriving Repr, DecidableEq

def biochemicalStageReceipt : TransferStageReceipt := {
  stage := .biochemicalStabilityStage, status := .paidBounded,
  ownerReference := "QuailEggGutTransferRound2Exact.quailOvomucoidStability1994Receipt",
  paidReading := "biochemical ovomucoid survival plausibility",
  residual := "post-digestion anti-mast-cell activity and human intestinal target engagement" }

def cellMastCellStageReceipt : TransferStageReceipt := {
  stage := .cellMastCellStage, status := .paidBounded,
  ownerReference := "QuailEggHistamineGutSnowballExact.lianto2018QuailEggReceipt",
  paidReading := "quail albumen anti-degranulation cell evidence",
  residual := "dose/exposure/target and human IBS transfer" }

def oralGIAnimalStageReceipt : TransferStageReceipt := {
  stage := .oralGIAnimalStage, status := .paidBounded,
  ownerReference := "QuailEggOralGIAnimalBridgeExact.lianto2018EoEReceipt",
  paidReading := "oral whole-quail-egg homogenate GI/allergic mouse evidence",
  residual := "species/disease-model transfer" }

def humanOralStageReceipt : TransferStageReceipt := {
  stage := .humanOralNonIBSStage, status := .paidBounded,
  ownerReference := "QuailEggHumanOralTransferExact",
  paidReading := "randomized human oral quail-product exposure in rhinitis/allergen challenge",
  residual := "gut target engagement and IBS endpoint" }

def humanIBSMechanismStageReceipt : TransferStageReceipt := {
  stage := .humanIBSMechanismStage, status := .paidAdjacent,
  ownerReference := "GutMastCellMechanismRouteAtlasExact",
  paidReading := "bounded human IBS histamine/mast-cell/barrier mechanisms",
  residual := "no quail intervention in those IBS studies" }

def humanIBSQuailStageReceipt : TransferStageReceipt := {
  stage := .humanIBSQuailInterventionStage, status := .openTerminal,
  ownerReference := "QuailEggGutTransferRound2Exact.canonicalSameObjectQuailGutExperiment",
  paidReading := "terminal experiment specified",
  residual := "quail-specific human IBS target-engagement and clinical evidence" }

structure HumanIBSQuailTerminalReceipt where
  terminalClosed : Bool
  sameObjectExperiment : SameObjectQuailGutExperiment
  safetyRequirement : QuailEggInterventionSafetyRequirement
  mechanismAtlas : GutMastCellMechanismRouteAtlas
  acquisitionReference : String
  deriving Repr, DecidableEq

def canonicalHumanIBSQuailTerminalReceipt : HumanIBSQuailTerminalReceipt := {
  terminalClosed := false
  sameObjectExperiment := canonicalSameObjectQuailGutExperiment
  safetyRequirement := canonicalQuailEggInterventionSafetyRequirement
  mechanismAtlas := canonicalGutMastCellMechanismRouteAtlas
  acquisitionReference := "Need prospective human IBS quail intervention or equivalent same-object evidence; adjacent studies cannot close the terminal."
}

inductive AdjacentEvidenceClosesHumanIBSPermission : Prop
theorem adjacentEvidenceDoesNotCloseHumanIBS : AdjacentEvidenceClosesHumanIBSPermission → False := by intro h; cases h

structure QuailEggIBSTransferLadder where
  biochemicalStage : TransferStageReceipt
  biochemicalStageIsCorrect : biochemicalStage.stage = .biochemicalStabilityStage
  biochemicalStatusIsPaid : biochemicalStage.status = .paidBounded
  mastCellStage : TransferStageReceipt
  mastCellStageIsCorrect : mastCellStage.stage = .cellMastCellStage
  mastCellStatusIsPaid : mastCellStage.status = .paidBounded
  animalStage : TransferStageReceipt
  animalStageIsCorrect : animalStage.stage = .oralGIAnimalStage
  animalStatusIsPaid : animalStage.status = .paidBounded
  humanOralStage : TransferStageReceipt
  humanOralStageIsCorrect : humanOralStage.stage = .humanOralNonIBSStage
  humanOralStatusIsPaid : humanOralStage.status = .paidBounded
  ibsMechanismStage : TransferStageReceipt
  ibsMechanismStageIsCorrect : ibsMechanismStage.stage = .humanIBSMechanismStage
  ibsMechanismStatusIsAdjacent : ibsMechanismStage.status = .paidAdjacent
  ibsQuailStage : TransferStageReceipt
  ibsQuailStageIsCorrect : ibsQuailStage.stage = .humanIBSQuailInterventionStage
  ibsQuailStatusIsOpen : ibsQuailStage.status = .openTerminal
  terminal : HumanIBSQuailTerminalReceipt
  terminalRemainsOpen : terminal.terminalClosed = false

def canonicalQuailEggIBSTransferLadder : QuailEggIBSTransferLadder := {
  biochemicalStage := biochemicalStageReceipt
  biochemicalStageIsCorrect := rfl
  biochemicalStatusIsPaid := rfl
  mastCellStage := cellMastCellStageReceipt
  mastCellStageIsCorrect := rfl
  mastCellStatusIsPaid := rfl
  animalStage := oralGIAnimalStageReceipt
  animalStageIsCorrect := rfl
  animalStatusIsPaid := rfl
  humanOralStage := humanOralStageReceipt
  humanOralStageIsCorrect := rfl
  humanOralStatusIsPaid := rfl
  ibsMechanismStage := humanIBSMechanismStageReceipt
  ibsMechanismStageIsCorrect := rfl
  ibsMechanismStatusIsAdjacent := rfl
  ibsQuailStage := humanIBSQuailStageReceipt
  ibsQuailStageIsCorrect := rfl
  ibsQuailStatusIsOpen := rfl
  terminal := canonicalHumanIBSQuailTerminalReceipt
  terminalRemainsOpen := rfl
}

def canonicalStages : List TransferStageReceipt := [
  canonicalQuailEggIBSTransferLadder.biochemicalStage,
  canonicalQuailEggIBSTransferLadder.mastCellStage,
  canonicalQuailEggIBSTransferLadder.animalStage,
  canonicalQuailEggIBSTransferLadder.humanOralStage,
  canonicalQuailEggIBSTransferLadder.ibsMechanismStage,
  canonicalQuailEggIBSTransferLadder.ibsQuailStage
]

structure QuailEggIBSTransferLadderBoundary where
  biochemicalSurvivalPaid : Bool
  preclinicalMastCellPaid : Bool
  oralGIAnimalPaid : Bool
  humanOralExposurePaid : Bool
  humanIBSMechanismsPaidAdjacent : Bool
  quailSpecificHumanIBSTerminalClosed : Bool
  furtherAdjacentLiteratureCannotSubstituteForTerminal : Bool
  deriving Repr, DecidableEq

def canonicalQuailEggIBSTransferLadderBoundary : QuailEggIBSTransferLadderBoundary := {
  biochemicalSurvivalPaid := true
  preclinicalMastCellPaid := true
  oralGIAnimalPaid := true
  humanOralExposurePaid := true
  humanIBSMechanismsPaidAdjacent := true
  quailSpecificHumanIBSTerminalClosed := false
  furtherAdjacentLiteratureCannotSubstituteForTerminal := true
}

end Dashi.Biology.QuailEggIBSTransferLadderExact
