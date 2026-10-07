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

def canonicalStages : List TransferStageReceipt := [
  { stage := .biochemicalStabilityStage, status := .paidBounded,
    ownerReference := "QuailEggGutTransferRound2Exact.quailOvomucoidStability1994Receipt",
    paidReading := "biochemical ovomucoid survival plausibility",
    residual := "post-digestion anti-mast-cell activity and human intestinal target engagement" },
  { stage := .cellMastCellStage, status := .paidBounded,
    ownerReference := "QuailEggHistamineGutSnowballExact.lianto2018QuailEggReceipt",
    paidReading := "quail albumen anti-degranulation cell evidence",
    residual := "dose/exposure/target and human IBS transfer" },
  { stage := .oralGIAnimalStage, status := .paidBounded,
    ownerReference := "QuailEggOralGIAnimalBridgeExact.lianto2018EoEReceipt",
    paidReading := "oral whole-quail GI allergic mouse evidence",
    residual := "species/disease-model transfer" },
  { stage := .humanOralNonIBSStage, status := .paidBounded,
    ownerReference := "QuailEggHumanOralTransferExact",
    paidReading := "randomized human oral quail-product exposure in rhinitis/allergen challenge",
    residual := "gut target engagement and IBS endpoint" },
  { stage := .humanIBSMechanismStage, status := .paidAdjacent,
    ownerReference := "GutMastCellMechanismRouteAtlasExact",
    paidReading := "bounded human IBS histamine/mast-cell/barrier mechanisms",
    residual := "no quail intervention in those IBS studies" },
  { stage := .humanIBSQuailInterventionStage, status := .openTerminal,
    ownerReference := "QuailEggGutTransferRound2Exact.canonicalSameObjectQuailGutExperiment",
    paidReading := "terminal experiment specified",
    residual := "quail-specific human IBS target-engagement and clinical evidence" }
]

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
  stages : List TransferStageReceipt
  terminal : HumanIBSQuailTerminalReceipt
  sourceRolesRetained : Bool
  adjacentEvidenceRetainedWithoutPromotion : Bool
  deriving Repr, DecidableEq

def canonicalQuailEggIBSTransferLadder : QuailEggIBSTransferLadder := {
  stages := canonicalStages
  terminal := canonicalHumanIBSQuailTerminalReceipt
  sourceRolesRetained := true
  adjacentEvidenceRetainedWithoutPromotion := true
}

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
