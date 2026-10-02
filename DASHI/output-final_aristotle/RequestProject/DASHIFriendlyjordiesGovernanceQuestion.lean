/-!
Named March-2026 Friendlyjordies governance application surface.

This records the comparison question only. Party names and case labels do not
constitute evidence and no winner/ranking is encoded. Historical assertions
must be supplied later through source-revision witnesses.
-/

import RequestProject.DASHIGovernanceTrajectoryRealisation

namespace DASHI.GovernanceTrajectory

inductive AustralianPoliticalFormation
  | labor
  | greens
  deriving DecidableEq, Repr

inductive MarchCase
  | cprs2009
  | southAustraliaRenewables
  deriving DecidableEq, Repr

inductive ComparisonHorizon
  | immediate
  | longRun
  deriving DecidableEq, Repr

structure MarchGovernanceQuestion where
  leftFormation : AustralianPoliticalFormation
  rightFormation : AustralianPoliticalFormation
  cases : List MarchCase
  horizons : List ComparisonHorizon
  sourceWitnessRequired : Bool
  counterfactualWitnessRequired : Bool
  universalRankingEncoded : Bool
  deriving DecidableEq, Repr

def canonicalMarchGovernanceQuestion : MarchGovernanceQuestion :=
  {
    leftFormation := .labor
    rightFormation := .greens
    cases := [.cprs2009, .southAustraliaRenewables]
    horizons := [.immediate, .longRun]
    sourceWitnessRequired := true
    counterfactualWitnessRequired := true
    universalRankingEncoded := false
  }

structure HistoricalCaseEvidence where
  case : MarchCase
  sourceRevisionRef : String
  statementRef : String
  provenanceRefs : List String
  evidenceKind : EvidenceKind
  sourceChecked : Bool
  deriving Repr

@[simp] theorem canonicalQuestion_requiresSources :
    canonicalMarchGovernanceQuestion.sourceWitnessRequired = true := rfl

@[simp] theorem canonicalQuestion_noRanking :
    canonicalMarchGovernanceQuestion.universalRankingEncoded = false := rfl

end DASHI.GovernanceTrajectory
