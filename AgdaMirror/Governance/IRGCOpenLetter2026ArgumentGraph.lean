import AgdaMirror.Governance.IRGCOpenLetter2026

namespace AgdaMirror.Governance.IRGCOpenLetter2026.ArgumentGraph

open AgdaMirror.Governance.IRGCOpenLetter2026

inductive ArgumentNode
  | peopleStateDistinction
  | commonOppressorAssertion
  | sharedVictimAssertion
  | popularAgencyAssertion
  | conditionalCoexistenceAssertion
  | liberationAssertion
  | eschatologicalCompletion
  deriving DecidableEq, Repr

inductive SourceEdge : ArgumentNode → ArgumentNode → Prop
  | distinguishThenCommonOppressor :
      SourceEdge .peopleStateDistinction .commonOppressorAssertion
  | commonOppressorThenSharedVictim :
      SourceEdge .commonOppressorAssertion .sharedVictimAssertion
  | sharedVictimThenAgency :
      SourceEdge .sharedVictimAssertion .popularAgencyAssertion
  | agencyThenCoexistence :
      SourceEdge .popularAgencyAssertion .conditionalCoexistenceAssertion
  | coexistenceThenLiberation :
      SourceEdge .conditionalCoexistenceAssertion .liberationAssertion
  | liberationThenEschatology :
      SourceEdge .liberationAssertion .eschatologicalCompletion

structure SourceArgumentTopology where
  e1 : SourceEdge .peopleStateDistinction .commonOppressorAssertion
  e2 : SourceEdge .commonOppressorAssertion .sharedVictimAssertion
  e3 : SourceEdge .sharedVictimAssertion .popularAgencyAssertion
  e4 : SourceEdge .popularAgencyAssertion .conditionalCoexistenceAssertion
  e5 : SourceEdge .conditionalCoexistenceAssertion .liberationAssertion
  e6 : SourceEdge .liberationAssertion .eschatologicalCompletion
  sourceReceipt : String

def canonicalTopology : SourceArgumentTopology :=
  ⟨.distinguishThenCommonOppressor,
   .commonOppressorThenSharedVictim,
   .sharedVictimThenAgency,
   .agencyThenCoexistence,
   .coexistenceThenLiberation,
   .liberationThenEschatology,
   "IRGC 2026 primary English PDF: source-local argumentative sequence"⟩

inductive SharedInterestFactEstablished : Prop
inductive ThreatClassificationEstablished : Prop
inductive PropagandaEfficacyEstablished : Prop

theorem source_shared_victim_frame_does_not_establish_shared_interest_fact
    (_ : SourceArgumentTopology) : ¬ SharedInterestFactEstablished := by
  intro h
  cases h

theorem warning_does_not_auto_promote_to_threat
    (_ : SpeechAct) : ¬ ThreatClassificationEstablished := by
  intro h
  cases h

theorem source_structure_does_not_establish_propaganda_efficacy
    (_ : SourceArgumentTopology) : ¬ PropagandaEfficacyEstablished := by
  intro h
  cases h

structure AgencyHistoryEschatologyBracket where
  openingAgencyCitation : CrossTraditionCitation
  politicalAgencyNode : ArgumentNode
  liberationNode : ArgumentNode
  closingEschatologyCitation : CrossTraditionCitation

def canonicalBracket : AgencyHistoryEschatologyBracket :=
  ⟨quranAgency, .popularAgencyAssertion, .liberationAssertion, quranClosure⟩

/-- Positive theorem: the typed source-local chain exists as a complete path.
    It says nothing about the truth of the contested premises. -/
theorem canonical_argument_path_exists :
    SourceEdge .peopleStateDistinction .commonOppressorAssertion ∧
    SourceEdge .commonOppressorAssertion .sharedVictimAssertion ∧
    SourceEdge .sharedVictimAssertion .popularAgencyAssertion ∧
    SourceEdge .popularAgencyAssertion .conditionalCoexistenceAssertion ∧
    SourceEdge .conditionalCoexistenceAssertion .liberationAssertion ∧
    SourceEdge .liberationAssertion .eschatologicalCompletion := by
  exact ⟨.distinguishThenCommonOppressor,
    .commonOppressorThenSharedVictim,
    .sharedVictimThenAgency,
    .agencyThenCoexistence,
    .coexistenceThenLiberation,
    .liberationThenEschatology⟩

end AgdaMirror.Governance.IRGCOpenLetter2026.ArgumentGraph
