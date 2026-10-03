import AgdaMirror.Cognition.PNF.SensibLawITIRNarrativeComparisonTransport
import AgdaMirror.Governance.AustralianLabourMarxianContactBoundary

namespace AgdaMirror.Governance.FriendlyjordiesNarrativeGovernanceTransport

open AgdaMirror.Cognition.PNF.SensibLawITIRNarrativeComparisonTransport
open AgdaMirror.Governance.AustralianLabourMarxianContactBoundary

def fjordiesSpan : SourceSpan :=
  ⟨"jordies_case", "thread:Climate-Change-Politics-AU",
   "public-media / archive-backed Friendlyjordies proposition fixture", true⟩

def counterSpan : SourceSpan :=
  ⟨"counter_analysis", "thread:Climate-Change-Politics-AU:counter",
   "balanced / counter-analysis lane from bounded comparison fixture", true⟩

def cprsClaim : AttributedProposition :=
  ⟨"prop:cprs:block", "block", fjordiesSpan, "FriendlyJordies",
   "source-local authority chain preserved by fixture", .interpreted, .cprsBlocking⟩

def governmentCapacityClaim : AttributedProposition :=
  ⟨"prop:government:capacity", "support", fjordiesSpan, "FriendlyJordies",
   "source-local authority chain preserved by fixture", .interpreted, .governmentCapacity⟩

def counterGovernmentClaim : AttributedProposition :=
  ⟨"prop:government:counter", "pass", counterSpan, "counter-analysis",
   "source-local counter-analysis", .interpreted, .governmentCapacity⟩

def supportLink : ClaimLink :=
  ⟨"link:jordies:cprs-government", .supports,
   "prop:cprs:block", "prop:government:capacity", .causalSupport, .medium,
   "counter_hypothesis:policy-capacity-may-depend-on-institutional-and-electoral-conditions-beyond-cprs",
   "SensibLaw A3 causal-link provenance contract", true⟩

def disputeLink : ClaimLink :=
  ⟨"link:comparison:government-capacity", .undermines,
   "prop:government:capacity", "prop:government:counter", .causalDispute, .medium,
   "counter_hypothesis:shared-outcome-may-have-multiple-causal-paths",
   "SensibLaw comparison receipt: shared subject / governance-family causal dispute", true⟩

def jordiesLane : NarrativeLane :=
  canonicalLaneBoundary "jordies_case" [cprsClaim, governmentCapacityClaim] [supportLink]

def counterLane : NarrativeLane :=
  canonicalLaneBoundary "counter_analysis" [counterGovernmentClaim] []

def comparisonRow : ComparisonRow :=
  ⟨"comparison:government-capacity", .disputed,
   "prop:government:capacity", "prop:government:counter",
   "support versus pass predicates preserve causal disagreement",
   "SensibLaw Friendlyjordies comparison fixtures", false⟩

def canonicalFriendlyjordiesComparison : NarrativeComparison :=
  canonicalComparison jordiesLane counterLane [comparisonRow]

structure GovernanceWitness where
  comparison : NarrativeComparison
  historicalLabourContact : ContactReceipt
  evidenceQualified : Bool := true
  missingnessRetained : Bool := true
  trajectoryInferenceClosed : Bool := false
  politicalVerdictIssued : Bool := false
  sourceNarrativePromotedToFact : Bool := false

def friendlyjordiesGovernanceWitness : GovernanceWitness :=
  ⟨canonicalFriendlyjordiesComparison, leninLaborCritique⟩

theorem friendlyjordies_transport_is_fail_closed :
    friendlyjordiesGovernanceWitness.comparison.disagreementPreserved = true ∧
    friendlyjordiesGovernanceWitness.comparison.truthScoreProduced = false ∧
    friendlyjordiesGovernanceWitness.trajectoryInferenceClosed = false ∧
    friendlyjordiesGovernanceWitness.politicalVerdictIssued = false ∧
    friendlyjordiesGovernanceWitness.sourceNarrativePromotedToFact = false := by
  decide

end AgdaMirror.Governance.FriendlyjordiesNarrativeGovernanceTransport
