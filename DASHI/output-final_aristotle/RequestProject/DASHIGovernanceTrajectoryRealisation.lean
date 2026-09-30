/-!
Governance trajectory / realised-policy gap kernel.

This is the party-neutral formal core recovered from the March 2026
O/R/C/S/L/P/G/F governance discussion. Concrete political organisations,
policy histories, and empirical claims enter only as source-indexed witnesses.

Prior-art weld:
* DASHIContextIndexedTransport: consumer/query-scoped evidence and transport.
* The Agda mirror additionally cross-pollinates the contextual 369 dialectic
  and comparison/synthesis owners.

No theorem in this file endorses, ranks, or universally prefers a political
party, strategy, or policy.
-/

import RequestProject.DASHIContextIndexedTransport

namespace DASHI.GovernanceTrajectory

open DASHI.ContextIndexedOntology

structure ZKPModel
    (Organization Requirement Code State Lattice Proposal Gap : Type) where
  O : Organization
  R : Requirement
  C : Code
  S : State
  L : Lattice
  P : Proposal
  G : Proposal → State → Bool
  F : Organization → Requirement → Code → State → Lattice → Gap

structure Dynamics
    (Organization State Lattice Proposal Code : Type) where
  transition : Organization → State → Proposal → Code → State
  latticeUpdate : Organization → Lattice → Proposal → Code → State → Lattice

def Dynamics.stepState
    {Organization State Lattice Proposal Code : Type}
    (d : Dynamics Organization State Lattice Proposal Code)
    (o : Organization) (s : State) (p : Proposal) (c : Code) : State :=
  d.transition o s p c

def Dynamics.stepLattice
    {Organization State Lattice Proposal Code : Type}
    (d : Dynamics Organization State Lattice Proposal Code)
    (o : Organization) (l : Lattice) (p : Proposal) (c : Code) (s : State) : Lattice :=
  d.latticeUpdate o l p c s

inductive ProposalOrientation
  | supports
  | neutral
  | counters
  deriving DecidableEq, Repr

structure ContextualProposalSystem (Frame Proposal : Type) where
  orientationIn : Frame → Proposal → ProposalOrientation

structure ProposalOrientationChange
    {Frame Proposal : Type}
    (system : ContextualProposalSystem Frame Proposal) where
  proposal : Proposal
  firstFrame : Frame
  secondFrame : Frame
  changed :
    system.orientationIn firstFrame proposal ≠
      system.orientationIn secondFrame proposal

theorem orientationChangeBlocksIntrinsicSign
    {Frame Proposal : Type}
    {system : ContextualProposalSystem Frame Proposal}
    (w : ProposalOrientationChange system)
    (intrinsic : Proposal → ProposalOrientation)
    (agrees : ∀ frame proposal,
      system.orientationIn frame proposal = intrinsic proposal) :
    False := by
  apply w.changed
  exact (agrees w.firstFrame w.proposal).trans
    (agrees w.secondFrame w.proposal).symm

structure IncrementalAcceptance (State Proposal : Type) where
  improvesCurrentGap : State → Proposal → Prop
  expandsFutureReachability : State → Proposal → Prop

def IncrementalAcceptance.accepts
    {State Proposal : Type}
    (rule : IncrementalAcceptance State Proposal)
    (s : State) (p : Proposal) : Prop :=
  rule.improvesCurrentGap s p ∧ rule.expandsFutureReachability s p

structure ThresholdAcceptance (State Proposal : Type) where
  clearsThreshold : State → Proposal → Prop
  acceptableLockInRisk : State → Proposal → Prop

def ThresholdAcceptance.accepts
    {State Proposal : Type}
    (rule : ThresholdAcceptance State Proposal)
    (s : State) (p : Proposal) : Prop :=
  rule.clearsThreshold s p ∧ rule.acceptableLockInRisk s p

structure StrategyWitness
    {State Proposal : Type}
    (incremental : IncrementalAcceptance State Proposal)
    (threshold : ThresholdAcceptance State Proposal)
    (state : State) (proposal : Proposal) where
  incrementalPremise : incremental.improvesCurrentGap state proposal
  reachabilityPremise : incremental.expandsFutureReachability state proposal
  thresholdPremise : threshold.clearsThreshold state proposal
  lockInPremise : threshold.acceptableLockInRisk state proposal

inductive EvidenceKind
  | observed
  | interpolated
  | counterfactual
  | speculative
  deriving DecidableEq, Repr

structure GovernanceEvidence where
  sourceRevision : String
  statementRef : String
  provenanceRefs : List String
  kind : EvidenceKind
  supportRefs : List String
  counterRefs : List String
  missingRefs : List String
  deriving Repr

structure GapEstimate (Gap Uncertainty : Type) where
  gap : Gap
  uncertainty : Uncertainty
  evidence : List GovernanceEvidence

structure ComparativeWitness
    (Organization Requirement Code State Lattice Gap Uncertainty : Type)
    (gapFn : Organization → Requirement → Code → State → Lattice → Gap) where
  left : Organization
  right : Organization
  requirement : Requirement
  code : Code
  state : State
  lattice : Lattice
  leftEstimate : GapEstimate Gap Uncertainty
  rightEstimate : GapEstimate Gap Uncertainty
  leftEstimateMatches :
    leftEstimate.gap = gapFn left requirement code state lattice
  rightEstimateMatches :
    rightEstimate.gap = gapFn right requirement code state lattice
  sourceFrame : String
  sourceRevisionRefs : List String

structure LocalGapOrdering {Gap : Type} (left right : Gap) where
  relation : Prop
  witnessRef : String

structure ScopedComparativeClaim
    {Organization Requirement Code State Lattice Gap Uncertainty : Type}
    {gapFn : Organization → Requirement → Code → State → Lattice → Gap}
    (w : ComparativeWitness Organization Requirement Code State Lattice Gap Uncertainty gapFn)
    where
  ordering : LocalGapOrdering w.leftEstimate.gap w.rightEstimate.gap
  reviewRequired : Bool
  universalDominance : Bool
  universalDominanceFalse : universalDominance = false

def GovernanceEvidence.toLedger (e : GovernanceEvidence) : EvidenceLedger :=
  {
    support := e.supportRefs
    counter := e.counterRefs
    missing := e.missingRefs
    provenance := e.provenanceRefs
  }

@[simp] theorem GovernanceEvidence.toLedger_support
    (e : GovernanceEvidence) :
    e.toLedger.support = e.supportRefs := rfl

@[simp] theorem GovernanceEvidence.toLedger_counter
    (e : GovernanceEvidence) :
    e.toLedger.counter = e.counterRefs := rfl

inductive DemoFrame
  | immediateOutcome
  | futureReachability
  deriving DecidableEq, Repr

inductive DemoProposal
  | sameProposal
  deriving DecidableEq, Repr

def demoProposalSystem : ContextualProposalSystem DemoFrame DemoProposal where
  orientationIn
    | .immediateOutcome, .sameProposal => .supports
    | .futureReachability, .sameProposal => .counters

def demoOrientationChange : ProposalOrientationChange demoProposalSystem where
  proposal := .sameProposal
  firstFrame := .immediateOutcome
  secondFrame := .futureReachability
  changed := by decide

theorem noIntrinsicProposalSign
    (intrinsic : DemoProposal → ProposalOrientation)
    (agrees : ∀ frame proposal,
      demoProposalSystem.orientationIn frame proposal = intrinsic proposal) :
    False :=
  orientationChangeBlocksIntrinsicSign demoOrientationChange intrinsic agrees

structure Boundary where
  contextIndexedProposalSign : Bool
  thresholdAndIncrementalSeparated : Bool
  evidenceKindTracked : Bool
  historicalWitnessImpliesUniversalRanking : Bool
  synthesisErasesPriorComparison : Bool
  deriving DecidableEq, Repr

def canonicalBoundary : Boundary :=
  {
    contextIndexedProposalSign := true
    thresholdAndIncrementalSeparated := true
    evidenceKindTracked := true
    historicalWitnessImpliesUniversalRanking := false
    synthesisErasesPriorComparison := false
  }

@[simp] theorem canonicalBoundary_contextual :
    canonicalBoundary.contextIndexedProposalSign = true := rfl

@[simp] theorem canonicalBoundary_noUniversalRanking :
    canonicalBoundary.historicalWitnessImpliesUniversalRanking = false := rfl

end DASHI.GovernanceTrajectory
