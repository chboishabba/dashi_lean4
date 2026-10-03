import Mathlib

/-!
# Grounded agent authority trajectories

A Lean formalisation of the zkSEC/zkperf security geometry used to analyse
autonomous-agent incidents.

The central boundary is intentionally epistemic:
public telemetry can propose a trajectory edge, but authority-bearing failure
claims require a grounded execution witness.

The core security property is not a claim about motive or "malice".  It is a
typed no-silent-authority-crossing invariant over capabilities, channels,
rings, destinations, transforms, and explicit receipts.
-/

namespace Security.AgentAuthorityTrajectory

inductive GroundingState
  | proposalOnly
  | grounded
  deriving DecidableEq, Repr

inductive Capability
  | readCap
  | writeCap
  | executeCap
  | networkEgressCap
  | identityMutationCap
  | policyMutationCap
  deriving DecidableEq, Repr

inductive Channel
  | localChannel
  | selfChannel
  | trustedPeerChannel
  | publicChannel
  | remoteAPIChannel
  deriving DecidableEq, Repr

inductive Ring
  | sovereignRing
  | boundedRing
  | remoteRing
  deriving DecidableEq, Repr

inductive Transform
  | classifyTransform
  | ingestTransform
  | readTransform
  | reviewTransform
  | probeTransform
  | publishTransform
  | executeTransform
  | patchTransform
  deriving DecidableEq, Repr

structure ActionEnvelope where
  capability : Capability
  channel : Channel
  ring : Ring
  destination : String
  transform : Transform
  receiptRef : String
  deriving Repr

structure AuthorityPolicy where
  capabilityAllowed : Capability → Prop
  channelAllowed : Channel → Prop
  ringAllowed : Ring → Prop
  destinationAllowed : String → Prop
  transformAllowed : Transform → Prop
  receiptAuthorized : String → Prop

structure Admissible (policy : AuthorityPolicy) (action : ActionEnvelope) : Prop where
  capabilityOK : policy.capabilityAllowed action.capability
  channelOK : policy.channelAllowed action.channel
  ringOK : policy.ringAllowed action.ring
  destinationOK : policy.destinationAllowed action.destination
  transformOK : policy.transformAllowed action.transform
  receiptOK : policy.receiptAuthorized action.receiptRef

structure GroundedAction where
  action : ActionEnvelope
  groundingState : GroundingState
  groundingIsGrounded : groundingState = .grounded
  evidenceRef : String

/-- Public or otherwise proposal-only telemetry.  It carries no authority proof. -/
structure ProposalTelemetry where
  sourceRef : String

structure GroundedExecutionReceipt where
  actionEvidence : GroundedAction
  runtimeReceiptRef : String

/-- A grounded action requesting a capability outside the granted policy is inadmissible. -/
theorem groundedUnauthorizedExpansion
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (capabilityDenied :
      ¬ policy.capabilityAllowed witness.action.capability) :
    ¬ Admissible policy witness.action := by
  intro h
  exact capabilityDenied h.capabilityOK

/-- A grounded action targeting an out-of-scope destination is inadmissible. -/
theorem groundedUnauthorizedDestination
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (destinationDenied :
      ¬ policy.destinationAllowed witness.action.destination) :
    ¬ Admissible policy witness.action := by
  intro h
  exact destinationDenied h.destinationOK

/-- Transform drift into an ungranted action class is inadmissible. -/
theorem groundedUnauthorizedTransform
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (transformDenied :
      ¬ policy.transformAllowed witness.action.transform) :
    ¬ Admissible policy witness.action := by
  intro h
  exact transformDenied h.transformOK

/-- A trajectory receipt identifying the earliest grounded inadmissible edge. -/
structure FirstAuthorityCrossing (policy : AuthorityPolicy) where
  admissiblePrefix : List ActionEnvelope
  crossing : GroundedAction
  suffix : List ActionEnvelope
  prefixIsAdmissible : ∀ a ∈ admissiblePrefix, Admissible policy a
  crossingIsDenied : ¬ Admissible policy crossing.action

theorem firstAuthorityCrossingSound
    (policy : AuthorityPolicy)
    (w : FirstAuthorityCrossing policy) :
    ¬ Admissible policy w.crossing.action :=
  w.crossingIsDenied

/-- Learning how to perform an operation is a separate carrier from authority to perform it. -/
structure LearnedProcedure where
  procedureRef : String

structure ExecutionAuthority where
  authorizedReceiptRef : String
  authorizedCapability : Capability
  authorizedDestination : String

/-- Abstract hash commitments for a privacy-preserving trajectory chain. -/
structure StepCommitment where
  priorCommitment : String
  actionCommitment : String
  observationCommitment : String
  receiptCommitment : String
  resultingCommitment : String

structure ConformanceProofStatement (policy : AuthorityPolicy) : Prop where
  committedAction : GroundedAction
  committedStep : StepCommitment
  admitted : Admissible policy committedAction.action

structure ViolationProofStatement (policy : AuthorityPolicy) : Prop where
  committedAction : GroundedAction
  committedStep : StepCommitment
  denied : ¬ Admissible policy committedAction.action

/--
The privacy-preserving incident statement we ultimately want zkperf to prove:
all disclosed prefix steps conform, while the committed crossing step does not.
-/
structure FirstCrossingProofStatement (policy : AuthorityPolicy) : Prop where
  crossing : FirstAuthorityCrossing policy
  prefixConforms :
    ∀ a ∈ crossing.admissiblePrefix, Admissible policy a
  crossingViolates : ¬ Admissible policy crossing.crossing.action

theorem firstCrossingProofStatement_sound
    (policy : AuthorityPolicy)
    (p : FirstCrossingProofStatement policy) :
    ¬ Admissible policy p.crossing.crossing.action :=
  p.crossingViolates

end Security.AgentAuthorityTrajectory
