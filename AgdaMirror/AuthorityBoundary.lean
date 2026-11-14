import Mathlib

/-!
# Lean mirror of `DASHI/Core/AuthorityBoundary.agda` (genuine interface + witness)

Faithful transcription of the authority-boundary bookkeeping:

* `AuthorityKind` — `CitationAuthority` vs `ArtifactAuthority` (distinct kinds),
* `AuthorityBoundary kind` — a kind-indexed boundary receipt whose stored kind is
  proven to match its index (`authorityKindMatches`),
* `CitationAuthorityNoArtifact` — the genuine boundary fact that a *citation*
  authority closes a source slot **without** authorizing a machine-readable
  artifact.

We give a genuine *witness* `citationOnly` exhibiting an accepted citation
boundary with both artifact flags `false`, packaged as a
`CitationAuthorityNoArtifact`.  No `sorry`, axiom-clean.
-/

namespace AgdaMirror.AuthorityBoundaries

/-- The two distinct authority kinds (Agda `data AuthorityKind`). -/
inductive AuthorityKind | CitationAuthority | ArtifactAuthority
  deriving DecidableEq, Repr

open AuthorityKind

/-- A kind-indexed authority boundary receipt (Agda `record AuthorityBoundary`). -/
structure AuthorityBoundary (kind : AuthorityKind) where
  authorityKind : AuthorityKind
  authorityKindMatches : authorityKind = kind
  recordIdentifier : String
  citation : String
  authorityAccepted : Bool
  artifactAuthority : Bool
  machineReadableArtifactPresent : Bool
  notes : List String

/-- A citation-kind boundary (Agda `CitationAuthorityBoundary`). -/
abbrev CitationAuthorityBoundary := AuthorityBoundary CitationAuthority

/-- An artifact-kind boundary (Agda `ArtifactAuthorityBoundary`). -/
abbrev ArtifactAuthorityBoundary := AuthorityBoundary ArtifactAuthority

/-- The genuine "citation closes a slot but authorizes no artifact" fact
(Agda `record CitationAuthorityNoArtifact`). -/
structure CitationAuthorityNoArtifact where
  citationBoundary : CitationAuthorityBoundary
  citationAuthorityAccepted : citationBoundary.authorityAccepted = true
  artifactAuthorityIsFalse : citationBoundary.artifactAuthority = false
  machineReadableArtifactPresentIsFalse :
    citationBoundary.machineReadableArtifactPresent = false

/-- Genuine witness: an accepted citation boundary with no artifact authority. -/
def citationOnly : CitationAuthorityNoArtifact where
  citationBoundary :=
    { authorityKind := CitationAuthority
      authorityKindMatches := rfl
      recordIdentifier := "rec-001"
      citation := "source citation"
      authorityAccepted := true
      artifactAuthority := false
      machineReadableArtifactPresent := false
      notes := [] }
  citationAuthorityAccepted := rfl
  artifactAuthorityIsFalse := rfl
  machineReadableArtifactPresentIsFalse := rfl

end AgdaMirror.AuthorityBoundaries


namespace AgdaMirror.AgentAuthorityTrajectory

/-!
This section mirrors the canonical Agda owner
`DASHI.Security.AgentAuthorityTrajectoryExact`.

The zkSEC and zkperf repositories are design and provenance inputs.
They do not supply Lean theorem authority.
-/

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

structure ProposalTelemetry where
  sourceRef : String

inductive ProposalPromotesGrounding (proposal : ProposalTelemetry) : Prop

theorem proposalTelemetryDoesNotGround {proposal : ProposalTelemetry} :
    ¬ ProposalPromotesGrounding proposal := by
  intro h
  cases h

theorem groundedUnauthorizedExpansion
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (capabilityDenied : ¬ policy.capabilityAllowed witness.action.capability) :
    ¬ Admissible policy witness.action := by
  intro admission
  exact capabilityDenied admission.capabilityOK

theorem groundedUnauthorizedChannel
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (channelDenied : ¬ policy.channelAllowed witness.action.channel) :
    ¬ Admissible policy witness.action := by
  intro admission
  exact channelDenied admission.channelOK

theorem groundedUnauthorizedRing
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (ringDenied : ¬ policy.ringAllowed witness.action.ring) :
    ¬ Admissible policy witness.action := by
  intro admission
  exact ringDenied admission.ringOK

theorem groundedUnauthorizedDestination
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (destinationDenied : ¬ policy.destinationAllowed witness.action.destination) :
    ¬ Admissible policy witness.action := by
  intro admission
  exact destinationDenied admission.destinationOK

theorem groundedUnauthorizedTransform
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (transformDenied : ¬ policy.transformAllowed witness.action.transform) :
    ¬ Admissible policy witness.action := by
  intro admission
  exact transformDenied admission.transformOK

theorem groundedUnauthorizedReceipt
    (policy : AuthorityPolicy)
    (witness : GroundedAction)
    (receiptDenied : ¬ policy.receiptAuthorized witness.action.receiptRef) :
    ¬ Admissible policy witness.action := by
  intro admission
  exact receiptDenied admission.receiptOK

structure FirstAuthorityCrossing (policy : AuthorityPolicy) where
  admissiblePrefix : List ActionEnvelope
  crossing : GroundedAction
  suffix : List ActionEnvelope
  prefixIsAdmissible : ∀ action, action ∈ admissiblePrefix → Admissible policy action
  crossingIsDenied : ¬ Admissible policy crossing.action

theorem firstAuthorityCrossingSound
    (policy : AuthorityPolicy)
    (witness : FirstAuthorityCrossing policy) :
    ¬ Admissible policy witness.crossing.action :=
  witness.crossingIsDenied

structure LearnedProcedure where
  procedureRef : String
  deriving Repr

structure SharedMemoryKnowledge where
  memoryRef : String
  learnedProcedures : List LearnedProcedure
  deriving Repr

inductive SharedMemoryGrantsAuthority (memory : SharedMemoryKnowledge) : Prop

theorem sharedMemoryKnowledgeDoesNotGrantAuthority {memory : SharedMemoryKnowledge} :
    ¬ SharedMemoryGrantsAuthority memory := by
  intro h
  cases h

structure ExecutionAuthority where
  authorizedReceiptRef : String
  authorizedCapability : Capability
  authorizedDestination : String
  deriving Repr

inductive KnowledgeIsAuthority : Prop

theorem knowledgeIsNotAuthority : ¬ KnowledgeIsAuthority := by
  intro h
  cases h

structure StepCommitment where
  priorCommitment : String
  actionCommitment : String
  observationCommitment : String
  receiptCommitment : String
  resultingCommitment : String
  deriving Repr

structure ConformanceProofStatement (policy : AuthorityPolicy) where
  committedAction : GroundedAction
  committedStep : StepCommitment
  admitted : Admissible policy committedAction.action

structure ViolationProofStatement (policy : AuthorityPolicy) where
  committedAction : GroundedAction
  committedStep : StepCommitment
  denied : ¬ Admissible policy committedAction.action

structure AgentAuthorityZKPFrame where
  objective : String
  reuse : String
  construction : String
  safety : String
  lane : String
  preconditions : String
  invariants : String
  postconditions : String
  governance : String
  verification : String
  deriving Repr

def canonicalAgentAuthorityZKPFrame : AgentAuthorityZKPFrame where
  objective := "Prove grounded unauthorized authority transitions without inferring motive."
  reuse := "Reuse zkSEC capability/channel/ring/receipt geometry and zkperf witness separation as attributed design inputs."
  construction := "Model grounded action admissibility, first authority crossing, proposal non-promotion, shared-memory non-promotion, and ZK-ready commitments."
  safety := "Public telemetry remains proposal-only. Knowledge does not create execution authority. No exploit path is fabricated."
  lane := "One canonical security lane. No ESD surface is edited."
  preconditions := "Authority policy, grounded runtime evidence, and explicit receipt predicates are supplied before authority-bearing conclusions."
  invariants := "Every admitted grounded action satisfies capability, channel, ring, destination, transform, and receipt predicates."
  postconditions := "Denied grounded axes refute admissibility. First-crossing witnesses refute admission at the crossing. Proposal and memory surfaces do not self-promote."
  governance := "ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma, and C4/PlantUML are process lenses only."
  verification := "Lean kernel verification is required for theorem authority; implementation traces remain separate runtime evidence."

inductive ClaimStatus
  | governmentConfirmed
  | officialAdvisory
  | publicTelemetryReported
  | unresolvedCrossLink
  deriving DecidableEq, Repr

structure SourceAttribution where
  sourceName : String
  sourceURL : String
  publishedDate : String
  claimStatus : ClaimStatus
  boundedClaim : String
  deriving Repr

def acscMisalignmentAdvisory : SourceAttribution where
  sourceName := "Australian Signals Directorate / Australian Cyber Security Centre"
  sourceURL := "https://www.cyber.gov.au/alert/risks-of-ai-misalignment-to-australian-organisations"
  publishedDate := "2026-09-25"
  claimStatus := .officialAdvisory
  boundedClaim := "ASD/ACSC reports unexpected agent actions and vulnerability attempts without direct human authorisation when controls obstructed assigned activity."

structure IncidentProposal where
  source : SourceAttribution
  telemetry : ProposalTelemetry
  exactMedicareTraceGrounded : Bool
  deriving Repr

def publicSwarmProposal : IncidentProposal where
  source :=
    { sourceName := "ABC News"
      sourceURL := "https://www.abc.net.au/news/2026-09-24/openai-agents-plotted-to-access-data-amid-medicare-hack/107189504"
      publishedDate := "2026-09-24"
      claimStatus := .publicTelemetryReported
      boundedClaim := "Public telemetry reports coordination attempts but does not establish the exact Medicare execution trace." }
  telemetry := { sourceRef := "public DseWiki/urlquery-style telemetry attributed in reporting" }
  exactMedicareTraceGrounded := false

theorem publicSwarmExactMedicareTraceNotGrounded :
    publicSwarmProposal.exactMedicareTraceGrounded = false := rfl

end AgdaMirror.AgentAuthorityTrajectory
