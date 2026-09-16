import Integration.CanonicalSpineRegistry

/-!
# TOE proof-debt action router

This module is a **derived view** over the existing Lean↔Agda lineage ledger.
It does not add another proof-status lattice and it does not promote anything.

The inputs already exist:

* `Integration.ProvenanceId.ProofStatus` says what kind of claim a row carries;
* `Integration.Lineage.Row.payments` records named downstream debt;
* `Integration.SpineRegistry` says which receipted Lean carriers have canonical
  ownership.

The router answers only the operational question "what kind of work is licensed
next?". The underlying `ProofStatus` is copied into the route unchanged.
-/

namespace Integration.ProofDebtRouter

open Integration.ProvenanceId
open Integration.Lineage

/-- A next-action class. These are workflow actions, not proof statuses. -/
inductive Action
  | consumeReceipt
  | dischargeHypotheses
  | dischargePayment
  | preserveFalsePinned
  | preserveNoGo
  | preserveSourceReceipt
  | preserveBookkeeping
  | researchConjecture
  | repairCanonicalOwner
  deriving DecidableEq, Repr

/-- Is the row's named Lean carrier already owned by the canonical registry? -/
def canonicalCarrierRegistered (r : Row) : Bool :=
  decide (r.leanCarrier ∈ Integration.SpineRegistry.carriers)

/-- The action dictated by the row's proof status, before secondary payments. -/
def statusAction : ProofStatus → Action
  | .provedTheorem _ => .consumeReceipt
  | .conditionalCompiler _ _ => .dischargeHypotheses
  | .openPayment _ => .dischargePayment
  | .falsePinned _ => .preserveFalsePinned
  | .noGo _ => .preserveNoGo
  | .sourceReceipt _ => .preserveSourceReceipt
  | .bookkeeping => .preserveBookkeeping
  | .conjectural _ => .researchConjecture

/-- A receipted Lean row first has to name a canonical owner; otherwise route by
its existing proof status. This is a fail-closed ownership check, not promotion. -/
def primaryAction (r : Row) : Action :=
  if carriesLeanReceipt r.status && !canonicalCarrierRegistered r then
    .repairCanonicalOwner
  else
    statusAction r.status

/-- Named downstream payments are orthogonal to the primary status/action. -/
def secondaryPaymentAction? (r : Row) : Option Action :=
  if r.payments.isEmpty then none else some .dischargePayment

/-- Executable routing view. `status` is copied verbatim. -/
structure Route where
  status : ProofStatus
  primary : Action
  secondary : Option Action
  canonicalOwnerPaid : Bool
  deriving DecidableEq, Repr

/-- Route one lineage row without changing its evidentiary status. -/
def route (r : Row) : Route :=
  { status := r.status
  , primary := primaryAction r
  , secondary := secondaryPaymentAction? r
  , canonicalOwnerPaid := canonicalCarrierRegistered r }

/-- The live lineage ledger cannot route any row to canonical-owner repair. For
receipted rows this follows from the canonical registry invariant; all other
statuses fail the ownership guard before that branch can be selected. -/
theorem no_receipted_ledger_row_needs_registry_repair :
    ∀ r ∈ ledger, primaryAction r ≠ .repairCanonicalOwner := by
  decide

@[simp] theorem route_status (r : Row) : (route r).status = r.status := rfl

/-- Provenance is not an input to routing. -/
theorem primaryAction_ignores_provenance (r : Row) (p : List Ident) :
    primaryAction { r with provenance := p } = primaryAction r := by
  rfl

theorem secondaryPaymentAction_ignores_provenance (r : Row) (p : List Ident) :
    secondaryPaymentAction? { r with provenance := p } = secondaryPaymentAction? r := by
  rfl

/-! ## Lossless worker handoff -/

/-- A worker-facing packet carries the complete lineage row plus derived routing
coordinates. The row fields are deliberately copied rather than summarized so a
proof worker never has to infer owner, consumer, hypotheses, provenance, or
payments from prose. -/
structure WorkerPacket where
  lane : Lane
  structureKey : String
  agdaOwner : String
  leanCarrier : String
  leanAdapter : String
  leanConsumer : String
  hypotheses : List String
  status : ProofStatus
  provenance : List Ident
  supersedes : String
  payments : List String
  primary : Action
  secondary : Option Action
  canonicalOwnerPaid : Bool
  deriving DecidableEq, Repr

/-- Recover the original lineage row exactly; routing coordinates are metadata
outside the evidentiary row. -/
def WorkerPacket.toRow (p : WorkerPacket) : Row :=
  { lane := p.lane
  , structureKey := p.structureKey
  , agdaOwner := p.agdaOwner
  , leanCarrier := p.leanCarrier
  , leanAdapter := p.leanAdapter
  , leanConsumer := p.leanConsumer
  , hypotheses := p.hypotheses
  , status := p.status
  , provenance := p.provenance
  , supersedes := p.supersedes
  , payments := p.payments }

/-- Produce one lossless worker packet from one lineage row. -/
def workerPacket (r : Row) : WorkerPacket :=
  { lane := r.lane
  , structureKey := r.structureKey
  , agdaOwner := r.agdaOwner
  , leanCarrier := r.leanCarrier
  , leanAdapter := r.leanAdapter
  , leanConsumer := r.leanConsumer
  , hypotheses := r.hypotheses
  , status := r.status
  , provenance := r.provenance
  , supersedes := r.supersedes
  , payments := r.payments
  , primary := primaryAction r
  , secondary := secondaryPaymentAction? r
  , canonicalOwnerPaid := canonicalCarrierRegistered r }

@[simp] theorem workerPacket_toRow (r : Row) : (workerPacket r).toRow = r := rfl

/-- Executable worker view of the complete live lineage ledger. -/
def workerPackets : List WorkerPacket := ledger.map workerPacket

@[simp] theorem workerPackets_length : workerPackets.length = ledger.length := by
  simp [workerPackets]

end Integration.ProofDebtRouter
