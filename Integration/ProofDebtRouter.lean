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
next?".  The underlying `ProofStatus` is copied into the route unchanged.
-/

namespace Integration.ProofDebtRouter

open Integration.ProvenanceId
open Integration.Lineage

/-- A next-action class.  These are workflow actions, not proof statuses. -/
inductive Action
  /-- A proved/no-hypothesis receipt is available for downstream use. -/
  | consumeReceipt
  /-- A conditional compiler exists; prove the hypotheses it names. -/
  | dischargeHypotheses
  /-- A named mathematical/representation/payment obligation remains. -/
  | dischargePayment
  /-- Keep an explicit negative ledger flag negative until new evidence exists. -/
  | preserveFalsePinned
  /-- Keep a proved obstruction/counterexample as a no-go result. -/
  | preserveNoGo
  /-- Keep a source/document receipt as source evidence only. -/
  | preserveSourceReceipt
  /-- Keep pure indexing/hash/path information as bookkeeping only. -/
  | preserveBookkeeping
  /-- This row is conjectural/new mathematics rather than a transport receipt. -/
  | researchConjecture
  /-- A receipted Lean row names a carrier outside the canonical registry. -/
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

/-- Primary routing rule.

A row asserting Lean content must first satisfy canonical ownership.  This check
is fail-closed, but on the live ledger it is unreachable by
`SpineRegistry.ledger_carriers_registered`.  Once ownership is paid, routing is
exactly the existing `ProofStatus` classification. -/
def primaryAction (r : Row) : Action :=
  if carriesLeanReceipt r.status && !canonicalCarrierRegistered r then
    .repairCanonicalOwner
  else
    statusAction r.status

/-- Named downstream payments are orthogonal to the primary status/action.
Even a proved theorem may still have a downstream representation or consumer
payment, so this is deliberately a second coordinate. -/
def secondaryPaymentAction? (r : Row) : Option Action :=
  if r.payments.isEmpty then none else some .dischargePayment

/-- Executable routing view.  `status` is copied verbatim: routing cannot mutate
proof status by construction. -/
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

/-- The live lineage ledger cannot route a receipted row to canonical-owner
repair: canonical ownership is already proved globally by the registry. -/
theorem no_receipted_ledger_row_needs_registry_repair :
    ∀ r ∈ ledger, primaryAction r ≠ .repairCanonicalOwner := by
  decide

/-- A route is a view, not a promotion operation. -/
@[simp] theorem route_status (r : Row) : (route r).status = r.status := rfl

/-- Source/provenance acquisition status is not consulted by the router.  The
next action is determined by proof status, ownership and explicit payments. -/
theorem primaryAction_ignores_provenance (r : Row) (p : List Ident) :
    primaryAction { r with provenance := p } = primaryAction r := by
  rfl

/-- The same is true of secondary payment routing. -/
theorem secondaryPaymentAction_ignores_provenance (r : Row) (p : List Ident) :
    secondaryPaymentAction? { r with provenance := p } = secondaryPaymentAction? r := by
  rfl

end Integration.ProofDebtRouter
