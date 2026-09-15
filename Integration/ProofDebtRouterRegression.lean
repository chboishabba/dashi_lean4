import Integration.LineageLedger
import Integration.CanonicalSpineRegistry
import Integration.ProofDebtRouter

/-!
Regression surface for the TOE proof-debt router.

This file is intentionally written before `Integration.ProofDebtRouter` exists.
It requires the router to remain a derived action view over the existing lineage
status and canonical registry rather than introducing another proof-status enum.
-/

namespace Integration.ProofDebtRouterRegression

open Integration.ProvenanceId
open Integration.Lineage
open Integration.ProofDebtRouter

private def baseRow (status : ProofStatus) (payments : List String := []) : Row :=
  { lane := .provenanceMeta
  , structureKey := "identifier-authority-firewall"
  , agdaOwner := "DASHI.Core.AttributedSourceCore"
  , leanCarrier := "Integration.ProvenanceIdentifier"
  , leanAdapter := ""
  , leanConsumer := "Integration.LineageLedger"
  , hypotheses := []
  , status := status
  , provenance := []
  , supersedes := ""
  , payments := payments }

example : primaryAction (baseRow (.provedTheorem "T")) = .consumeReceipt := by decide

example : primaryAction (baseRow (.conditionalCompiler "T" ["H"])) = .dischargeHypotheses := by decide

example : primaryAction (baseRow (.openPayment "P")) = .dischargePayment := by decide

example : primaryAction (baseRow (.falsePinned "flag = false")) = .preserveFalsePinned := by decide

example : primaryAction (baseRow (.noGo "N")) = .preserveNoGo := by decide

example : primaryAction (baseRow (.sourceReceipt ⟨.doi, "10.1/x"⟩)) = .preserveSourceReceipt := by decide

example : primaryAction (baseRow .bookkeeping) = .preserveBookkeeping := by decide

example : primaryAction (baseRow (.conjectural "C")) = .researchConjecture := by decide

example : secondaryPaymentAction? (baseRow (.provedTheorem "T") ["downstream seam"]) =
    some .dischargePayment := by decide

/-- The live TOE ledger may not route a receipted row to registry repair: that
would contradict the already-proved canonical-owner invariant. -/
theorem live_ledger_has_no_registry_repair :
    ∀ r ∈ ledger, primaryAction r ≠ .repairCanonicalOwner :=
  no_receipted_ledger_row_needs_registry_repair

/-- Routing is a view: it does not mutate or promote the underlying status. -/
theorem routing_preserves_status (r : Row) : (route r).status = r.status := rfl

end Integration.ProofDebtRouterRegression
