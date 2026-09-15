import Integration.LineageLedger
import Integration.CanonicalSpineRegistry
import Integration.ProofDebtRouter

/-!
Regression surface for the TOE proof-debt router.

The router is a derived action view over the existing lineage status and
canonical registry rather than a new proof-status enum. Worker packets must be
lossless projections of lineage rows: routing may classify work, but it may not
rewrite owner, consumer, hypotheses, payments, provenance, supersession, or
evidence status.
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
example : secondaryPaymentAction? (baseRow (.provedTheorem "T") ["downstream seam"]) = some .dischargePayment := by decide

theorem live_ledger_has_no_registry_repair :
    ∀ r ∈ ledger, primaryAction r ≠ .repairCanonicalOwner :=
  no_receipted_ledger_row_needs_registry_repair

theorem routing_preserves_status (r : Row) : (route r).status = r.status := rfl

private def conditionalRow : Row :=
  { lane := .chemistry
  , structureKey := "reachability-closure"
  , agdaOwner := "DASHI.Chemistry.SomeOwner"
  , leanCarrier := "Integration.ReachabilityBarrier"
  , leanAdapter := "Welds.ReachabilityCarrier.ofStep"
  , leanConsumer := "Integration.ChemistryReachability.reachB"
  , hypotheses := ["finite vertex type", "Bool-valued step relation"]
  , status := .conditionalCompiler "T" ["finite vertex type", "Bool-valued step relation"]
  , provenance := [⟨.agdaModule, "DASHI.Chemistry.SomeOwner"⟩]
  , supersedes := "older-local-copy"
  , payments := ["physical carrier identification"] }

private def packet := workerPacket conditionalRow

example : packet.lane = .chemistry := rfl
example : packet.structureKey = "reachability-closure" := rfl
example : packet.agdaOwner = "DASHI.Chemistry.SomeOwner" := rfl
example : packet.leanCarrier = "Integration.ReachabilityBarrier" := rfl
example : packet.leanAdapter = "Welds.ReachabilityCarrier.ofStep" := rfl
example : packet.leanConsumer = "Integration.ChemistryReachability.reachB" := rfl
example : packet.hypotheses = ["finite vertex type", "Bool-valued step relation"] := rfl
example : packet.payments = ["physical carrier identification"] := rfl
example : packet.provenance = [⟨.agdaModule, "DASHI.Chemistry.SomeOwner"⟩] := rfl
example : packet.supersedes = "older-local-copy" := rfl
example : packet.status = conditionalRow.status := rfl
example : packet.primary = .dischargeHypotheses := by decide
example : packet.secondary = some .dischargePayment := by decide
example : packet.toRow = conditionalRow := rfl

theorem worker_packets_cover_live_ledger : workerPackets.length = ledger.length :=
  workerPackets_length

theorem worker_packet_roundtrip (r : Row) : (workerPacket r).toRow = r :=
  workerPacket_toRow r

end Integration.ProofDebtRouterRegression
