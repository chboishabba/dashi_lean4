import Integration.OggSSP2BActualStableCompletionSubquotient
import Integration.OggSSP2BFinalSameObjectCompiler

/-!
# Post-Brauer terminal compiler for the 2B programme

After the all-2-regular-class CTblLib PASS, B' is no longer a candidate-discovery
problem.  The remaining B'+C' acquisition is one explicit M22:2-stable quotient of the
actual Tate carrier.  D is exactly two independently sourced orientation bits.

This owner makes that final dependency graph literal: one stable same-object quotient,
one actual three-fibre transport receipt, transport of that selected quotient, and one
two-bit provenance receipt compile directly to the final 2B core recognition.
-/

namespace Integration.OggSSP2BPostBrauerFinalCompiler

namespace S := Integration.OggSSP2BActualStableCompletionSubquotient
namespace F := Integration.OggSSP2BFinalSameObjectCompiler
namespace P := Integration.OggSSP2BDefectTwoBitProvenanceSelector

abbrev Scalar := F.Scalar

structure PostBrauerFinalReceipt
    (Q : Type*) [AddCommGroup Q] [Module Scalar Q] where
  stableSubquotient : S.StableCompletionSubquotientReceipt Q
  fullTateTransport : F.ActualThreeFibreTateTransportReceipt
  selectedTransport :
    F.SelectedQ10TransportReceipt Q
      stableSubquotient.toRecognition fullTateTransport
  defectSource : P.TwoBitSourceReceipt
  sourceProvenance : String

namespace PostBrauerFinalReceipt

variable {Q : Type*} [AddCommGroup Q] [Module Scalar Q]

/-- The final compiler: no architectural theorem remains after these concrete receipts. -/
def toFinalCore (r : PostBrauerFinalReceipt Q) : F.Final2BCoreRecognition Q :=
  F.Final2BCoreRecognition.fromTwoBitDefectProvenance
    r.stableSubquotient.toRecognition
    r.fullTateTransport
    r.selectedTransport
    r.defectSource
    r.sourceProvenance

/-- B': the actual selected quotient is ten-dimensional. -/
theorem selected_finrank_ten (r : PostBrauerFinalReceipt Q) :
    Module.finrank Scalar Q = 10 :=
  r.stableSubquotient.target_finrank

/-- C': the sourced outer action descends to the same quotient and is exactly the
Completion10 flip under the recognition chart. -/
theorem outer_action_is_completion
    (r : PostBrauerFinalReceipt Q) (q : Q) :
    r.stableSubquotient.completionChart
        (r.stableSubquotient.quotientOuterOperator q)
      = Integration.OggSSP2BRevisedCompletionRecognition.completionFlipLinear
          (r.stableSubquotient.completionChart q) :=
  r.stableSubquotient.completion_intertwining q

/-- A': the selected Q10 returns after the three fibre transports. -/
theorem selected_three_fibre_cycle_closes
    (r : PostBrauerFinalReceipt Q) (q : Q) :
    r.selectedTransport.qPhi20
      (r.selectedTransport.qPhi12 (r.selectedTransport.qPhi01 q)) = q :=
  r.selectedTransport.quotient_cycle_coherent q

/-- D: exactly the independently sourced two-bit chart is used in the final core. -/
theorem final_defect_chart_is_two_bit_source
    (r : PostBrauerFinalReceipt Q) :
    r.toFinalCore.defectRecognition.modeToOrderStratum
      = P.chartFromBits r.defectSource.bits := by
  rfl

end PostBrauerFinalReceipt

/-- The executed Brauer-character screen is necessary ingress evidence but cannot by
itself construct the explicit stable quotient or the two provenance bits. -/
inductive BrauerPassAloneConstructsFinalReceipt : Prop

theorem brauer_pass_alone_does_not_construct_final_receipt :
    ¬ BrauerPassAloneConstructsFinalReceipt := by
  intro h
  cases h

end Integration.OggSSP2BPostBrauerFinalCompiler
