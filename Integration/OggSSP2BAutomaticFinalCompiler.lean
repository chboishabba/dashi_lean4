import Integration.OggSSP2BNormToStableCompletion
import Integration.OggSSP2BSelectedQ10TransportCompiler
import Integration.OggSSP2BFinalSameObjectCompiler

/-!
# Automatic terminal compiler for the 2B core

At this point the remaining mathematical inputs are concrete same-object maps,
not architectural receipts.  This owner removes the last packaging layers:

* a stable actual-Tate Completion10 quotient;
* a full three-fibre Tate cycle plus linear refinements of its source maps;
* the two sourced Mode5/2T orientation bits

compile directly to `Final2BCoreRecognition`.

A stronger constructor starts one step earlier from the equivariant norm/
exterior vertical weld; it first generates the actual Tate stable quotient,
then generates selected fibre transport, then closes the final core.
-/

namespace Integration.OggSSP2BAutomaticFinalCompiler

namespace A := Integration.OggSSP2BActualStableCompletionSubquotient
namespace F := Integration.OggSSP2BFinalSameObjectCompiler
namespace L := Integration.OggSSP2BSelectedQ10TransportCompiler
namespace N := Integration.OggSSP2BNormToStableCompletion
namespace P := Integration.OggSSP2BDefectTwoBitProvenanceSelector
namespace RQ := Integration.OggSSP2BResidualExteriorQuotient
namespace K := Integration.OggSSP2BCommonLaneKernelWeld
namespace T := Integration.OggSSP2BStableCompletionModelTransport

abbrev Scalar := F.Scalar

variable {Q : Type*} [AddCommGroup Q] [Module Scalar Q]

/-- Once B'+C' is on the actual Tate quotient, A' selected transport is no
longer a separate receipt if the full fibre maps are supplied linearly. -/
noncomputable def finalFromStableAndLinearTransport
    (stable : A.StableCompletionSubquotientReceipt Q)
    (full : F.ActualThreeFibreTateTransportReceipt)
    (linear : L.LinearThreeFibreTransportReceipt full)
    (defectSource : P.TwoBitSourceReceipt)
    (sourceProvenance : String) :
    F.Final2BCoreRecognition Q := by
  let completion := stable.toRecognition
  let selected :=
    linear.compileSelectedTransport (recognition := completion)
  exact F.Final2BCoreRecognition.fromTwoBitDefectProvenance
    completion full selected defectSource sourceProvenance

/-- The generated final core retains the actual selected ten-dimensional
quotient. -/
theorem finalFromStable_finrank_ten
    (stable : A.StableCompletionSubquotientReceipt Q)
    (full : F.ActualThreeFibreTateTransportReceipt)
    (linear : L.LinearThreeFibreTransportReceipt full)
    (defectSource : P.TwoBitSourceReceipt)
    (sourceProvenance : String) :
    Module.finrank Scalar Q = 10 :=
  (finalFromStableAndLinearTransport stable full linear defectSource
    sourceProvenance).selected_Q10_has_finrank_ten

/-- Strongest terminal constructor: actual norm-cokernel/exterior equivariance
produces B'+C'; linear fibre refinements produce selected A'; two source bits
produce D.  No manual stable-subquotient or selected-transport receipt remains. -/
noncomputable def finalFromVerticalWeld
    {M C S E : Type*}
    [AddCommGroup M] [Module Scalar M] [FiniteDimensional Scalar M]
    [AddCommGroup C] [Module Scalar C] [FiniteDimensional Scalar C]
    [AddCommGroup S] [Module Scalar S] [FiniteDimensional Scalar S]
    [AddCommGroup E] [Module Scalar E]
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q)
    (vertical : N.VerticalWeldReceipt kernelData residual model)
    (full : F.ActualThreeFibreTateTransportReceipt)
    (linear : L.LinearThreeFibreTransportReceipt full)
    (defectSource : P.TwoBitSourceReceipt)
    (sourceProvenance : String) :
    F.Final2BCoreRecognition Q :=
  finalFromStableAndLinearTransport
    (vertical.toActualStableCompletion kernelData residual model)
    full linear defectSource sourceProvenance

/-- C' in the terminal vertical-weld path is still the sourced outer action on
the same actual quotient, not a reconstructed finite-model operator. -/
theorem finalFromVerticalWeld_completion
    {M C S E : Type*}
    [AddCommGroup M] [Module Scalar M] [FiniteDimensional Scalar M]
    [AddCommGroup C] [Module Scalar C] [FiniteDimensional Scalar C]
    [AddCommGroup S] [Module Scalar S] [FiniteDimensional Scalar S]
    [AddCommGroup E] [Module Scalar E]
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q)
    (vertical : N.VerticalWeldReceipt kernelData residual model)
    (full : F.ActualThreeFibreTateTransportReceipt)
    (linear : L.LinearThreeFibreTransportReceipt full)
    (defectSource : P.TwoBitSourceReceipt)
    (sourceProvenance : String)
    (q : Q) :
    let result := finalFromVerticalWeld kernelData residual model vertical
      full linear defectSource sourceProvenance
    result.completion.completion.chart
        (result.completion.completion.binaryOperator q)
      = Integration.OggSSP2BRevisedCompletionRecognition.completionFlipLinear
          (result.completion.completion.chart q) := by
  simpa using
    (finalFromVerticalWeld kernelData residual model vertical full linear
      defectSource sourceProvenance).completion_action_intertwines q

end Integration.OggSSP2BAutomaticFinalCompiler
