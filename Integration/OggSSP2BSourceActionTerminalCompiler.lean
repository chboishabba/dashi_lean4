import Integration.OggSSP2BOuterActionLastEquation
import Integration.OggSSP2BAutomaticFinalCompiler

/-!
# Terminal compiler from the last 2B action equation to the finished core

The current max-cut has reduced the B'+C' same-object problem to one equation on
the source-native Tate cokernel.  This owner removes the final packaging step:
once that equation produces the actual stable Completion10 quotient, the
existing selected-fibre transport and two-bit defect compilers immediately
produce `Final2BCoreRecognition`.

No new source claim is introduced here.  The remaining external/same-object
inputs remain exactly:
* formal source-native centralizer action and its induced cokernel operator;
* equality of that operator with the finite duad/M22:2 operator transported
  through the norm/exterior weld;
* the already-sourced full three-fibre Tate transport, instantiated formally;
* the two independent Mode5/2T provenance decisions.
-/

namespace Integration.OggSSP2BSourceActionTerminalCompiler

namespace O := Integration.OggSSP2BOuterActionLastEquation
namespace A := Integration.OggSSP2BAutomaticFinalCompiler
namespace K := Integration.OggSSP2BCommonLaneKernelWeld
namespace RQ := Integration.OggSSP2BResidualExteriorQuotient
namespace T := Integration.OggSSP2BStableCompletionModelTransport
namespace F := Integration.OggSSP2BFinalSameObjectCompiler
namespace L := Integration.OggSSP2BSelectedQ10TransportCompiler
namespace P := Integration.OggSSP2BDefectTwoBitProvenanceSelector

abbrev Scalar := F.Scalar

variable {M C S E Q : Type*}
  [AddCommGroup M] [Module Scalar M] [FiniteDimensional Scalar M]
  [AddCommGroup C] [Module Scalar C] [FiniteDimensional Scalar C]
  [AddCommGroup S] [Module Scalar S] [FiniteDimensional Scalar S]
  [AddCommGroup E] [Module Scalar E]
  [AddCommGroup Q] [Module Scalar Q]

/-- Strongest current terminal constructor for the original 2B core. -/
noncomputable def finalCoreFromLastActionEquation
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q)
    (hfinrank :
      Module.finrank Scalar ((C × S) ⧸ kernelData.normRange) = 276)
    (last : O.ActualCokernelOuterMatchesModelReceipt kernelData residual model)
    (lastEquationProvenance : String)
    (full : F.ActualThreeFibreTateTransportReceipt)
    (linear : L.LinearThreeFibreTransportReceipt full)
    (defectSource : P.TwoBitSourceReceipt)
    (finalProvenance : String) :
    F.Final2BCoreRecognition Q :=
  A.finalFromStableAndLinearTransport
    (O.actualStableCompletionFromLastEquation kernelData residual model hfinrank
      last lastEquationProvenance)
    full linear defectSource finalProvenance

/-- The terminal constructor retains the selected ten-dimensional quotient. -/
theorem finalCoreFromLastActionEquation_finrank_ten
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := S))
    (residual : RQ.ResidualExteriorReceipt (E := E) kernelData)
    (model : T.ModelStableCompletionReceipt E Q)
    (hfinrank :
      Module.finrank Scalar ((C × S) ⧸ kernelData.normRange) = 276)
    (last : O.ActualCokernelOuterMatchesModelReceipt kernelData residual model)
    (lastEquationProvenance : String)
    (full : F.ActualThreeFibreTateTransportReceipt)
    (linear : L.LinearThreeFibreTransportReceipt full)
    (defectSource : P.TwoBitSourceReceipt)
    (finalProvenance : String) :
    Module.finrank Scalar Q = 10 :=
  (finalCoreFromLastActionEquation kernelData residual model hfinrank last
    lastEquationProvenance full linear defectSource finalProvenance)
    .selected_Q10_has_finrank_ten

end Integration.OggSSP2BSourceActionTerminalCompiler
