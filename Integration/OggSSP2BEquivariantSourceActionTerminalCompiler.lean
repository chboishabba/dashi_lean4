import Integration.OggSSP2BEquivariantWeldKillsLastEquation
import Integration.OggSSP2BSourceActionTerminalCompiler

/-!
# Terminal 2B compiler from an equivariant same-object weld

The previous terminal compiler consumed an explicit equality

  g_actual = e⁻¹ ∘ g_model ∘ e.

`OggSSP2BEquivariantWeldKillsLastEquation` proves that this equality is already
forced by equivariance of the literal Tate/exterior equivalence.  This owner
therefore exposes the stronger public constructor: callers provide the actual
source-native outer operator and an intertwining theorem for the same-object
weld; the old equality receipt is generated internally.

Attribution remains unchanged: external sources own the Moonshine/centralizer
action and finite ATLAS model; DASHI owns only the compiler reduction.
-/

namespace Integration.OggSSP2BEquivariantSourceActionTerminalCompiler

namespace E := Integration.OggSSP2BEquivariantWeldKillsLastEquation
namespace S := Integration.OggSSP2BSourceActionTerminalCompiler
namespace K := Integration.OggSSP2BCommonLaneKernelWeld
namespace RQ := Integration.OggSSP2BResidualExteriorQuotient
namespace T := Integration.OggSSP2BStableCompletionModelTransport
namespace F := Integration.OggSSP2BFinalSameObjectCompiler
namespace L := Integration.OggSSP2BSelectedQ10TransportCompiler
namespace P := Integration.OggSSP2BDefectTwoBitProvenanceSelector

abbrev Scalar := F.Scalar

/-- Machine-readable status bit: after this compiler, the literal conjugation
equality is no longer an independent acquisition leaf. -/
def outerActionEqualityIsCompilerOutput : Bool := true

variable {M C R X Q : Type*}
  [AddCommGroup M] [Module Scalar M] [FiniteDimensional Scalar M]
  [AddCommGroup C] [Module Scalar C] [FiniteDimensional Scalar C]
  [AddCommGroup R] [Module Scalar R] [FiniteDimensional Scalar R]
  [AddCommGroup X] [Module Scalar X]
  [AddCommGroup Q] [Module Scalar Q]

/-- Strongest current terminal constructor: equivariance of the actual
Tate/exterior weld produces the old last-equation receipt internally and then
feeds the existing automatic final compiler. -/
noncomputable def finalCoreFromEquivariantWeld
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := R))
    (residual : RQ.ResidualExteriorReceipt (E := X) kernelData)
    (model : T.ModelStableCompletionReceipt X Q)
    (hfinrank : Module.finrank Scalar ((C × R) ⧸ kernelData.normRange) = 276)
    (actualOuter :
      ((C × R) ⧸ kernelData.normRange) →ₗ[Scalar]
        ((C × R) ⧸ kernelData.normRange))
    (hintertwines : ∀ z,
      residual.fullCokernelEquiv kernelData (actualOuter z) =
        model.outerOperator (residual.fullCokernelEquiv kernelData z))
    (actualOuterOperatorSourced : Bool)
    (actionProvenance : String)
    (full : F.ActualThreeFibreTateTransportReceipt)
    (linear : L.LinearThreeFibreTransportReceipt full)
    (defectSource : P.TwoBitSourceReceipt)
    (finalProvenance : String) :
    F.Final2BCoreRecognition Q :=
  S.finalCoreFromLastActionEquation
    kernelData residual model hfinrank
    (E.lastEquationFromEquivariance kernelData residual model actualOuter
      hintertwines actualOuterOperatorSourced actionProvenance)
    actionProvenance full linear defectSource finalProvenance

/-- The selected quotient remains ten-dimensional in the equivariant API. -/
theorem finalCoreFromEquivariantWeld_finrank_ten
    (kernelData : K.KernelWeldData
      (K := Scalar) (M := M) (C := C) (S := R))
    (residual : RQ.ResidualExteriorReceipt (E := X) kernelData)
    (model : T.ModelStableCompletionReceipt X Q)
    (hfinrank : Module.finrank Scalar ((C × R) ⧸ kernelData.normRange) = 276)
    (actualOuter :
      ((C × R) ⧸ kernelData.normRange) →ₗ[Scalar]
        ((C × R) ⧸ kernelData.normRange))
    (hintertwines : ∀ z,
      residual.fullCokernelEquiv kernelData (actualOuter z) =
        model.outerOperator (residual.fullCokernelEquiv kernelData z))
    (actualOuterOperatorSourced : Bool)
    (actionProvenance : String)
    (full : F.ActualThreeFibreTateTransportReceipt)
    (linear : L.LinearThreeFibreTransportReceipt full)
    (defectSource : P.TwoBitSourceReceipt)
    (finalProvenance : String) :
    Module.finrank Scalar Q = 10 :=
  (finalCoreFromEquivariantWeld kernelData residual model hfinrank actualOuter
    hintertwines actualOuterOperatorSourced actionProvenance full linear
    defectSource finalProvenance).selected_Q10_has_finrank_ten

end Integration.OggSSP2BEquivariantSourceActionTerminalCompiler
