import Integration.OggSSP2BNormWeldCompiler

/-!
# Proof-bearing residual Frobenius quotient receipt

After literal cancellation of the common 98280 lane, the vertical weld is a
residual quotient problem.  This owner makes the remaining datum an actual
linear equivalence rather than a Boolean/status proposition:

  S / range(residual)  ≃  Exterior276.

When the residual map has already been identified with the unique nonzero
Frobenius 24 -> Sym2(24) map, this is exactly the concrete

  Sym2(24) / Frob(24)  ≃  wedge2(24)

quotient theorem.  The terminal compiler can then compose it with literal
common-lane cancellation to obtain the actual Tate-cokernel equivalence.
-/

namespace Integration.OggSSP2BResidualExteriorQuotient

namespace Weld := Integration.OggSSP2BNormWeldCompiler
namespace Kernel := Integration.OggSSP2BCommonLaneKernelWeld

variable {K M C S E : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup E] [Module K E]

/-- A literal residual-quotient equivalence to a fixed exterior model.  The
provenance string records the concrete realization (for this programme:
Sym2(24)/Frob(24) identified with the Co1 exterior-square / duad model). -/
structure ResidualExteriorReceipt
    (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S)) where
  residualQuotientEquiv : (S ⧸ kernelData.residualRange) ≃ₗ[K] E
  sourceProvenance : String

namespace ResidualExteriorReceipt

variable
  (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S))
  (r : ResidualExteriorReceipt (E := E) kernelData)

/-- Literal full Tate-cokernel equivalence obtained by composing common-lane
cancellation with the residual exterior quotient. -/
noncomputable def fullCokernelEquiv :
    ((C × S) ⧸ kernelData.normRange) ≃ₗ[K] E :=
  Weld.tateCokernelEquivFromResidual kernelData r.residualQuotientEquiv

/-- Downstream users consume an actual equivalence, not a status flag. -/
theorem fullCokernelSameObjectPaid :
    Nonempty (((C × S) ⧸ kernelData.normRange) ≃ₗ[K] E) :=
  ⟨r.fullCokernelEquiv kernelData⟩

end ResidualExteriorReceipt

end Integration.OggSSP2BResidualExteriorQuotient
