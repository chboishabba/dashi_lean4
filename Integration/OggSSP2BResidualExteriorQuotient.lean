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

/-- The residual quotient theorem is carried by a literal linear equivalence.
The provenance string records which concrete model supplies it (e.g. the
explicit Frobenius-square quotient of Sym2(24)). -/
structure ResidualExteriorReceipt
    (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S)) where
  exteriorModel : Type*
  exteriorAddCommGroup : AddCommGroup exteriorModel
  exteriorModule : Module K exteriorModel
  residualQuotientEquiv :
    (S ⧸ kernelData.residualRange) ≃ₗ[K] exteriorModel
  sourceProvenance : String

attribute [instance] ResidualExteriorReceipt.exteriorAddCommGroup
attribute [instance] ResidualExteriorReceipt.exteriorModule

namespace ResidualExteriorReceipt

variable
  (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S))
  (r : ResidualExteriorReceipt kernelData)

/-- Literal full Tate-cokernel equivalence obtained by composing the common-lane
cancellation theorem with the residual exterior quotient. -/
noncomputable def fullCokernelEquiv :
    ((C × S) ⧸ kernelData.normRange) ≃ₗ[K] r.exteriorModel :=
  Weld.tateCokernelEquivFromResidual kernelData r.residualQuotientEquiv

/-- Downstream users consume an actual equivalence, not a status flag. -/
theorem fullCokernelSameObjectPaid :
    Nonempty (((C × S) ⧸ kernelData.normRange) ≃ₗ[K] r.exteriorModel) :=
  ⟨r.fullCokernelEquiv kernelData⟩

end ResidualExteriorReceipt

/-- Simpler non-dependent packaging for callers that already fixed the exterior
model type `E`. -/
structure FixedResidualExteriorReceipt
    (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S)) where
  residualQuotientEquiv : (S ⧸ kernelData.residualRange) ≃ₗ[K] E
  sourceProvenance : String

namespace FixedResidualExteriorReceipt

variable
  (kernelData : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S))
  (r : FixedResidualExteriorReceipt (E := E) kernelData)

noncomputable def fullCokernelEquiv :
    ((C × S) ⧸ kernelData.normRange) ≃ₗ[K] E :=
  Weld.tateCokernelEquivFromResidual kernelData r.residualQuotientEquiv

end FixedResidualExteriorReceipt

end Integration.OggSSP2BResidualExteriorQuotient
