import Integration.OggSSP2BUniqueInvariant24Range
import Integration.OggSSP2BCommonLaneKernelWeld

/-!
# Direct norm weld from the unique invariant 24-dimensional target range

This is the shortest image-level route to the 2B Tate exterior-square weld.
Once the actual residual norm coordinate is known to have rank 24 and invariant
image, a target-side uniqueness theorem for the Frobenius-square 24-submodule
forces equality of ranges.  No source quotient chart `M/ker(residual) ≃ V24`
is required.

The concrete quotient equivalence

  Sym^2(24) / range(Frobenius) ≃ Exterior^2(24)

then transports directly across the range equality.  Combined with the existing
common-lane cokernel cancellation, this yields the full Tate cokernel model.
-/

namespace Integration.OggSSP2BUniqueRangeNormWeld

namespace U := Integration.OggSSP2BUniqueInvariant24Range
namespace K := Integration.OggSSP2BCommonLaneKernelWeld

variable {R M C S V E : Type*}
  [DivisionRing R]
  [AddCommGroup M] [Module R M] [FiniteDimensional R M]
  [AddCommGroup C] [Module R C] [FiniteDimensional R C]
  [AddCommGroup S] [Module R S] [FiniteDimensional R S]
  [AddCommGroup V] [Module R V] [FiniteDimensional R V]
  [AddCommGroup E] [Module R E]

/-- Target uniqueness turns the actual residual image into the Frobenius image
literally. -/
theorem residual_range_eq_frobenius_from_unique_target
    (residual : M →ₗ[R] S)
    (frobenius : V →ₗ[R] S)
    {IsInvariant : Submodule R S → Prop}
    (unique : U.UniqueInvariant24SubmoduleReceipt frobenius IsInvariant)
    (hrank : Module.finrank R residual.range = 24)
    (hinvariant : IsInvariant residual.range) :
    residual.range = frobenius.range :=
  unique.range_eq_frobenius residual hrank hinvariant

/-- The residual cokernel is the exterior-square model as soon as the two image
submodules are forced equal. -/
noncomputable def residualCokernelEquivFromUniqueTarget
    (residual : M →ₗ[R] S)
    (frobenius : V →ₗ[R] S)
    {IsInvariant : Submodule R S → Prop}
    (unique : U.UniqueInvariant24SubmoduleReceipt frobenius IsInvariant)
    (hrank : Module.finrank R residual.range = 24)
    (hinvariant : IsInvariant residual.range)
    (frobeniusExterior : (S ⧸ frobenius.range) ≃ₗ[R] E) :
    (S ⧸ residual.range) ≃ₗ[R] E := by
  let hRange := residual_range_eq_frobenius_from_unique_target
    residual frobenius unique hrank hinvariant
  exact (residual.range.quotEquivOfEq frobenius.range hRange).trans
    frobeniusExterior

/-- Full Tate-cokernel equivalence after the already-existing common-lane
cancellation. -/
noncomputable def tateCokernelEquivFromUniqueTarget
    (kernelData : K.KernelWeldData (K := R) (M := M) (C := C) (S := S))
    (frobenius : V →ₗ[R] S)
    {IsInvariant : Submodule R S → Prop}
    (unique : U.UniqueInvariant24SubmoduleReceipt frobenius IsInvariant)
    (hrank : Module.finrank R kernelData.residualProjection.range = 24)
    (hinvariant : IsInvariant kernelData.residualProjection.range)
    (frobeniusExterior : (S ⧸ frobenius.range) ≃ₗ[R] E) :
    ((C × S) ⧸ kernelData.normRange) ≃ₗ[R] E :=
  kernelData.cokernelEquivResidualCokernel.trans
    (residualCokernelEquivFromUniqueTarget
      kernelData.residualProjection frobenius unique hrank hinvariant
      frobeniusExterior)

end Integration.OggSSP2BUniqueRangeNormWeld
