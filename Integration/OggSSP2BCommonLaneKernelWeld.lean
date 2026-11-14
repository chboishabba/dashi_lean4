import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Integration.OggSSP2BTateCokernelRankRigidity

/-!
# Common 98280 lane is forced by the residual-kernel geometry

The source-native norm map is injective and lands in a direct sum

  C_common(98280) ⊕ S_residual(300).

After the rank-rigidity step, the kernel of the residual projection has
finrank 98280.  On that kernel the residual coordinate is zero, so injectivity
of the full norm map implies injectivity of the common projection.  Since the
common target also has finrank 98280, the restricted common projection is
automatically a linear equivalence.

This removes `commonLaneSameObject` as an independent scientific leaf.  The
remaining acquisition is to provide the actual common/residual projections and
the already-screened finrank equality for the source-native norm map.
-/

namespace Integration.OggSSP2BCommonLaneKernelWeld

variable {K M C S : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]

/-- Proof-relevant data for the two coordinate projections of the actual norm
map.  `paired_injective` is exactly injectivity of the norm map after choosing
its common/residual target splitting. -/
structure KernelWeldData where
  commonProjection : M →ₗ[K] C
  residualProjection : M →ₗ[K] S
  paired_injective :
    Function.Injective (fun x : M => (commonProjection x, residualProjection x))
  kernel_finrank_eq_common :
    Module.finrank K residualProjection.ker = Module.finrank K C

namespace KernelWeldData

variable (d : KernelWeldData (K := K) (M := M) (C := C) (S := S))

/-- Restrict the common coordinate to the kernel of the residual coordinate. -/
def commonOnResidualKernel : d.residualProjection.ker →ₗ[K] C :=
  d.commonProjection.comp d.residualProjection.ker.subtype

/-- Injectivity of the whole norm map descends to injectivity of the common
coordinate on the residual kernel. -/
theorem commonOnResidualKernel_injective :
    Function.Injective d.commonOnResidualKernel := by
  intro x y hxy
  apply Subtype.ext
  apply d.paired_injective
  apply Prod.ext
  · simpa [commonOnResidualKernel] using hxy
  · have hx : d.residualProjection x.1 = 0 := LinearMap.mem_ker.mp x.2
    have hy : d.residualProjection y.1 = 0 := LinearMap.mem_ker.mp y.2
    exact hx.trans hy.symm

/-- Equal finite dimensions turn the injective common restriction into a
surjection. -/
theorem commonOnResidualKernel_surjective :
    Function.Surjective d.commonOnResidualKernel :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := d.commonOnResidualKernel) d.kernel_finrank_eq_common).mp
    d.commonOnResidualKernel_injective

/-- The common 98280 lane is therefore not an extra same-object hypothesis: it
is the residual kernel itself, canonically equivalent to the common target. -/
noncomputable def commonLaneEquiv : d.residualProjection.ker ≃ₗ[K] C :=
  LinearMap.linearEquivOfInjective
    d.commonOnResidualKernel
    d.commonOnResidualKernel_injective
    d.kernel_finrank_eq_common

/-- Proposition-level form consumed by the terminal norm-weld compiler. -/
theorem commonLaneSameObjectPaid :
    Nonempty (d.residualProjection.ker ≃ₗ[K] C) :=
  ⟨d.commonLaneEquiv⟩

end KernelWeldData

end Integration.OggSSP2BCommonLaneKernelWeld
