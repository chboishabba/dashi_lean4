import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod
import Integration.OggSSP2BCommonLaneKernelWeld

/-!
# Cancel the common norm lane at the level of actual cokernels

Let the actual norm map be represented by its two target coordinates

  f = (common, residual) : M -> C × S.

If the restriction of `common` to `ker residual` is an isomorphism onto `C`
(which is forced by injectivity + the 98280 finrank equality), then projection
to `S` induces a linear equivalence

  (C × S) / range(f)  ≃  S / range(residual).

Thus common-lane cancellation is not merely a Grothendieck/Jordan--Hoelder
statement: it holds on the literal cokernel.  Once the residual map is the
Frobenius 24 -> Sym2(24) embedding, the source-native Tate cokernel is therefore
its literal residual cokernel.
-/

namespace Integration.OggSSP2BCokernelCancellation

namespace Kernel := Integration.OggSSP2BCommonLaneKernelWeld

variable {K M C S : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]

namespace Kernel.KernelWeldData

variable (d : Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S))

/-- The actual norm map after choosing common/residual target coordinates. -/
def normMap : M →ₗ[K] C × S :=
  d.commonProjection.prod d.residualProjection

/-- Literal image of the norm map in the split target. -/
def normRange : Submodule K (C × S) := d.normMap.range

/-- Literal image of the residual projection. -/
def residualRange : Submodule K S := d.residualProjection.range

/-- Projection to the residual coordinate sends the full norm image into the
residual image, so it descends to cokernels. -/
theorem normRange_le_comap_residual :
    d.normRange ≤ Submodule.comap (LinearMap.snd K C S) d.residualRange := by
  intro z hz
  rcases hz with ⟨x, rfl⟩
  change d.residualProjection x ∈ d.residualProjection.range
  exact ⟨x, rfl⟩

/-- Projection onto the residual target induces the canonical map from the
full norm cokernel to the residual cokernel. -/
def cokernelToResidualCokernel :
    ((C × S) ⧸ d.normRange) →ₗ[K] (S ⧸ d.residualRange) :=
  d.normRange.mapQ d.residualRange (LinearMap.snd K C S)
    d.normRange_le_comap_residual

/-- Every residual-cokernel class has the obvious preimage represented by
`(0,s)` in the full target. -/
theorem cokernelToResidualCokernel_surjective :
    Function.Surjective d.cokernelToResidualCokernel := by
  intro q
  refine Submodule.Quotient.induction_on d.residualRange q ?_
  intro s
  refine ⟨d.normRange.mkQ (0, s), ?_⟩
  simp [cokernelToResidualCokernel, normRange, residualRange, normMap]

/-- Kernel-zero form of the cancellation argument.  If the residual quotient
of `(c,s)` vanishes, subtract a norm preimage of `s`; the remainder has zero
residual coordinate and is then killed by surjectivity of the common map on
`ker residual`. -/
theorem cokernelToResidualCokernel_kernel_zero :
    ∀ q, d.cokernelToResidualCokernel q = 0 → q = 0 := by
  intro q
  refine Submodule.Quotient.induction_on d.normRange q ?_
  intro p hp
  have hs0 : d.residualRange.mkQ p.2 = 0 := by
    simpa [cokernelToResidualCokernel, normRange, residualRange, normMap] using hp
  have hs_mem : p.2 ∈ d.residualRange :=
    (Submodule.Quotient.mk_eq_zero d.residualRange).mp hs0
  rcases hs_mem with ⟨m, hm⟩
  let c : C := p.1 - d.commonProjection m
  obtain ⟨k, hk⟩ := d.commonOnResidualKernel_surjective c
  change d.commonProjection k.1 = c at hk
  have hk_res : d.residualProjection k.1 = 0 := LinearMap.mem_ker.mp k.2
  have hp_range : p ∈ d.normRange := by
    refine ⟨m + k.1, ?_⟩
    apply Prod.ext
    · change d.commonProjection (m + k.1) = p.1
      rw [map_add, hk]
      simp [c]
    · change d.residualProjection (m + k.1) = p.2
      rw [map_add, hk_res, add_zero]
      exact hm
  exact (Submodule.Quotient.mk_eq_zero d.normRange).mpr hp_range

/-- The quotient projection is injective because its kernel is zero. -/
theorem cokernelToResidualCokernel_injective :
    Function.Injective d.cokernelToResidualCokernel := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply d.cokernelToResidualCokernel_kernel_zero
  have hzero : d.cokernelToResidualCokernel x - d.cokernelToResidualCokernel y = 0 :=
    sub_eq_zero.mpr hxy
  simpa using hzero

/-- Literal cokernel cancellation theorem. -/
noncomputable def cokernelEquivResidualCokernel :
    ((C × S) ⧸ d.normRange) ≃ₗ[K] (S ⧸ d.residualRange) :=
  LinearEquiv.ofBijective d.cokernelToResidualCokernel
    ⟨d.cokernelToResidualCokernel_injective,
      d.cokernelToResidualCokernel_surjective⟩

/-- Proposition-level receipt for downstream compilers. -/
theorem literalCokernelCancellationPaid :
    Nonempty (((C × S) ⧸ d.normRange) ≃ₗ[K] (S ⧸ d.residualRange)) :=
  ⟨d.cokernelEquivResidualCokernel⟩

end Kernel.KernelWeldData

end Integration.OggSSP2BCokernelCancellation
