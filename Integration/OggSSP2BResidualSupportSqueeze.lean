import Integration.OggSSP2BTateCokernelRankRigidity

/-!
# Residual-support squeeze for the actual 2B norm map

After the canonical block split, the source-native norm map has actual
coordinates

  common   : M_98304 -> C_98280,
  residual : M_98304 -> S_300,

and the paired map `(common,residual)` is injective.

The strengthened Co1 decomposition runtime does not need to materialize the
residual matrix.  Its block/support statement has the exact map-level
consequence needed here: the residual image can use at most the unique
24-dimensional residual simple lane.

From

  finrank range(residual) <= 24

and paired injectivity, the residual kernel injects into the 98280-dimensional
common target.  Rank-nullity then has no slack and forces

  finrank range(residual) = 24,
  finrank ker(residual)   = 98280.

Thus one support upper bound replaces both the old residual-rank calculation
and the old kernel-control hypothesis.
-/

namespace Integration.OggSSP2BResidualSupportSqueeze

namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity

variable {K M C S : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]

/-- Map-level semantic consequence of the certified residual support theorem. -/
structure ResidualSupportUpperBoundReceipt (residual : M →ₗ[K] S) : Prop where
  range_finrank_le_24 : Module.finrank K residual.range ≤ 24

/-- Restrict the common coordinate to the kernel of the residual coordinate. -/
def commonOnResidualKernel
    (common : M →ₗ[K] C) (residual : M →ₗ[K] S) :
    residual.ker →ₗ[K] C :=
  common.domRestrict residual.ker

/-- Paired injectivity makes the common coordinate injective on the residual
kernel. -/
theorem commonOnResidualKernel_injective
    (common : M →ₗ[K] C) (residual : M →ₗ[K] S)
    (paired_injective : Function.Injective (fun x : M => (common x, residual x))) :
    Function.Injective (commonOnResidualKernel common residual) := by
  intro x y hxy
  apply Subtype.ext
  apply paired_injective
  apply Prod.ext
  · exact hxy
  · have hx : residual x.1 = 0 := by
      simpa only [LinearMap.mem_ker] using x.2
    have hy : residual y.1 = 0 := by
      simpa only [LinearMap.mem_ker] using y.2
    rw [hx, hy]

/-- The residual kernel can be no larger than the common target. -/
theorem residual_kernel_finrank_le_common
    (common : M →ₗ[K] C) (residual : M →ₗ[K] S)
    (paired_injective : Function.Injective (fun x : M => (common x, residual x))) :
    Module.finrank K residual.ker ≤ Module.finrank K C := by
  exact LinearMap.finrank_le_finrank_of_injective
    (commonOnResidualKernel_injective common residual paired_injective)

/-- Central compiler: support separation + paired injectivity forces the actual
residual map to have rank exactly 24. -/
def compileLinearRankRigidity
    (common : M →ₗ[K] C) (residual : M →ₗ[K] S)
    (paired_injective : Function.Injective (fun x : M => (common x, residual x)))
    (hsource : Module.finrank K M = 98304)
    (hcommon : Module.finrank K C = 98280)
    (hsupport : ResidualSupportUpperBoundReceipt residual) :
    Rank.LinearRankRigidityReceipt residual := by
  let rr : Nat := Module.finrank K residual.range
  let kk : Nat := Module.finrank K residual.ker
  have hrn := LinearMap.finrank_range_add_finrank_ker residual
  have hker : kk ≤ 98280 := by
    dsimp [kk]
    rw [← hcommon]
    exact residual_kernel_finrank_le_common common residual paired_injective
  have hsum : kk + rr = 98304 := by
    dsimp [kk, rr]
    omega
  have hrle : rr ≤ 24 := by
    exact hsupport.range_finrank_le_24
  let numeric : Rank.RankRigidityReceipt := {
    residualProjectionRank := rr
    residualProjectionKernelDimension := kk
    rankNullity := hsum
    residualRank_le_natural := hrle
    kernel_le_common := hker
  }
  exact {
    numeric := numeric
    residual_rank_matches := rfl
    residual_kernel_matches := rfl
  }

/-- Expose the forced rank as the preferred downstream theorem. -/
theorem residual_finrank_eq_24
    (common : M →ₗ[K] C) (residual : M →ₗ[K] S)
    (paired_injective : Function.Injective (fun x : M => (common x, residual x)))
    (hsource : Module.finrank K M = 98304)
    (hcommon : Module.finrank K C = 98280)
    (hsupport : ResidualSupportUpperBoundReceipt residual) :
    Module.finrank K residual.range = 24 :=
  (compileLinearRankRigidity common residual paired_injective
    hsource hcommon hsupport).residual_finrank_eq_24

end Integration.OggSSP2BResidualSupportSqueeze
