import Integration.OggSSP2BCentralizerMod2CancellationRigidity

/-!
# Rank rigidity of the weight-two Tate norm cokernel

The actual source-native norm map has dimensions

  f : M_minus(98304) -> C(98280) ⊕ S(300)

and is injective.  The centralizer decomposition-matrix max-cut is designed to
show that all composition support common with the 300-dimensional residual
piece is the single 24-dimensional natural factor.  Hence the residual
projection `pi_S ∘ f` has rank at most 24.

On the other hand, the kernel of that residual projection injects into the
98280-dimensional common target `C`, hence has dimension at most 98280.
Rank-nullity leaves no slack:

  rank(pi_S ∘ f) = 24,
  dim ker(pi_S ∘ f) = 98280.

The original `RankRigidityReceipt` records the arithmetic squeeze.  The new
`LinearRankRigidityReceipt` ties those integers to the range and kernel of an
actual linear map, so rank 24 immediately proves that concrete residual map is
nonzero and its concrete kernel has finrank 98280.
-/

namespace Integration.OggSSP2BTateCokernelRankRigidity

abbrev minusDimension : Nat := 98304
abbrev commonTargetDimension : Nat := 98280
abbrev residualTargetDimension : Nat := 300
abbrev residualNaturalDimension : Nat := 24

structure RankRigidityReceipt where
  residualProjectionRank : Nat
  residualProjectionKernelDimension : Nat
  rankNullity :
    residualProjectionKernelDimension + residualProjectionRank = minusDimension
  residualRank_le_natural : residualProjectionRank ≤ residualNaturalDimension
  kernel_le_common : residualProjectionKernelDimension ≤ commonTargetDimension

namespace RankRigidityReceipt

variable (r : RankRigidityReceipt)

/-- The two one-sided bounds and rank-nullity force the residual projection to
use the entire natural 24-dimensional lane. -/
theorem residual_rank_eq_24 : r.residualProjectionRank = 24 := by
  omega

/-- Consequently the residual-projection kernel has exactly the common target
size 98280. -/
theorem kernel_dimension_eq_98280 :
    r.residualProjectionKernelDimension = 98280 := by
  omega

/-- In particular the numeric residual rank is positive. -/
theorem residual_rank_positive : 0 < r.residualProjectionRank := by
  rw [r.residual_rank_eq_24]
  decide

end RankRigidityReceipt

/-- Proof-bearing attachment of the numeric rank squeeze to one actual residual
linear map.  This is the preferred receipt downstream. -/
structure LinearRankRigidityReceipt
    {K M S : Type*}
    [DivisionRing K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    (residual : M →ₗ[K] S) where
  numeric : RankRigidityReceipt
  residual_rank_matches :
    Module.finrank K residual.range = numeric.residualProjectionRank
  residual_kernel_matches :
    Module.finrank K residual.ker = numeric.residualProjectionKernelDimension

namespace LinearRankRigidityReceipt

variable
  {K M S : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  {residual : M →ₗ[K] S}
  (r : LinearRankRigidityReceipt residual)

/-- The actual residual map has rank 24. -/
theorem residual_finrank_eq_24 :
    Module.finrank K residual.range = 24 := by
  rw [r.residual_rank_matches, r.numeric.residual_rank_eq_24]

/-- The actual residual kernel has finrank 98280. -/
theorem kernel_finrank_eq_98280 :
    Module.finrank K residual.ker = 98280 := by
  rw [r.residual_kernel_matches, r.numeric.kernel_dimension_eq_98280]

/-- Rank 24 rules out the zero map on the actual residual coordinate. -/
theorem residual_ne_zero : residual ≠ 0 := by
  intro hzero
  have hr := r.residual_finrank_eq_24
  rw [hzero] at hr
  simp at hr

end LinearRankRigidityReceipt

structure PromotionBoundary where
  normMapInjectivitySourceNative : Bool
  supportSeparationRuntimePaid : Bool
  residualRankUpperBoundPaid : Bool
  kernelCommonTargetUpperBoundPaid : Bool
  rankRigidityCompilerFormalized : Bool
  mapCoupledRankReceiptFormalized : Bool
  residualRankTwentyFourPaid : Bool
  commonKernelDimension98280Paid : Bool
  residualMapForcedFrobenius : Bool
  actualTateExteriorSquareWeldPaid : Bool

def canonicalBoundary : PromotionBoundary where
  normMapInjectivitySourceNative := true
  supportSeparationRuntimePaid := false
  residualRankUpperBoundPaid := false
  kernelCommonTargetUpperBoundPaid := true
  rankRigidityCompilerFormalized := true
  mapCoupledRankReceiptFormalized := true
  residualRankTwentyFourPaid := false
  commonKernelDimension98280Paid := false
  residualMapForcedFrobenius := false
  actualTateExteriorSquareWeldPaid := false

theorem same_object_weld_still_open :
    canonicalBoundary.actualTateExteriorSquareWeldPaid = false := rfl

end Integration.OggSSP2BTateCokernelRankRigidity
