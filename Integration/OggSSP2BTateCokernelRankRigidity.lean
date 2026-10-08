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
Rank-nullity then leaves no slack:

  rank(pi_S ∘ f) = 24,
  dim ker(pi_S ∘ f) = 98280.

Thus the common lane is covered automatically and the residual 24 map is
nonzero/full-rank.  Once `Hom_Co1(24,Sym^2(24))` is runtime-proved to be
one-dimensional, that residual map is forced to be the Frobenius-square
embedding.  This file formalizes the dimension squeeze without pretending the
runtime support-separation hypotheses are already paid.
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

/-- In particular the residual map cannot vanish. -/
theorem residual_rank_positive : 0 < r.residualProjectionRank := by
  rw [r.residual_rank_eq_24]
  decide

end RankRigidityReceipt

structure PromotionBoundary where
  normMapInjectivitySourceNative : Bool
  supportSeparationRuntimePaid : Bool
  residualRankUpperBoundPaid : Bool
  kernelCommonTargetUpperBoundPaid : Bool
  rankRigidityCompilerFormalized : Bool
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
  residualRankTwentyFourPaid := false
  commonKernelDimension98280Paid := false
  residualMapForcedFrobenius := false
  actualTateExteriorSquareWeldPaid := false

theorem same_object_weld_still_open :
    canonicalBoundary.actualTateExteriorSquareWeldPaid = false := rfl

end Integration.OggSSP2BTateCokernelRankRigidity
