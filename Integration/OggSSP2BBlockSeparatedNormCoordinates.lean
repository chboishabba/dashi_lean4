import Integration.OggSSP2BTateCokernelRankRigidity
import Integration.OggSSP2BCommonLaneKernelWeld

/-!
# Common/residual norm coordinates from the canonical 2-block split

The strengthened CTBlocks screen is designed to prove that the common 98280
lane and residual 300 lane of the weight-two plus-side module lie in disjoint
2-blocks.  Block idempotents therefore give a canonical equivariant target
splitting

  T_plus  ≃  C_common × S_residual.

Once this target splitting is supplied, the source-native norm map

  norm : M_minus -> T_plus

itself determines the common and residual coordinate maps by projection.  The
paired coordinate map is just `targetSplit ∘ norm`, so its injectivity follows
from source-native injectivity of `norm`; no separate projection/injectivity
hypotheses remain.
-/

namespace Integration.OggSSP2BBlockSeparatedNormCoordinates

namespace Kernel := Integration.OggSSP2BCommonLaneKernelWeld
namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity

variable {K M T C S : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup T] [Module K T] [FiniteDimensional K T]
  [AddCommGroup C] [Module K C] [FiniteDimensional K C]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]

/-- Source-native norm map, before choosing block coordinates. -/
structure SourceNormReceipt where
  norm : M →ₗ[K] T
  norm_injective : Function.Injective norm
  sourceProvenance : String

/-- Canonical target decomposition supplied by modular block idempotents. -/
structure BlockTargetSplitReceipt where
  targetSplit : T ≃ₗ[K] C × S
  common_finrank_eq_98280 : Module.finrank K C = 98280
  residual_finrank_eq_300 : Module.finrank K S = 300
  blockSeparated : Prop
  blockSeparated_paid : blockSeparated
  sourceProvenance : String

namespace SourceNormReceipt

variable (n : SourceNormReceipt (K := K) (M := M) (T := T))
variable (b : BlockTargetSplitReceipt (K := K) (T := T) (C := C) (S := S))

/-- Common coordinate of the actual norm map, canonically induced by the block
split. -/
def commonProjection : M →ₗ[K] C :=
  (LinearMap.fst K C S).comp (b.targetSplit.toLinearMap.comp n.norm)

/-- Residual coordinate of the actual norm map. -/
def residualProjection : M →ₗ[K] S :=
  (LinearMap.snd K C S).comp (b.targetSplit.toLinearMap.comp n.norm)

/-- The paired coordinate map is injective because it is literally the target
block equivalence applied to the injective source-native norm map. -/
theorem paired_injective :
    Function.Injective
      (fun x : M => (n.commonProjection b x, n.residualProjection b x)) := by
  intro x y hxy
  apply n.norm_injective
  apply b.targetSplit.injective
  apply Prod.ext
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy

/-- Attach map-coupled rank data to the residual coordinate and obtain the
kernel/common weld consumed downstream. -/
def toKernelWeldData
    (hrank : Rank.LinearRankRigidityReceipt (n.residualProjection b)) :
    Kernel.KernelWeldData (K := K) (M := M) (C := C) (S := S) where
  commonProjection := n.commonProjection b
  residualProjection := n.residualProjection b
  paired_injective := n.paired_injective b
  kernel_finrank_eq_common := by
    calc
      Module.finrank K (n.residualProjection b).ker = 98280 :=
        hrank.kernel_finrank_eq_98280
      _ = Module.finrank K C := b.common_finrank_eq_98280.symm

end SourceNormReceipt

end Integration.OggSSP2BBlockSeparatedNormCoordinates
