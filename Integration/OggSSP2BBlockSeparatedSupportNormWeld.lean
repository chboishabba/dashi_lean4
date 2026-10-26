import Integration.OggSSP2BBlockSeparatedNormCoordinates
import Integration.OggSSP2BResidualSupportSqueeze

/-!
# Canonical block norm weld from residual support separation

The strengthened CTBlocks/decomposition runtime pays the representation-side
statement that the actual residual block can see at most the unique
24-dimensional simple lane.  Once that semantic support statement is attached
to the literal residual coordinate induced by the canonical block split, no
further rank computation is needed.

This compiler combines:

* source-native injective norm map;
* canonical common/residual target coordinates from block idempotents;
* source finrank 98304;
* actual residual-image support <= 24.

It returns the existing `LinearRankRigidityReceipt` and `KernelWeldData`, hence
pays residual rank 24, residual-kernel rank 98280, and the common-lane
same-object equivalence.
-/

namespace Integration.OggSSP2BBlockSeparatedSupportNormWeld

namespace B := Integration.OggSSP2BBlockSeparatedNormCoordinates
namespace Squeeze := Integration.OggSSP2BResidualSupportSqueeze
namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity
namespace K := Integration.OggSSP2BCommonLaneKernelWeld

variable {R M T C S : Type*}
  [DivisionRing R]
  [AddCommGroup M] [Module R M] [FiniteDimensional R M]
  [AddCommGroup T] [Module R T] [FiniteDimensional R T]
  [AddCommGroup C] [Module R C] [FiniteDimensional R C]
  [AddCommGroup S] [Module R S] [FiniteDimensional R S]

structure ActualResidualSupportReceipt
    (n : B.SourceNormReceipt (K := R) (M := M) (T := T))
    (b : B.BlockTargetSplitReceipt (K := R) (T := T) (C := C) (S := S)) : Prop where
  source_finrank_eq_98304 : Module.finrank R M = 98304
  residualSupport :
    Squeeze.ResidualSupportUpperBoundReceipt (n.residualProjection b)

namespace ActualResidualSupportReceipt

variable
  (n : B.SourceNormReceipt (K := R) (M := M) (T := T))
  (b : B.BlockTargetSplitReceipt (K := R) (T := T) (C := C) (S := S))
  (r : ActualResidualSupportReceipt n b)

/-- Representation support + source-native injectivity force the exact map rank
receipt consumed by all downstream welds. -/
def toLinearRankRigidity : Rank.LinearRankRigidityReceipt (n.residualProjection b) :=
  Squeeze.compileLinearRankRigidity
    (n.commonProjection b)
    (n.residualProjection b)
    (n.paired_injective b)
    r.source_finrank_eq_98304
    b.common_finrank_eq_98280
    r.residualSupport

/-- The common 98280 lane cancels as an actual linear object. -/
def toKernelWeldData : K.KernelWeldData (K := R) (M := M) (C := C) (S := S) :=
  n.toKernelWeldData b r.toLinearRankRigidity

theorem residual_rank_is_24 :
    Module.finrank R (n.residualProjection b).range = 24 :=
  r.toLinearRankRigidity.residual_finrank_eq_24

theorem residual_kernel_is_98280 :
    Module.finrank R (n.residualProjection b).ker = 98280 :=
  r.toLinearRankRigidity.kernel_finrank_eq_98280

theorem common_lane_same_object :
    Nonempty ((n.residualProjection b).ker ≃ₗ[R] C) :=
  r.toKernelWeldData.commonLaneSameObjectPaid

end ActualResidualSupportReceipt

end Integration.OggSSP2BBlockSeparatedSupportNormWeld
