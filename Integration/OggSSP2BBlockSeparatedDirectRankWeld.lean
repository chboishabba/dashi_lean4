import Integration.OggSSP2BBlockSeparatedNormCoordinates
import Integration.OggSSP2BDirectResidualRankCompiler

/-!
# Block-separated norm weld from one direct residual-rank fact

The canonical modular-block split supplies the actual common and residual
coordinates of the source-native norm map.  The norm itself is injective.
Consequently, once the actual residual coordinate is known to have rank 24,
rank-nullity forces its kernel to have finrank 98280.  This is exactly the
common target dimension, so the existing kernel-weld compiler produces the
same-object common-lane equivalence automatically.

No independent `kernelControl` or common-map-surjectivity hypothesis remains.
-/

namespace Integration.OggSSP2BBlockSeparatedDirectRankWeld

namespace B := Integration.OggSSP2BBlockSeparatedNormCoordinates
namespace D := Integration.OggSSP2BDirectResidualRankCompiler
namespace K := Integration.OggSSP2BCommonLaneKernelWeld

variable {R M T C S : Type*}
  [DivisionRing R]
  [AddCommGroup M] [Module R M] [FiniteDimensional R M]
  [AddCommGroup T] [Module R T] [FiniteDimensional R T]
  [AddCommGroup C] [Module R C] [FiniteDimensional R C]
  [AddCommGroup S] [Module R S] [FiniteDimensional R S]

/-- The only new map-level datum needed after the block split is the rank of the
actual residual coordinate. -/
structure ActualResidualRank24Receipt
    (n : B.SourceNormReceipt (K := R) (M := M) (T := T))
    (b : B.BlockTargetSplitReceipt (K := R) (T := T) (C := C) (S := S)) : Prop where
  source_finrank_eq_98304 : Module.finrank R M = 98304
  residual_range_finrank_eq_24 :
    Module.finrank R (n.residualProjection b).range = 24

namespace ActualResidualRank24Receipt

variable
  (n : B.SourceNormReceipt (K := R) (M := M) (T := T))
  (b : B.BlockTargetSplitReceipt (K := R) (T := T) (C := C) (S := S))
  (r : ActualResidualRank24Receipt n b)

/-- Convert the one direct runtime rank fact to the standard map-coupled rank
receipt used throughout the downstream norm-weld chain. -/
def toLinearRankRigidity :
    Integration.OggSSP2BTateCokernelRankRigidity.LinearRankRigidityReceipt
      (n.residualProjection b) :=
  (D.DirectResidualRankReceipt.mk
    r.source_finrank_eq_98304 r.residual_range_finrank_eq_24).toLinearRankRigidity

/-- Common-lane same-object cancellation is now automatic. -/
def toKernelWeldData :
    K.KernelWeldData (K := R) (M := M) (C := C) (S := S) :=
  n.toKernelWeldData b r.toLinearRankRigidity

/-- The residual kernel is literally 98280-dimensional on the actual map. -/
theorem residual_kernel_finrank_eq_98280 :
    Module.finrank R (n.residualProjection b).ker = 98280 :=
  r.toLinearRankRigidity.kernel_finrank_eq_98280

/-- The common lane is therefore an actual same-object linear equivalence, not
just a matching dimension or composition profile. -/
theorem common_lane_same_object :
    Nonempty ((n.residualProjection b).ker ≃ₗ[R] C) :=
  r.toKernelWeldData.commonLaneSameObjectPaid

end ActualResidualRank24Receipt

end Integration.OggSSP2BBlockSeparatedDirectRankWeld
