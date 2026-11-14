import Integration.OggSSP2BTateCokernelRankRigidity

/-!
# Direct residual-rank compiler for the 2B norm weld

The older rank-rigidity route obtained the residual rank-24 theorem from two
one-sided bounds, one of which was phrased as kernel control.  Once a runtime
or source-native calculation is attached directly to the actual residual norm
coordinate, that detour is unnecessary.

For the actual residual map

  residual : M_minus -> S_residual

it is enough to know

  finrank M_minus = 98304,
  finrank range(residual) = 24.

Rank-nullity then forces

  finrank ker(residual) = 98280.

This produces the existing `LinearRankRigidityReceipt`, so every downstream
common-lane cancellation and Frobenius-weld theorem can consume a single
map-level runtime fact: the actual residual coordinate has rank 24.
-/

namespace Integration.OggSSP2BDirectResidualRankCompiler

namespace Rank := Integration.OggSSP2BTateCokernelRankRigidity

variable {K M S : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]

/-- Minimal map-coupled receipt needed after the block-separated target split. -/
structure DirectResidualRankReceipt (residual : M →ₗ[K] S) : Prop where
  source_finrank_eq_98304 : Module.finrank K M = 98304
  residual_range_finrank_eq_24 : Module.finrank K residual.range = 24

namespace DirectResidualRankReceipt

variable {residual : M →ₗ[K] S}
variable (r : DirectResidualRankReceipt residual)

/-- Rank-nullity leaves exactly the 98280-dimensional common kernel. -/
theorem residual_kernel_finrank_eq_98280 :
    Module.finrank K residual.ker = 98280 := by
  have h := LinearMap.finrank_range_add_finrank_ker residual
  rw [r.residual_range_finrank_eq_24, r.source_finrank_eq_98304] at h
  omega

/-- Compile the direct runtime rank fact into the existing proof-bearing rank
rigidity receipt used by the norm-weld chain. -/
def toLinearRankRigidity : Rank.LinearRankRigidityReceipt residual where
  numeric := {
    residualProjectionRank := 24
    residualProjectionKernelDimension := 98280
    rankNullity := by decide
    residualRank_le_natural := by decide
    kernel_le_common := by decide
  }
  residual_rank_matches := by
    simpa using r.residual_range_finrank_eq_24
  residual_kernel_matches := by
    simpa using r.residual_kernel_finrank_eq_98280

/-- The actual residual coordinate is automatically nonzero. -/
theorem residual_ne_zero : residual ≠ 0 :=
  r.toLinearRankRigidity.residual_ne_zero

end DirectResidualRankReceipt

end Integration.OggSSP2BDirectResidualRankCompiler
