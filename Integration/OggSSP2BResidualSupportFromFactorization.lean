import Integration.OggSSP2BResidualSupportSqueeze

/-!
# Residual support bound from the certified 24-dimensional source lane

The CTBlocks/decomposition runtime identifies one unique 24-dimensional simple
as the only source support not shared with the common 98280 lane.  The
map-level content needed downstream is therefore not a full matrix for the
residual norm coordinate.  It is the much smaller factorization statement

  M_minus --project--> R24 --f--> S_300

for the actual residual coordinate.

Any map factoring through a 24-dimensional space has image finrank at most 24.
This owner turns that literal factorization into the
`ResidualSupportUpperBoundReceipt` consumed by the rank squeeze.
-/

namespace Integration.OggSSP2BResidualSupportFromFactorization

namespace Squeeze := Integration.OggSSP2BResidualSupportSqueeze

variable {K M S R24 : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]
  [AddCommGroup R24] [Module K R24] [FiniteDimensional K R24]

/-- Literal map factorization of the actual residual norm coordinate through
the runtime-certified unique 24-dimensional residual source lane. -/
structure Residual24FactorizationReceipt
    (residual : M →ₗ[K] S) : Prop where
  sourceProjection : M →ₗ[K] R24
  residualOn24 : R24 →ₗ[K] S
  factorization : residual = residualOn24.comp sourceProjection
  residualSource_finrank_eq_24 : Module.finrank K R24 = 24
  sourceProvenance : String

namespace Residual24FactorizationReceipt

variable {residual : M →ₗ[K] S}
variable (r : Residual24FactorizationReceipt (R24 := R24) residual)

/-- The actual residual image lies inside the image of the 24-dimensional
factor map. -/
theorem range_le_residualOn24_range :
    residual.range ≤ r.residualOn24.range := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨r.sourceProjection x, ?_⟩
  rw [r.factorization]
  rfl

/-- Hence the actual residual coordinate has rank at most 24. -/
theorem range_finrank_le_24 :
    Module.finrank K residual.range ≤ 24 := by
  calc
    Module.finrank K residual.range
        ≤ Module.finrank K r.residualOn24.range :=
      Submodule.finrank_mono r.range_le_residualOn24_range
    _ ≤ Module.finrank K R24 := LinearMap.finrank_range_le r.residualOn24
    _ = 24 := r.residualSource_finrank_eq_24

/-- Compile directly to the support receipt consumed by the no-slack rank
squeeze. -/
def toSupportUpperBound : Squeeze.ResidualSupportUpperBoundReceipt residual where
  range_finrank_le_24 := r.range_finrank_le_24

end Residual24FactorizationReceipt

end Integration.OggSSP2BResidualSupportFromFactorization
