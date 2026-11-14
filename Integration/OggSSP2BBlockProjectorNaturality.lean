import Integration.OggSSP2BResidualBlockProjectorFactorization

/-!
# Block-projector naturality for the source-native 2B norm map

The remaining residual factorization equation should not be supplied ad hoc.
For a centralizer-equivariant norm map, corresponding central block idempotents
on source and target commute with the map.

Suppose

  n  : M -> T,
  eM : M -> M,
  eT : T -> T,
  q  : T -> S

satisfy

  eT ∘ n  = n ∘ eM,
  q  ∘ eT = q.

Then the actual residual coordinate `q ∘ n` obeys

  (q ∘ n) ∘ eM = q ∘ n.

Thus central block naturality automatically produces the exact equation needed
by `ResidualBlockProjectorReceipt`.  The remaining representation-aware input
is the standard theorem that the source-native norm is equivariant for the
actual centralizer action and hence commutes with its central block idempotents.
-/

namespace Integration.OggSSP2BBlockProjectorNaturality

namespace R := Integration.OggSSP2BResidualBlockProjectorFactorization

variable {K M T S : Type*}
  [DivisionRing K]
  [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  [AddCommGroup T] [Module K T] [FiniteDimensional K T]
  [AddCommGroup S] [Module K S] [FiniteDimensional K S]

/-- Abstract source/target central-block naturality data. -/
structure BlockNaturalityReceipt
    (n : M →ₗ[K] T) (q : T →ₗ[K] S) : Prop where
  sourceProjector : M →ₗ[K] M
  targetProjector : T →ₗ[K] T
  source_idempotent : sourceProjector.comp sourceProjector = sourceProjector
  source_range_finrank_eq_24 : Module.finrank K sourceProjector.range = 24
  norm_intertwines_blocks : targetProjector.comp n = n.comp sourceProjector
  residual_target_identity : q.comp targetProjector = q
  blockProvenance : String

/-- Projector naturality gives the residual source-projector equation. -/
theorem residual_comp_sourceProjector
    (n : M →ₗ[K] T) (q : T →ₗ[K] S)
    (r : BlockNaturalityReceipt n q) :
    (q.comp n).comp r.sourceProjector = q.comp n := by
  ext x
  have hn := LinearMap.congr_fun r.norm_intertwines_blocks x
  have hq := LinearMap.congr_fun r.residual_target_identity (n x)
  change q (n (r.sourceProjector x)) = q (n x)
  calc
    q (n (r.sourceProjector x)) = q (r.targetProjector (n x)) := by rw [← hn]
    _ = q (n x) := hq

/-- Compile central-block naturality directly into the canonical residual block
projector receipt consumed by the support/rank squeeze. -/
def toResidualBlockProjectorReceipt
    (n : M →ₗ[K] T) (q : T →ₗ[K] S)
    (r : BlockNaturalityReceipt n q) :
    R.ResidualBlockProjectorReceipt (q.comp n) where
  e24 := r.sourceProjector
  idempotent := r.source_idempotent
  range_finrank_eq_24 := r.source_range_finrank_eq_24
  residual_comp_projector := residual_comp_sourceProjector n q r
  blockProvenance := r.blockProvenance

end Integration.OggSSP2BBlockProjectorNaturality
