import Integration.OggSSP2BResidualBlockProjectorFactorization

/-!
# Block-projector naturality for the source-native 2B norm map

The remaining residual factorization equation should not be supplied ad hoc.
For a centralizer-equivariant norm map, corresponding central block idempotents
on source and target commute with the map.

This file isolates the purely linear consequence.  Suppose

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
by `ResidualBlockProjectorReceipt`.  The only genuinely representation-aware
input left is the standard theorem that the source-native norm is equivariant
for the actual centralizer action and hence commutes with its central block
idempotents.
-/

namespace Integration.OggSSP2BBlockProjectorNaturality

namespace R := Integration.OggSSP2BResidualBlockProjectorFactorization

variable {K M T S : Type*}
  [Semiring K]
  [AddCommMonoid M] [Module K M]
  [AddCommMonoid T] [Module K T]
  [AddCommMonoid S] [Module K S]

/-- Abstract source/target block naturality data. -/
structure BlockNaturalityReceipt
    (n : M →ₗ[K] T) (q : T →ₗ[K] S) : Prop where
  sourceProjector : M →ₗ[K] M
  targetProjector : T →ₗ[K] T
  source_idempotent : sourceProjector.comp sourceProjector = sourceProjector
  source_range_finrank_eq_24 :
    ∀ [DivisionRing K] [FiniteDimensional K M],
      Module.finrank K sourceProjector.range = 24
  norm_intertwines_blocks : targetProjector.comp n = n.comp sourceProjector
  residual_target_identity : q.comp targetProjector = q
  blockProvenance : String

/-- Projector naturality gives the residual source-projector equation. -/
theorem residual_comp_sourceProjector
    (n : M →ₗ[K] T) (q : T →ₗ[K] S)
    (r : BlockNaturalityReceipt n q) :
    (q.comp n).comp r.sourceProjector = q.comp n := by
  calc
    (q.comp n).comp r.sourceProjector
        = q.comp (n.comp r.sourceProjector) := by simp [LinearMap.comp_assoc]
    _ = q.comp (r.targetProjector.comp n) := by rw [r.norm_intertwines_blocks]
    _ = (q.comp r.targetProjector).comp n := by simp [LinearMap.comp_assoc]
    _ = q.comp n := by rw [r.residual_target_identity]

end Integration.OggSSP2BBlockProjectorNaturality
