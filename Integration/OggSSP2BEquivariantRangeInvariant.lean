import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Equivariant maps have invariant range

For the preferred 2B norm-weld route, Co1-stability of the actual residual image
is not an independent source theorem.  Once the source-native norm and the
residual target-block projection are equivariant, their composite is
equivariant, and the range of any equivariant linear map is invariant.

Thus after identifying the actual modular block projector/split, target-range
invariance is formal.
-/

namespace Integration.OggSSP2BEquivariantRangeInvariant

variable {K G M T S : Type*}
  [Semiring K]
  [AddCommMonoid M] [Module K M]
  [AddCommMonoid T] [Module K T]
  [AddCommMonoid S] [Module K S]

/-- Pointwise equivariance for linear actions. -/
def LinearEquivariant
    (actM : G → M →ₗ[K] M)
    (actS : G → S →ₗ[K] S)
    (f : M →ₗ[K] S) : Prop :=
  ∀ g x, f (actM g x) = actS g (f x)

/-- The image/range of `f` is stable under the target action. -/
def RangeInvariant
    (actS : G → S →ₗ[K] S)
    (f : M →ₗ[K] S) : Prop :=
  ∀ g y, y ∈ f.range → actS g y ∈ f.range

/-- Equivariance is preserved by composition. -/
theorem comp_equivariant
    (actM : G → M →ₗ[K] M)
    (actT : G → T →ₗ[K] T)
    (actS : G → S →ₗ[K] S)
    (f : M →ₗ[K] T)
    (p : T →ₗ[K] S)
    (hf : LinearEquivariant actM actT f)
    (hp : LinearEquivariant actT actS p) :
    LinearEquivariant actM actS (p.comp f) := by
  intro g x
  change p (f (actM g x)) = actS g (p (f x))
  rw [hf g x]
  exact hp g (f x)

/-- Main compiler: an equivariant linear map has invariant range. -/
theorem range_invariant_of_equivariant
    (actM : G → M →ₗ[K] M)
    (actS : G → S →ₗ[K] S)
    (f : M →ₗ[K] S)
    (hf : LinearEquivariant actM actS f) :
    RangeInvariant actS f := by
  intro g y hy
  rcases hy with ⟨x, rfl⟩
  exact ⟨actM g x, hf g x⟩

/-- Combined form used by the norm/block route: equivariant norm followed by an
equivariant residual block projection has invariant residual image. -/
theorem range_invariant_of_equivariant_composite
    (actM : G → M →ₗ[K] M)
    (actT : G → T →ₗ[K] T)
    (actS : G → S →ₗ[K] S)
    (norm : M →ₗ[K] T)
    (residualProjection : T →ₗ[K] S)
    (hnorm : LinearEquivariant actM actT norm)
    (hprojection : LinearEquivariant actT actS residualProjection) :
    RangeInvariant actS (residualProjection.comp norm) :=
  range_invariant_of_equivariant actM actS
    (residualProjection.comp norm)
    (comp_equivariant actM actT actS norm residualProjection hnorm hprojection)

end Integration.OggSSP2BEquivariantRangeInvariant
