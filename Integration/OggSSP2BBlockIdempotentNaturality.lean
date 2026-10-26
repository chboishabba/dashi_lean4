import Mathlib.LinearAlgebra.Basic

/-!
# Central block-idempotent naturality is formal

For the 2B norm weld, once the source and target carry the actual module action,
commutation with a central block idempotent is not an independent theorem.
Any linear/module homomorphism preserves vectors fixed by the idempotent simply
by `map_smul`.  Consequently, if the entire source is supported on a selected
block, the range of the map is supported on the same block.

This is the algebraic compiler behind the modular-block source authority.  It
does not instantiate the actual Monster-centralizer group-algebra action or
choose the residual block; those remain same-object data.
-/

namespace Integration.OggSSP2BBlockIdempotentNaturality

variable {A M S : Type*}
  [Semiring A]
  [AddCommMonoid M] [Module A M]
  [AddCommMonoid S] [Module A S]

/-- A submodule is supported on `e` when `e` acts as identity on all of it. -/
def BlockSupported (e : A) (W : Submodule A S) : Prop :=
  ∀ y, y ∈ W → e • y = y

/-- Module-linearity alone makes every linear map preserve an idempotent block.
No extra equivariance receipt is needed once the scalar action is the actual
block-algebra action. -/
theorem map_preserves_idempotent_block
    (f : M →ₗ[A] S) (e : A) (x : M)
    (hx : e • x = x) :
    e • f x = f x := by
  rw [← f.map_smul, hx]

/-- If the source is entirely in the selected block, then the image/range is in
that same block. -/
theorem range_block_supported_of_source_block_supported
    (f : M →ₗ[A] S) (e : A)
    (hsource : ∀ x : M, e • x = x) :
    BlockSupported e f.range := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact map_preserves_idempotent_block f e x (hsource x)

end Integration.OggSSP2BBlockIdempotentNaturality
