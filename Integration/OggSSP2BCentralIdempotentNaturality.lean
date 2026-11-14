import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Central-idempotent naturality is automatic for module homomorphisms

The source-native norm map is centralizer-equivariant.  Algebraically, once it
is represented as a linear map over the centralizer/group algebra, commuting
with a central block idempotent is not an additional same-object hypothesis:
it is `map_smul`.

This tiny owner isolates that point independently of the concrete Monster group
algebra.  If `e : A` acts on source and target by the corresponding block
projectors and `n : M ->_A T`, then

  n (e • x) = e • n x

for every `x`.  Concrete 2B code therefore only has to identify the actual
rank-24 block idempotent and the residual target block; norm/block naturality
itself follows from the already-source-native equivariance of the norm map.
-/

namespace Integration.OggSSP2BCentralIdempotentNaturality

variable {A M T : Type*}
  [Semiring A]
  [AddCommMonoid M] [Module A M]
  [AddCommMonoid T] [Module A T]

/-- Any `A`-linear map automatically intertwines the action of every algebra
 element, hence in particular every central block idempotent. -/
theorem map_smul_idempotent
    (n : M →ₗ[A] T) (e : A) (x : M) :
    n (e • x) = e • n x := by
  exact n.map_smul e x

/-- Function-level formulation used by the block-projector compiler. -/
theorem intertwines_scalar_projectors
    (n : M →ₗ[A] T) (e : A) :
    (fun x : M => n (e • x)) = (fun x : M => e • n x) := by
  funext x
  exact n.map_smul e x

end Integration.OggSSP2BCentralIdempotentNaturality
