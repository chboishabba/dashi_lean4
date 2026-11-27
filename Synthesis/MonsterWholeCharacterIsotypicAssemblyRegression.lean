import Synthesis.MonsterWholeCharacterIsotypicAssembly

/-!
Regression consumer for the generic semisimple/isotypic assembly used by the
Monster 3B whole-character route.

This deliberately contains no Monster-specific data.  It only checks that once
a semisimple finite module has a proof that every simple submodule has one
fixed simple type, the implementation returns a finite-copy linear equivalence.
-/

namespace Synthesis

noncomputable section

universe u

variable {R M S : Type u}
variable [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup S] [Module R S]
variable [IsSemisimpleModule R M]
variable [Module.Finite R M]

example
    (classify :
      ∀ (m : Submodule R M), [IsSimpleModule R m] →
        Nonempty (m ≃ₗ[R] S)) :
    ∃ n : ℕ, Nonempty (M ≃ₗ[R] (Fin n → S)) := by
  exact finiteCopiesOfOneSimpleType classify

end

end Synthesis
