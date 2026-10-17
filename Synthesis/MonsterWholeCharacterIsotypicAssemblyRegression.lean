import Synthesis.MonsterWholeCharacterIsotypicAssembly

/-!
Regression consumer for the generic semisimple/isotypic assembly used by the
Monster 3B whole-character route.

This contains no Monster-specific identification.  It exercises both the
proof-relevant classifier -> finite-copy linear-equivalence theorem and the
lawful post-recognition copy-count cancellation theorem.
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

section CopyCount

variable {k V H : Type u}
variable [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup H] [Module k H] [FiniteDimensional k H]

example {n target : ℕ}
    (e : V ≃ₗ[k] (Fin n → H))
    (hH : 0 < Module.finrank k H)
    (hV : Module.finrank k V = target * Module.finrank k H) :
    n = target := by
  exact finiteCopyCountOfFinrankRatio e hH hV

end CopyCount

end

end Synthesis
