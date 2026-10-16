import Synthesis.MonsterTwoIsotypicBlockAssembly

/-!
Regression consumer for the generic two-block semisimple assembler used after
actual 12/78 multiplicity block recognition.
-/

namespace Synthesis

noncomputable section

universe u

variable {R M T S : Type u}
variable [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup T] [Module R T]
variable [AddCommGroup S] [Module R S]

example
    (A B : Submodule R M)
    [IsSemisimpleModule R A] [Module.Finite R A]
    [IsSemisimpleModule R B] [Module.Finite R B]
    (hcompl : IsCompl A B)
    (classifyA :
      ∀ (m : Submodule R A), [IsSimpleModule R m] →
        Nonempty (m ≃ₗ[R] T))
    (classifyB :
      ∀ (m : Submodule R B), [IsSimpleModule R m] →
        Nonempty (m ≃ₗ[R] S)) :
    ∃ n m : ℕ,
      Nonempty (M ≃ₗ[R] ((Fin n → T) × (Fin m → S))) := by
  exact finiteCopiesOfTwoComplementarySimpleTypes A B hcompl classifyA classifyB

end

end Synthesis
