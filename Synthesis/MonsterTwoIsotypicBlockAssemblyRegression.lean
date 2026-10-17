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

section TwelveSeventyEight

variable {k V T12 T78 : Type u}
variable [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup T12] [Module k T12] [FiniteDimensional k T12]
variable [AddCommGroup T78] [Module k T78] [FiniteDimensional k T78]

example {n m : ℕ}
    (e : V ≃ₗ[k] ((Fin n → T12) × (Fin m → T78)))
    (h12 : Module.finrank k T12 = 12)
    (h78 : Module.finrank k T78 = 78)
    (h90 : Module.finrank k V = 90) :
    n = 1 ∧ m = 1 := by
  exact twelveSeventyEightCopyCountsOfFinrank e h12 h78 h90

end TwelveSeventyEight

end

end Synthesis
