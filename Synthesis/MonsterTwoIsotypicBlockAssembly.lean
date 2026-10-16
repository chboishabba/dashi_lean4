import Synthesis.MonsterWholeCharacterIsotypicAssembly
import Mathlib.LinearAlgebra.Projection

/-!
# Complementary two-isotypic block assembly

Generic tail used by the Monster 3B multiplicity route after the two actual
isotypic blocks have been recognized on the same representation.

This file deliberately does not obtain those blocks from character-table labels
or dimensions.  It consumes a proof that the two submodules are complementary
and a proof-relevant simple-type classifier on each block, then reuses the
one-type isotypic assembler and the standard `Submodule.prodEquivOfIsCompl`.
-/

namespace Synthesis

noncomputable section

universe u

variable {R M T S : Type u}
variable [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup T] [Module R T]
variable [AddCommGroup S] [Module R S]

/-- A paid complementary pair is already an actual linear direct-sum
presentation of the ambient module. -/
theorem twoBlockLinearEquiv
    (A B : Submodule R M) (hcompl : IsCompl A B) :
    M ≃ₗ[R] (A × B) :=
  (A.prodEquivOfIsCompl B hcompl).symm

/-- If each member of a complementary pair is semisimple, finite, and has one
proof-relevantly classified simple type, assemble the ambient module as finite
copies of those two types.

For the Monster consumer this is the generic tail *after* the actual 12-family
and 78-family submodules and their complementarity have been paid. -/
theorem finiteCopiesOfTwoComplementarySimpleTypes
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
  obtain ⟨n, ⟨eA⟩⟩ := finiteCopiesOfOneSimpleType classifyA
  obtain ⟨m, ⟨eB⟩⟩ := finiteCopiesOfOneSimpleType classifyB
  exact ⟨n, m, ⟨twoBlockLinearEquiv A B hcompl ≪≫ₗ
    LinearEquiv.prodCongr eA eB⟩⟩

end

end Synthesis
