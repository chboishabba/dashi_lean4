import Synthesis.MonsterWholeCharacterIsotypicAssembly
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Omega

/-!
# Complementary two-isotypic block assembly

Generic tail used by the Monster 3B multiplicity route after the two actual
isotypic blocks have been recognized on the same representation.

This file deliberately does not obtain those blocks from character-table labels
or dimensions.  It consumes a proof that the two submodules are complementary
and a proof-relevant simple-type classifier on each block, then reuses the
one-type isotypic assembler and the standard `Submodule.prodEquivOfIsCompl`.

A second theorem records the lawful post-recognition arithmetic specific to the
12+78 Monster multiplicity target: after an actual equivalence to finite copies
of 12- and 78-dimensional types exists, ambient finrank 90 forces exactly one
copy of each.  The equation is not allowed to create the two-block recognition.
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

section TwelveSeventyEight

variable {k V T12 T78 : Type u}
variable [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup T12] [Module k T12] [FiniteDimensional k T12]
variable [AddCommGroup T78] [Module k T78] [FiniteDimensional k T78]

/-- Once `V` has actually been recognized as finite copies of the 12- and
78-dimensional types, ambient dimension 90 forces one copy of each.

This is intentionally downstream of `e`; `12 + 78 = 90` alone is not a
representation-recognition theorem. -/
theorem twelveSeventyEightCopyCountsOfFinrank {n m : ℕ}
    (e : V ≃ₗ[k] ((Fin n → T12) × (Fin m → T78)))
    (h12 : Module.finrank k T12 = 12)
    (h78 : Module.finrank k T78 = 78)
    (h90 : Module.finrank k V = 90) :
    n = 1 ∧ m = 1 := by
  have hdim : 12 * n + 78 * m = 90 := by
    have h := e.finrank_eq
    rw [Module.finrank_prod, Module.finrank_pi_fintype,
      Module.finrank_pi_fintype] at h
    simp [h12, h78, h90, Nat.mul_comm] at h ⊢
    exact h.symm
  omega

end TwelveSeventyEight

end

end Synthesis
