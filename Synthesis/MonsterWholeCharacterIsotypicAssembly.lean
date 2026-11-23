import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Generic semisimple isotypic assembly

This is the representation-independent assembly leaf shared by the Monster 3B
whole-character H_zeta route and by later multiplicity decompositions.

The input is deliberately the proof-relevant statement that every simple
submodule of a finite semisimple module has one fixed module type.  Mathlib's
`IsIsotypicOfType.linearEquiv_fun` then supplies an actual finite-copy linear
equivalence.  Character arithmetic, dimensions, labels and source citations do
not manufacture the classifier consumed here.
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

/-- Assemble a finite direct-copy presentation once every simple submodule of
`M` has been classified as the same simple type `S`.

This theorem owns only the generic semisimple assembly.  In the Monster 3B
consumer, proving `classify` on the *actual restricted sector* is the separate
same-object representation payment. -/
theorem finiteCopiesOfOneSimpleType
    (classify :
      ∀ (m : Submodule R M), [IsSimpleModule R m] →
        Nonempty (m ≃ₗ[R] S)) :
    ∃ n : ℕ, Nonempty (M ≃ₗ[R] (Fin n → S)) := by
  let h : IsIsotypicOfType R M S := fun m _ => classify m
  exact h.linearEquiv_fun

/-- Expose the intermediate `IsIsotypicOfType` witness separately for consumers
that need module-level isotypic structure before choosing finite coordinates. -/
theorem isIsotypicOfTypeOfSimpleTypeClassifier
    (classify :
      ∀ (m : Submodule R M), [IsSimpleModule R m] →
        Nonempty (m ≃ₗ[R] S)) :
    IsIsotypicOfType R M S := by
  intro m _
  exact classify m

end

end Synthesis
