import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Generic semisimple isotypic assembly

This is the representation-independent assembly leaf shared by the Monster 3B
whole-character H_zeta route and by later multiplicity decompositions.

The input is deliberately the proof-relevant statement that every simple
submodule of a finite semisimple module has one fixed module type.  Mathlib's
`IsIsotypicOfType.linearEquiv_fun` then supplies an actual finite-copy linear
equivalence.  Character arithmetic, dimensions, labels and source citations do
not manufacture the classifier consumed here.

Once such a same-object finite-copy equivalence is already present, ordinary
finrank cancellation may lawfully determine the copy count.  This is kept as a
separate post-recognition theorem so a bare numerical identity cannot be used to
manufacture representation identity.
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
consumer, proving `classify` on the actual restricted sector is the separate
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

section CopyCount

variable {k V H : Type u}
variable [Field k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup H] [Module k H] [FiniteDimensional k H]

/-- After an actual finite-copy equivalence has been paid, a nonzero constituent
finrank and the actual ambient/constituent finranks determine the number of
copies by cancellation.

For Monster 3B this is the lawful point at which `65610 = 90 * 729` may select
`90`: only *after* `W_zeta` has been recognized as finite copies of the same
actual `H_zeta`. -/
theorem finiteCopyCountOfFinrankRatio {n target : ℕ}
    (e : V ≃ₗ[k] (Fin n → H))
    (hH : 0 < Module.finrank k H)
    (hV : Module.finrank k V = target * Module.finrank k H) :
    n = target := by
  have hdim : n * Module.finrank k H = target * Module.finrank k H := by
    calc
      n * Module.finrank k H = Module.finrank k (Fin n → H) := by
        rw [Module.finrank_pi_fintype]
        simp
      _ = Module.finrank k V := e.finrank_eq.symm
      _ = target * Module.finrank k H := hV
  exact Nat.mul_right_cancel hH hdim

end CopyCount

end

end Synthesis
