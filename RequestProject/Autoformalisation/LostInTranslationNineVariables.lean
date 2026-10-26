import Mathlib

/-!
# BCH2026 Appendix A.3: exact nine-variable logical reduction

Original theorem, argument and computational genealogy:
Alexander Bastounis, Fabian Circelli and Anders C. Hansen,
arXiv:2610.08144v1 (2026-10-06), Appendix A.2,
Theorem A.3, and the original DPRM/nine-unknown predecessors.

This file proves the **LOGICAL** core from a supplied source-faithful
nine-natural-variable Diophantine encoding, preserving ∃n∀x and its
alternation. No computable polynomial enumeration, nine-variable
DPRM construction, effective code map, Sigma^0_2 completeness,
strictness theorem or SCI=infinity is asserted or manufactured.

The precise open input is
  Halts e n ↔ ∃ x : Fin 9 → Nat, Q e n x = 0.
If an actual original source owner pays this with an integer polynomial
and a *computable* index transformation, the propositional reduction
below can be applied. Semantic DPRM by Cameron Freer provides some
witness arity k; it does not automatically instantiate k=9.
-/

namespace RequestProject.Autoformalisation.LostInTranslationNineVariables

/-- A fixed nine-unknown relation representing halting when an actual
source-specific polynomial Q exists. This is only an abstract function
until polynomiality/effective coding are supplied. -/
def NineVariableRoot
    (Q : ℕ → ℕ → (Fin 9 → ℕ) → ℤ) (e n : ℕ) : Prop :=
  ∃ x : Fin 9 → ℕ, Q e n x = 0

def NineVariableNoRoot
    (Q : ℕ → ℕ → (Fin 9 → ℕ) → ℤ) (e n : ℕ) : Prop :=
  ∀ x : Fin 9 → ℕ, Q e n x ≠ 0

/-- Exactly the first-order equivalence between no root and the
negation of an existential nine-variable root. -/
theorem not_nine_root_iff_all_nonzero
    (Q : ℕ → ℕ → (Fin 9 → ℕ) → ℤ) (e n : ℕ) :
    ¬ NineVariableRoot Q e n ↔ NineVariableNoRoot Q e n := by
  constructor
  · intro h x hx
    apply h
    exact ⟨x, hx⟩
  · intro h ⟨x, hx⟩
    exact h x hx

/-- This is the BCH source's NTOT **shape**, not a theorem that a
particular universal computation is non-total. -/
def SomeInputDoesNotHalt (Halts : ℕ → ℕ → Prop) (e : ℕ) : Prop :=
  ∃ n : ℕ, ¬ Halts e n

/-- Exactly the d={e | ∃n B_e(n)} pattern in source A.3,
assuming the original Diophantine coding has been provided. -/
def SomeInputHasNoRoot
    (Q : ℕ → ℕ → (Fin 9 → ℕ) → ℤ) (e : ℕ) : Prop :=
  ∃ n : ℕ, NineVariableNoRoot Q e n

/-- The finite logical heart of the original paper's A.3 reduction.
NO source-to-polynomial code compiler is constructed by this theorem. -/
theorem semantic_reduction_at_nine_variables
    (Halts : ℕ → ℕ → Prop)
    (Q : ℕ → ℕ → (Fin 9 → ℕ) → ℤ)
    (hDPRMNine : ∀ e n, Halts e n ↔ NineVariableRoot Q e n)
    (e : ℕ) :
    SomeInputDoesNotHalt Halts e ↔ SomeInputHasNoRoot Q e := by
  constructor
  · rintro ⟨n, hDoesNotHalt⟩
    refine ⟨n, ?_⟩
    apply (not_nine_root_iff_all_nonzero Q e n).mp
    intro hRoot
    exact hDoesNotHalt ((hDPRMNine e n).mpr hRoot)
  · rintro ⟨n, hNoRoot⟩
    refine ⟨n, ?_⟩
    intro hHalt
    have hRoot := (hDPRMNine e n).mp hHalt
    exact (not_nine_root_iff_all_nonzero Q e n).mpr hNoRoot hRoot

/-!
The source's *effective* reduction furthermore needs a computable
function e ↦ index(p_e), with equality of the encoded integer-polynomial
coefficients in the chosen enumeration. Our Q is a mathematical function;
this theorem alone supplies neither effective indices nor Σ^0_2-hardness.
-/

end RequestProject.Autoformalisation.LostInTranslationNineVariables
