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

/-!
## Appendix A.3: exact enumeration-index search and target equivalence

The paper selects t(e)=μj[enum(j) has exactly the same polynomial
coefficients as specialised q(e,n,x)]; total computable indexing
uses two independent inputs: an effective enumeration/equality test and
surjectivity. We prove index correctness and the membership reduction,
but not the computability of the selected index.

A generic Code may be specialised to integer polynomial syntax by
a later donor. Genericity itself supplies no polynomiality.
-/

/-- A least source index from an actual surjectivity proof.
No algorithmic computability of this search is claimed. -/
noncomputable def sourceIndex
    {Code : Type*} (enumeration : ℕ → Code)
    (target : ℕ → Code)
    (hSurjective : Function.Surjective enumeration)
    (e : ℕ) : ℕ := by
  classical
  exact Nat.find (hSurjective (target e))

theorem sourceIndex_identifies_source_code
    {Code : Type*} (enumeration : ℕ → Code)
    (target : ℕ → Code)
    (hSurjective : Function.Surjective enumeration)
    (e : ℕ) :
    enumeration (sourceIndex enumeration target hSurjective e) =
      target e := by
  classical
  exact Nat.find_spec (hSurjective (target e))

/-- The selected matching coefficient-code index is also least, as
required by the source's μ-operator. Classical leastness is a
mathematical fact and still does NOT prove computability of μ-search. -/
theorem sourceIndex_is_least_matching_code
    {Code : Type*} (enumeration : ℕ → Code)
    (target : ℕ → Code)
    (hSurjective : Function.Surjective enumeration)
    (e j : ℕ) (hMatch : enumeration j = target e) :
    sourceIndex enumeration target hSurjective e ≤ j := by
  classical
  exact Nat.find_min' (hSurjective (target e)) hMatch

/-- Original d shape, evaluated on a chosen enumeration code. -/
def IndexedNoRoot
    {Code : Type*}
    (enumeration : ℕ → Code)
    (root : Code → ℕ → Prop) (index : ℕ) : Prop :=
  ∃ n : ℕ, ¬ root (enumeration index) n

/-- The exact source index t(e) transports the NTOT predicate to d,
given a source-specific halting-root representation.
No effective mapping is constructed or inferred. -/
theorem sourceIndex_preserves_nontermination_membership
    {Code : Type*} (enumeration : ℕ → Code)
    (target : ℕ → Code)
    (hSurjective : Function.Surjective enumeration)
    (root : Code → ℕ → Prop) (Halts : ℕ → ℕ → Prop)
    (hRepresentation :
      ∀ e n, Halts e n ↔ root (target e) n)
    (e : ℕ) :
    SomeInputDoesNotHalt Halts e ↔
      IndexedNoRoot enumeration root
        (sourceIndex enumeration target hSurjective e) := by
  constructor
  · rintro ⟨n, hNotHalts⟩
    refine ⟨n, ?_⟩
    rw [sourceIndex_identifies_source_code
      enumeration target hSurjective e]
    intro hRoot
    exact hNotHalts ((hRepresentation e n).mpr hRoot)
  · rintro ⟨n, hNotRoot⟩
    refine ⟨n, ?_⟩
    intro hHalts
    apply hNotRoot
    rw [sourceIndex_identifies_source_code
      enumeration target hSurjective e]
    exact (hRepresentation e n).mp hHalts

/-!
## Appendix A.3: instantiate the source enumeration with real polynomials

The paper's source index enumerates INTEGER-COEFFICIENT POLYNOMIALS
in (n,x₁,...,x₉), not abstract codes. The type below pays that
syntactic polynomial requirement by using Mathlib's MvPolynomial.
What remains unpaid is the explicit computable enumeration, the
specialisation of a nine-unknown universal polynomial, and a
computable-index-search theorem. Do NOT promote a noncomputable
Nat.find to a verified Turing reduction.
-/

/-- A genuine integer-coefficient 10-variable polynomial with
one distinguished natural parameter and nine natural root variables. -/
def IntegerPolynomialRoot
    (P : MvPolynomial (Fin 1 ⊕ Fin 9) ℤ) (n : ℕ) : Prop :=
  ∃ x : Fin 9 → ℕ,
    MvPolynomial.eval
      (Sum.elim (fun _ : Fin 1 => (n : ℤ))
        (fun i : Fin 9 => (x i : ℤ))) P = 0

/-- Instantiates the earlier exact index search at the PAPER's
polynomial source type. The source's nine-variable DPRM and
computable enumeration premises remain external/visible. -/
theorem polynomial_index_reduces_ntot_if_representation_is_paid
    (enumeration : ℕ → MvPolynomial (Fin 1 ⊕ Fin 9) ℤ)
    (hSurj : Function.Surjective enumeration)
    (specialized : ℕ → MvPolynomial (Fin 1 ⊕ Fin 9) ℤ)
    (Halts : ℕ → ℕ → Prop)
    (hNineVariablePolynomial :
      ∀ e n, Halts e n ↔ IntegerPolynomialRoot (specialized e) n)
    (e : ℕ) :
    SomeInputDoesNotHalt Halts e ↔
      IndexedNoRoot enumeration IntegerPolynomialRoot
        (sourceIndex enumeration specialized hSurj e) := by
  exact sourceIndex_preserves_nontermination_membership
    enumeration specialized hSurj IntegerPolynomialRoot
    Halts hNineVariablePolynomial e

end RequestProject.Autoformalisation.LostInTranslationNineVariables
