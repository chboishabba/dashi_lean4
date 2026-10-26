import Mathlib
import RequestProject.Autoformalisation.LostInTranslationAlternation

/-!
# BCH2026 Appendix A.4: extending nine natural witnesses to k >= 9

Original nine-*natural-number* Diophantine representation: James P.
Jones, "Universal diophantine equation", J. Symbolic Logic 47(3)
(1982), 549–571, DOI 10.2307/2273588, building on work by
Matiyasevich and prior DPRM authors. Bastounis/Circelli/Hansen (2026),
arXiv:2610.08144v1, Theorem A.4, requires every k >= 9.

This DASHI lemma proves that padding a nine-tuple with irrelevant
coordinates preserves both existential-root and universal-nonroot
SEMANTICS. We instantiate it on the genuine integer `MvPolynomial`
source evaluator in `LostInTranslationAlternation`. Formally
constructing a renamed polynomial of arity k and an *effective*
integer coefficient-code compiler is still separate; this is
not a proof of Σ_l-completeness or SCI infinity.
-/

namespace RequestProject.Autoformalisation.LostInTranslationPadding

open RequestProject.Autoformalisation.LostInTranslationAlternation

/-- Embed a nine-element natural tuple into a k-element tuple, setting
the additional k-9 coordinates to zero. -/
def liftNine (k : ℕ) (hk : 9 ≤ k)
    (x : Fin 9 → ℕ) : Fin k → ℕ :=
  fun i => if hi : i.val < 9 then x ⟨i.val, hi⟩ else 0

/-- Restricting that tuple to the first nine entries recovers the
original values exactly: no defaulted source coordinate is introduced. -/
theorem take_liftNine (k : ℕ) (hk : 9 ≤ k)
    (x : Fin 9 → ℕ) :
    Fin.take 9 hk (liftNine k hk x) = x := by
  funext i
  simp [Fin.take, liftNine, i.isLt]

/-- An arbitrary predicate on the first nine coordinates has the
same existential witness status after padding with k-9 extras. -/
theorem existential_nine_iff_k_padding
    (k : ℕ) (hk : 9 ≤ k) (P : (Fin 9 → ℕ) → Prop) :
    (∃ x : Fin 9 → ℕ, P x) ↔
      (∃ y : Fin k → ℕ, P (Fin.take 9 hk y)) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨liftNine k hk x, ?_⟩
    rw [take_liftNine]
    exact hx
  · rintro ⟨y, hy⟩
    exact ⟨Fin.take 9 hk y, hy⟩

/-- The corresponding universal prefix preserves the no-root test. -/
theorem universal_nine_iff_k_padding
    (k : ℕ) (hk : 9 ≤ k) (P : (Fin 9 → ℕ) → Prop) :
    (∀ x : Fin 9 → ℕ, P x) ↔
      (∀ y : Fin k → ℕ, P (Fin.take 9 hk y)) := by
  constructor
  · intro h y
    exact h (Fin.take 9 hk y)
  · intro h x
    simpa only [take_liftNine] using h (liftNine k hk x)

/-- Applied to the exact source polynomial, an existential root test
has the same truth value for k>=9 after ignoring excess variables.
This theorem does NOT construct an arity-k polynomial's code. -/
theorem source_polynomial_exists_padding
    (level k : ℕ) (hk : 9 ≤ k)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) (zs : List ℕ) :
    (∃ x : Fin 9 → ℕ,
       evalSourceA4Polynomial level P n zs x = 0) ↔
    (∃ y : Fin k → ℕ,
       evalSourceA4Polynomial level P n zs
         (Fin.take 9 hk y) = 0) := by
  exact existential_nine_iff_k_padding k hk
    (fun x => evalSourceA4Polynomial level P n zs x = 0)

/-- The universal non-root test has the same preserved source
semantics. Actual polynomial-code renaming is an OPEN producer. -/
theorem source_polynomial_forall_padding
    (level k : ℕ) (hk : 9 ≤ k)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) (zs : List ℕ) :
    (∀ x : Fin 9 → ℕ,
       evalSourceA4Polynomial level P n zs x ≠ 0) ↔
    (∀ y : Fin k → ℕ,
       evalSourceA4Polynomial level P n zs
         (Fin.take 9 hk y) ≠ 0) := by
  exact universal_nine_iff_k_padding k hk
    (fun x => evalSourceA4Polynomial level P n zs x ≠ 0)

/-!
## Real arity-k polynomial syntax, not only nine-coordinate predicates

Mathlib's `MvPolynomial.rename` maps the nine root-variable names
into the first nine coordinates of the larger k-variable block.
This produces an ACTUAL integer-coefficient k-root-variable polynomial,
whose evaluation is precisely the original nine-variable evaluation
at the first nine tuple entries. The computability of a matching
source polynomial-code enumeration remains a separate obligation.
-/

/-- Variable-map respecting the distinguished n, all intermediate
prefix variables, and the first nine final root coordinates. -/
def sourceNineToKVariableMap (level k : ℕ) (hk : 9 ≤ k) :
    (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) →
      (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin k))
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl i)
  | Sum.inr (Sum.inr i) =>
      Sum.inr (Sum.inr (Fin.castLE hk i))

/-- A GENUINE integer-coefficient polynomial with k>=9 final
variables, not an arbitrary predicate or oracle Q. -/
noncomputable def padPolynomial
    (level k : ℕ) (hk : 9 ≤ k)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ) :
    MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin k)) ℤ :=
  MvPolynomial.rename (sourceNineToKVariableMap level k hk) P

/-- Evaluate an honest k-final-variable polynomial at fixed source
input and actual prefix values. -/
def evalSourcePolynomialK
    (level k : ℕ)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin k)) ℤ)
    (n : ℕ) (zs : List ℕ) (y : Fin k → ℕ) : ℤ :=
  MvPolynomial.eval
    (Sum.elim
      (fun _ : Fin 1 => (n : ℤ))
      (Sum.elim
        (fun i : Fin (level - 2) => ((zs.getD i.val 0 : ℕ) : ℤ))
        (fun i : Fin k => (y i : ℤ)))) P

/-- Renaming variables truly preserves polynomial evaluation. This is
Mathlib's original `MvPolynomial.eval_rename` theorem, not
a bespoke new proof of DPRM's polynomial representation. -/
theorem eval_padPolynomial_eq_first_nine
    (level k : ℕ) (hk : 9 ≤ k)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) (zs : List ℕ) (y : Fin k → ℕ) :
    evalSourcePolynomialK level k (padPolynomial level k hk P) n zs y =
      evalSourceA4Polynomial level P n zs (Fin.take 9 hk y) := by
  unfold evalSourcePolynomialK padPolynomial evalSourceA4Polynomial
  rw [MvPolynomial.eval_rename]
  congr 1
  funext i
  cases i with
  | inl a => rfl
  | inr j =>
      cases j with
      | inl b => rfl
      | inr c => rfl

/-- The *arity-k integer polynomial* has a natural-number zero iff
the original nine-variable integer polynomial has one. -/
theorem source_polynomial_root_iff_arity_k
    (level k : ℕ) (hk : 9 ≤ k)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) (zs : List ℕ) :
    (∃ x : Fin 9 → ℕ,
      evalSourceA4Polynomial level P n zs x = 0) ↔
    (∃ y : Fin k → ℕ,
      evalSourcePolynomialK level k
        (padPolynomial level k hk P) n zs y = 0) := by
  simpa only [eval_padPolynomial_eq_first_nine] using
    (source_polynomial_exists_padding level k hk P n zs)

/-- The universal non-root arity-k statement is equally preserved.
For full A.4, these equivalences compose with `quantifyPrefix_congr`,
provided the same fixed polynomial and source prefix are used. -/
theorem source_polynomial_nonroot_iff_arity_k
    (level k : ℕ) (hk : 9 ≤ k)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) (zs : List ℕ) :
    (∀ x : Fin 9 → ℕ,
      evalSourceA4Polynomial level P n zs x ≠ 0) ↔
    (∀ y : Fin k → ℕ,
      evalSourcePolynomialK level k
        (padPolynomial level k hk P) n zs y ≠ 0) := by
  simpa only [eval_padPolynomial_eq_first_nine] using
    (source_polynomial_forall_padding level k hk P n zs)

end RequestProject.Autoformalisation.LostInTranslationPadding
