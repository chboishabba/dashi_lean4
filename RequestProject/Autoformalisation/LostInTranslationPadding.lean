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

end RequestProject.Autoformalisation.LostInTranslationPadding
