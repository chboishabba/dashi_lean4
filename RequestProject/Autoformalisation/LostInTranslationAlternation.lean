import Mathlib

/-!
# BCH2026 Appendix A.4: parity-preserving final Diophantine block

Original: Bastounis, Circelli, Hansen, arXiv:2610.08144v1,
Appendix A, Theorem A.4. This DASHI reconstruction proves that
replacing the last block by a semantically equivalent nine-variable
polynomial block preserves an existing quantifier prefix. It does
not construct the source's DPRM polynomial, effective index reduction,
Sigma^0_l completeness or SCI hierarchy.
-/

namespace RequestProject.Autoformalisation.LostInTranslationAlternation

/-- A reusable ordered quantifier prefix. True = existential,
false = universal; the particular source alternation is specified
by the consumer. -/
def quantifyPrefix : List Bool → (List ℕ → Prop) → Prop
  | [], P => P []
  | true :: rest, P =>
      ∃ x : ℕ, quantifyPrefix rest (fun ys => P (x :: ys))
  | false :: rest, P =>
      ∀ x : ℕ, quantifyPrefix rest (fun ys => P (x :: ys))

/-- Pointwise equivalence survives any *existing* prefix. -/
theorem quantifyPrefix_congr
    (prefix : List Bool) (P Q : List ℕ → Prop)
    (h : ∀ xs : List ℕ, P xs ↔ Q xs) :
    quantifyPrefix prefix P ↔ quantifyPrefix prefix Q := by
  induction prefix generalizing P Q with
  | nil =>
      exact h []
  | cons b rest ih =>
      cases b with
      | false =>
          simp only [quantifyPrefix]
          constructor
          · intro hp x
            exact (ih _ _ (fun ys => h (x :: ys))).mp (hp x)
          · intro hq x
            exact (ih _ _ (fun ys => h (x :: ys))).mpr (hq x)
      | true =>
          simp only [quantifyPrefix]
          constructor
          · rintro ⟨x, hx⟩
            exact ⟨x, (ih _ _ (fun ys => h (x :: ys))).mp hx⟩
          · rintro ⟨x, hx⟩
            exact ⟨x, (ih _ _ (fun ys => h (x :: ys))).mpr hx⟩

/-- Existential nine-variable Diophantine substitution, conditional
on an actual polynomial representation at every prefix assignment. -/
theorem final_exists_of_nine_variable_representation
    (prefix : List Bool) (C : List ℕ → Prop)
    (Q : List ℕ → (Fin 9 → ℕ) → ℤ)
    (hRepresentation :
      ∀ xs : List ℕ, C xs ↔ ∃ z : Fin 9 → ℕ, Q xs z = 0) :
    quantifyPrefix prefix C ↔
      quantifyPrefix prefix
        (fun xs => ∃ z : Fin 9 → ℕ, Q xs z = 0) :=
  quantifyPrefix_congr prefix _ _ hRepresentation

/-- The negated final existential block corresponds to a universal
nine-variable non-root condition, leaving the prefix unchanged. -/
theorem final_forall_of_nine_variable_representation
    (prefix : List Bool) (C : List ℕ → Prop)
    (Q : List ℕ → (Fin 9 → ℕ) → ℤ)
    (hRepresentation :
      ∀ xs : List ℕ, C xs ↔ ∃ z : Fin 9 → ℕ, Q xs z = 0) :
    quantifyPrefix prefix (fun xs => ¬ C xs) ↔
      quantifyPrefix prefix
        (fun xs => ∀ z : Fin 9 → ℕ, Q xs z ≠ 0) := by
  apply quantifyPrefix_congr
  intro xs
  constructor
  · intro hNoC z hz
    exact hNoC ((hRepresentation xs).mpr ⟨z, hz⟩)
  · intro hNoRoot hC
    obtain ⟨z, hz⟩ := (hRepresentation xs).mp hC
    exact hNoRoot z hz

end RequestProject.Autoformalisation.LostInTranslationAlternation
