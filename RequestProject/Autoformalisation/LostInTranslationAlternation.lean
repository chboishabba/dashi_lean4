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

/-!
## Source-exact A.4a/b quantifier parity and finite 9-witness block

For level l>=2, the prefix is Q₂ ... Q_(l-1), with
Q_j = ∀ when j even, ∃ when j odd. In the final block the paper
uses ∀x Q≠0 for EVEN l and ∃x Q=0 for ODD l.
The predicate supplied below is source-shaped, not a proof of
Sigma^0_l completeness or of effective polynomial enumeration.
-/

/-- Boolean true=exists, false=forall; index i refers to Q_(i+2). -/
def sourceAlternationPrefix (level : ℕ) : List Bool :=
  (List.range (level - 2)).map
    (fun i => (i + 2) % 2 == 1)

/-- A.4a/b with the exact source alternation and exactly nine final
natural variables. General k>=9 needs source-preserving padding. -/
def sourceA4Predicate
    (level : ℕ) (Q : ℕ → List ℕ → (Fin 9 → ℕ) → ℤ)
    (n : ℕ) : Prop :=
  quantifyPrefix (sourceAlternationPrefix level)
    (fun zs =>
      if level % 2 == 0 then
        ∀ x : Fin 9 → ℕ, Q n zs x ≠ 0
      else
        ∃ x : Fin 9 → ℕ, Q n zs x = 0)

/-- Source has exactly (l-2) intermediate quantifier variables. -/
theorem sourceAlternationPrefix_length (level : ℕ) :
    (sourceAlternationPrefix level).length = level - 2 := by
  simp [sourceAlternationPrefix]

/-- Theorem A.4 states the level-two base case is A.3. -/
theorem source_A4_level_two_is_A3
    (Q : ℕ → List ℕ → (Fin 9 → ℕ) → ℤ)
    (n : ℕ) :
    sourceA4Predicate 2 Q n ↔
      ∀ x : Fin 9 → ℕ, Q n [] x ≠ 0 := by
  rfl

/-- Odd level three: Q₂ universal, then a final existential block. -/
theorem source_A4_level_three_shape
    (Q : ℕ → List ℕ → (Fin 9 → ℕ) → ℤ)
    (n : ℕ) :
    sourceA4Predicate 3 Q n ↔
      ∀ z₂ : ℕ, ∃ x : Fin 9 → ℕ,
        Q n [z₂] x = 0 := by
  rfl

/-- Even level four: Q₂ universal then Q₃ existential, followed
by a universal non-root block. -/
theorem source_A4_level_four_shape
    (Q : ℕ → List ℕ → (Fin 9 → ℕ) → ℤ)
    (n : ℕ) :
    sourceA4Predicate 4 Q n ↔
      ∀ z₂ : ℕ, ∃ z₃ : ℕ,
        ∀ x : Fin 9 → ℕ,
          Q n [z₂, z₃] x ≠ 0 := by
  rfl

end RequestProject.Autoformalisation.LostInTranslationAlternation
