import Mathlib

/-!
# BCH2026 Appendix A.4: parity-preserving Diophantine final blocks

Original mathematical source: Alexander Bastounis, Fabian Circelli,
Anders C. Hansen, arXiv:2610.08144v1 (2026-10-06), Theorem A.4.
Original numerical-variable restriction: k >= 9. This file proves
source-shaped statements at k=9, with a *real integer polynomial* in
one distinguished input n, the l-2 prefix variables, and nine final
root variables. It does NOT prove the uniform effective polynomial
construction, Sigma^0_l completeness, or SCI=infinity. General k>=9
requires a separate source-preserving parameterisation/padding lemma.

The generic congruence theorem below preserves quantifier-prefix
semantics. Crucially, a *function* Q(xs,z) can encode any predicate
using a case split and would not be a DPRM representation. Therefore
all the source-specific final blocks are now restricted to actual
MvPolynomial values with fixed coefficients, independent of the
individual assignments n, prefix variables and root variables.
-/

namespace RequestProject.Autoformalisation.LostInTranslationAlternation

/-- Ordered prefix: true = existential; false = universal. -/
def quantifyPrefix : List Bool → (List ℕ → Prop) → Prop
  | [], P => P []
  | true :: rest, P =>
      ∃ x : ℕ, quantifyPrefix rest (fun ys => P (x :: ys))
  | false :: rest, P =>
      ∀ x : ℕ, quantifyPrefix rest (fun ys => P (x :: ys))

/-- Any *pointwise* equivalence survives an unchanged quantifier prefix.
This does not by itself prove either predicate is Diophantine. -/
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

/-- A quantifier-prefix consumer cannot access malformed-length
assignments: this eliminates a potential *new* default-value trap in
the source-level MvPolynomial evaluator. Two predicates that agree on
assignments of the actual prefix length are indistinguishable under
that prefix, even if they differ on arbitrary other lists. -/
theorem quantifyPrefix_congr_at_valid_length
    (prefix : List Bool) (P Q : List ℕ → Prop)
    (h : ∀ zs : List ℕ,
      zs.length = prefix.length → (P zs ↔ Q zs)) :
    quantifyPrefix prefix P ↔ quantifyPrefix prefix Q := by
  induction prefix generalizing P Q with
  | nil =>
      exact h [] rfl
  | cons b rest ih =>
      cases b with
      | false =>
          change (∀ x : ℕ, quantifyPrefix rest (fun ys => P (x :: ys))) ↔
            (∀ x : ℕ, quantifyPrefix rest (fun ys => Q (x :: ys)))
          constructor
          · intro hp x
            have hx : ∀ ys : List ℕ, ys.length = rest.length →
                (P (x :: ys) ↔ Q (x :: ys)) := by
              intro ys hlen
              exact h (x :: ys) (by simp [hlen])
            exact (ih _ _ hx).mp (hp x)
          · intro hq x
            have hx : ∀ ys : List ℕ, ys.length = rest.length →
                (P (x :: ys) ↔ Q (x :: ys)) := by
              intro ys hlen
              exact h (x :: ys) (by simp [hlen])
            exact (ih _ _ hx).mpr (hq x)
      | true =>
          change (∃ x : ℕ, quantifyPrefix rest (fun ys => P (x :: ys))) ↔
            (∃ x : ℕ, quantifyPrefix rest (fun ys => Q (x :: ys)))
          constructor
          · rintro ⟨x, hp⟩
            have hx : ∀ ys : List ℕ, ys.length = rest.length →
                (P (x :: ys) ↔ Q (x :: ys)) := by
              intro ys hlen
              exact h (x :: ys) (by simp [hlen])
            exact ⟨x, (ih _ _ hx).mp hp⟩
          · rintro ⟨x, hq⟩
            have hx : ∀ ys : List ℕ, ys.length = rest.length →
                (P (x :: ys) ↔ Q (x :: ys)) := by
              intro ys hlen
              exact h (x :: ys) (by simp [hlen])
            exact ⟨x, (ih _ _ hx).mpr hq⟩

/-- Q₂=∀, Q₃=∃, alternating thereafter; prefix length is l-2. -/
def sourceAlternationPrefix (level : ℕ) : List Bool :=
  (List.range (level - 2)).map
    (fun i => (i + 2) % 2 == 1)

theorem sourceAlternationPrefix_length (level : ℕ) :
    (sourceAlternationPrefix level).length = level - 2 := by
  simp [sourceAlternationPrefix]

/-- One actual INTEGER-COEFFICIENT polynomial in: distinguished n,
the l-2 intermediate quantified variables, and nine final variables.
The coefficient syntax P cannot vary with the sample assignments.
For malformed lists, out-of-bounds prefix variables default to 0;
only the source-shaped full-length prefix is consumed below. -/
def evalSourceA4Polynomial
    (level : ℕ)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) (zs : List ℕ) (x : Fin 9 → ℕ) : ℤ :=
  MvPolynomial.eval
    (Sum.elim
      (fun _ : Fin 1 => (n : ℤ))
      (Sum.elim
        (fun i : Fin (level - 2) => ((zs.getD i.val 0 : ℕ) : ℤ))
        (fun i : Fin 9 => (x i : ℤ)))) P

/-- Under the valid source prefix length, every source-variable
index is actually in range. The List.getD fallback used above cannot
be reached by any valid prefix assignment. -/
theorem sourceA4_prefix_coordinate_in_bounds
    (level : ℕ) (zs : List ℕ)
    (hLength : zs.length = level - 2)
    (i : Fin (level - 2)) :
    i.val < zs.length := by
  simpa only [hLength] using i.isLt

/-- Consequently evaluation uses the ACTUAL source coordinate, not an
unjustified manufactured zero. The explicit length witness is essential. -/
theorem sourceA4_prefix_getD_agrees_with_actual
    (level : ℕ) (zs : List ℕ)
    (hLength : zs.length = level - 2)
    (i : Fin (level - 2)) :
    zs.getD i.val 0 =
      zs[i.val]'(sourceA4_prefix_coordinate_in_bounds level zs hLength i) := by
  exact List.getD_eq_getElem zs 0
    (sourceA4_prefix_coordinate_in_bounds level zs hLength i)

/-- Even level: universal nonroot final block; odd level:
existential polynomial-root final block. `P` is syntactic polynomial
source code, unlike a case-defined function that smuggles C in. -/
def sourceA4Predicate
    (level : ℕ)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) : Prop :=
  quantifyPrefix (sourceAlternationPrefix level)
    (fun zs =>
      if level % 2 == 0 then
        ∀ x : Fin 9 → ℕ, evalSourceA4Polynomial level P n zs x ≠ 0
      else
        ∃ x : Fin 9 → ℕ, evalSourceA4Polynomial level P n zs x = 0)

/-- Pointwise source-to-Diophantine representation, including a fixed
polynomial P, survives an arbitrary prefix. This is only conditional
on the separately provided representation theorem. -/
theorem final_exists_of_nine_variable_representation
    (level : ℕ) (prefix : List Bool) (C : List ℕ → Prop)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ)
    (hRepresentation :
      ∀ zs : List ℕ,
        C zs ↔ ∃ x : Fin 9 → ℕ,
          evalSourceA4Polynomial level P n zs x = 0) :
    quantifyPrefix prefix C ↔
      quantifyPrefix prefix
        (fun zs => ∃ x : Fin 9 → ℕ,
          evalSourceA4Polynomial level P n zs x = 0) :=
  quantifyPrefix_congr prefix _ _ hRepresentation

/-- Negating the final existential polynomial-root block produces
the universal non-root block under the same outer prefix. -/
theorem final_forall_of_nine_variable_representation
    (level : ℕ) (prefix : List Bool) (C : List ℕ → Prop)
    (P : MvPolynomial (Fin 1 ⊕ (Fin (level - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ)
    (hRepresentation :
      ∀ zs : List ℕ,
        C zs ↔ ∃ x : Fin 9 → ℕ,
          evalSourceA4Polynomial level P n zs x = 0) :
    quantifyPrefix prefix (fun zs => ¬ C zs) ↔
      quantifyPrefix prefix
        (fun zs => ∀ x : Fin 9 → ℕ,
          evalSourceA4Polynomial level P n zs x ≠ 0) := by
  apply quantifyPrefix_congr
  intro zs
  constructor
  · intro hNoC x hx
    exact hNoC ((hRepresentation zs).mpr ⟨x, hx⟩)
  · intro hNoRoot hC
    obtain ⟨x, hx⟩ := (hRepresentation zs).mp hC
    exact hNoRoot x hx

/-- A.4 level two recovers the A.3 universal non-root block. -/
theorem source_A4_level_two_is_A3
    (P : MvPolynomial (Fin 1 ⊕ (Fin (2 - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) :
    sourceA4Predicate 2 P n ↔
      ∀ x : Fin 9 → ℕ,
        evalSourceA4Polynomial 2 P n [] x ≠ 0 := by
  rfl

/-- The odd level-three outer Q₂ is universal. -/
theorem source_A4_level_three_shape
    (P : MvPolynomial (Fin 1 ⊕ (Fin (3 - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) :
    sourceA4Predicate 3 P n ↔
      ∀ z₂ : ℕ, ∃ x : Fin 9 → ℕ,
        evalSourceA4Polynomial 3 P n [z₂] x = 0 := by
  rfl

/-- The even level-four prefix is Q₂=∀, Q₃=∃. -/
theorem source_A4_level_four_shape
    (P : MvPolynomial (Fin 1 ⊕ (Fin (4 - 2) ⊕ Fin 9)) ℤ)
    (n : ℕ) :
    sourceA4Predicate 4 P n ↔
      ∀ z₂ : ℕ, ∃ z₃ : ℕ,
        ∀ x : Fin 9 → ℕ,
          evalSourceA4Polynomial 4 P n [z₂, z₃] x ≠ 0 := by
  rfl

end RequestProject.Autoformalisation.LostInTranslationAlternation
