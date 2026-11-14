import Mathlib
import RequestProject.Autoformalisation.LostInTranslationExamples

/-!
# BCH2026, Example 4.1: conditional formalisation is not a decision procedure

Original source: Alexander Bastounis, Fabian Circelli, Anders C. Hansen
(2026-10-06), arXiv:2610.08144v1, Example 4.1, Remark 4.2 and A.2.1.

The authors' SCI=infinity claim concerns a TOTAL trustworthiness contract
which, for every source program index, correctly chooses between
a semantically faithful *closed* translation and refusal.

This independent DASHI proof tests the much weaker option of returning
a theorem TEMPLATE which requires an explicit existence proof. This is
semantically meaningful, but does NOT decide if the original ungated
statement is well-defined, nor necessarily meet the paper's TOTAL
translate-or-refuse specification. This is not a refutation of BCH2026.
-/

namespace RequestProject.Autoformalisation.ConditionalTranslation

open RequestProject.Autoformalisation.LostInTranslationExamples

/-- A proof-carrying least number. The existence and minimality both
appear in the type rather than defaulting when a presupposition fails. -/
structure MinimalNatural (P : ℕ → Prop) where
  value : ℕ
  admissible : P value
  minimal : ∀ m, P m → value ≤ m

/-- Denotation as rational is only defined if source supplies an actual
witness for its claimed least natural number. -/
def rationalFromWitness
    {P : ℕ → Prop} (receipt : MinimalNatural P) : ℚ :=
  1 / ((receipt.value : ℚ) + 1)

/-- A reusable conditional proof *template*.
Every particular result can be instantiated only by an actual receipt. -/
theorem square_identity_from_presupposition
    {P : ℕ → Prop} (receipt : MinimalNatural P) :
    (rationalFromWitness receipt + 1) ^ 2 =
      (rationalFromWitness receipt) ^ 2 +
        2 * rationalFromWitness receipt + 1 := by
  ring

/-- Every source predicate has such an if-supplied theorem template;
this does not produce the required receipt and is not an unconditional
proof of the originally intended closed claim. -/
theorem uniform_guarded_template
    (P : ℕ → Prop) :
    ∀ receipt : MinimalNatural P,
      (rationalFromWitness receipt + 1) ^ 2 =
        (rationalFromWitness receipt) ^ 2 +
          2 * rationalFromWitness receipt + 1 :=
  fun receipt => square_identity_from_presupposition receipt

/-- For the BCH finite no-root counterexample, the source predicate
has NO permissible proof-carrying minimum. -/
theorem no_instance_for_source_no_root_example :
    ¬ Nonempty (MinimalNatural noNaturalRoot) := by
  rintro ⟨receipt⟩
  exact noNaturalRoot_is_impossible receipt.value receipt.admissible

/-- Thus a *typechecking conditional schema* can coexist with an
uninhabited source presupposition, without fabricating any value.
The distinction is logical, not a proof of decidability or SCI height. -/
theorem guarded_schema_does_not_exhibit_nonexistent_minimum :
    (∀ receipt : MinimalNatural noNaturalRoot,
      (rationalFromWitness receipt + 1) ^ 2 =
        (rationalFromWitness receipt) ^ 2 +
          2 * rationalFromWitness receipt + 1) ∧
    ¬ Nonempty (MinimalNatural noNaturalRoot) := by
  exact ⟨uniform_guarded_template noNaturalRoot,
    no_instance_for_source_no_root_example⟩

end RequestProject.Autoformalisation.ConditionalTranslation
