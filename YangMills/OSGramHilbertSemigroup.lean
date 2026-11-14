import Mathlib
import YangMills.OSGramHilbertTranslation

/-!
# Discrete OS semigroup on the completed Hilbert space

The quotient translations already satisfy the identity and additive-time laws.
Because their bounded extensions agree on the dense quotient image, the same
laws hold on the Hilbert completion.  This finishes the generic discrete
semigroup construction before the standard continuous-time/generator theorem.
-/

namespace RequestProject.YangMills

namespace OSGramData

/-- Time zero extends to the identity on the completed OS Hilbert space. -/
theorem hilbertTranslation_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : ℕ → V →ₗ[ℝ] V)
    (hContract : ∀ t v,
      data.gram (T t v) (T t v) ≤ data.gram v v)
    (hZero : ∀ v, T 0 v = v) :
    data.hilbertTranslation (T 0) (hContract 0) =
      ContinuousLinearMap.id ℝ data.Hilbert := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih q =>
      rw [data.hilbertTranslation_coe]
      change UniformSpace.Completion.coe
          (data.quotientTranslation (T 0) (hContract 0) q) =
        UniformSpace.Completion.coe q
      rw [osGramQuotientTranslation_zero
        data.gram data.positive data.symmetric T hContract hZero]
      rfl

/-- Additive Euclidean time extends to composition on the completed Hilbert space. -/
theorem hilbertTranslation_add
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : ℕ → V →ₗ[ℝ] V)
    (hContract : ∀ t v,
      data.gram (T t v) (T t v) ≤ data.gram v v)
    (hAdd : ∀ s t v, T (s + t) v = T s (T t v))
    (s t : ℕ) :
    data.hilbertTranslation (T (s + t)) (hContract (s + t)) =
      (data.hilbertTranslation (T s) (hContract s)).comp
        (data.hilbertTranslation (T t) (hContract t)) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih q =>
      rw [data.hilbertTranslation_coe]
      simp only [ContinuousLinearMap.comp_apply]
      rw [data.hilbertTranslation_coe, data.hilbertTranslation_coe]
      change UniformSpace.Completion.coe
          (data.quotientTranslation (T (s + t)) (hContract (s + t)) q) =
        UniformSpace.Completion.coe
          ((data.quotientTranslation (T s) (hContract s)).comp
            (data.quotientTranslation (T t) (hContract t)) q)
      rw [osGramQuotientTranslation_add
        data.gram data.positive data.symmetric T hContract hAdd s t]

end OSGramData

end RequestProject.YangMills
