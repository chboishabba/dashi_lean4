import Mathlib
import YangMills.OSGramQuotientTranslation

/-!
# Semigroup laws on the algebraic OS quotient

Once each positive-time translation is contractive for the reflected Gram form,
the maps descend to the null quotient.  This file shows that the identity and
composition laws descend automatically as well.  Thus the remaining E2 debt is
analytic: equip the quotient with the induced pre-Hilbert norm, complete it,
extend these contractions continuously, prove the required continuity/self-
adjointness, and identify the generator.
-/

namespace RequestProject.YangMills

/-- The time-zero translation descends to the identity on the OS quotient. -/
theorem osGramQuotientTranslation_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : ℕ → V →ₗ[ℝ] V)
    (hContract : ∀ t v, B (T t v) (T t v) ≤ B v v)
    (hZero : ∀ v, T 0 v = v) :
    osGramQuotientTranslation B hPositive hSymmetric (T 0) (hContract 0) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  rw [osGramQuotientTranslation_mk]
  change Submodule.Quotient.mk (T 0 v) = Submodule.Quotient.mk v
  rw [hZero]

/-- The additive time law descends exactly to composition on the quotient. -/
theorem osGramQuotientTranslation_add
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : ℕ → V →ₗ[ℝ] V)
    (hContract : ∀ t v, B (T t v) (T t v) ≤ B v v)
    (hAdd : ∀ s t v, T (s + t) v = T s (T t v))
    (s t : ℕ) :
    osGramQuotientTranslation B hPositive hSymmetric (T (s + t))
        (hContract (s + t)) =
      (osGramQuotientTranslation B hPositive hSymmetric (T s) (hContract s)).comp
        (osGramQuotientTranslation B hPositive hSymmetric (T t) (hContract t)) := by
  apply LinearMap.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro v
  rw [osGramQuotientTranslation_mk]
  simp only [LinearMap.comp_apply]
  rw [osGramQuotientTranslation_mk, osGramQuotientTranslation_mk]
  change Submodule.Quotient.mk (T (s + t) v) =
    Submodule.Quotient.mk (T s (T t v))
  rw [hAdd]

end RequestProject.YangMills
