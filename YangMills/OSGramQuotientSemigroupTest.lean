import YangMills.OSGramQuotientSemigroup

namespace RequestProject.YangMills

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : ℕ → V →ₗ[ℝ] V)
    (hContract : ∀ t v, B (T t v) (T t v) ≤ B v v)
    (hZero : ∀ v, T 0 v = v) :
    osGramQuotientTranslation B hPositive hSymmetric (T 0) (hContract 0) =
      LinearMap.id :=
  osGramQuotientTranslation_zero B hPositive hSymmetric T hContract hZero

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : ℕ → V →ₗ[ℝ] V)
    (hContract : ∀ t v, B (T t v) (T t v) ≤ B v v)
    (hAdd : ∀ s t v, T (s + t) v = T s (T t v))
    (s t : ℕ) :
    osGramQuotientTranslation B hPositive hSymmetric (T (s + t)) (hContract (s + t)) =
      (osGramQuotientTranslation B hPositive hSymmetric (T s) (hContract s)).comp
        (osGramQuotientTranslation B hPositive hSymmetric (T t) (hContract t)) :=
  osGramQuotientTranslation_add B hPositive hSymmetric T hContract hAdd s t

end RequestProject.YangMills
