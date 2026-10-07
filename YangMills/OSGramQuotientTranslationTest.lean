import YangMills.OSGramQuotientTranslation

namespace RequestProject.YangMills

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V, B (T v) (T v) ≤ B v v) :
    V ⧸ B.ker →ₗ[ℝ] V ⧸ B.ker :=
  osGramQuotientTranslation B hPositive hSymmetric T hContract

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V, B (T v) (T v) ≤ B v v)
    (v : V) :
    osGramQuotientTranslation B hPositive hSymmetric T hContract
        (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (T v) :=
  osGramQuotientTranslation_mk B hPositive hSymmetric T hContract v

end RequestProject.YangMills
