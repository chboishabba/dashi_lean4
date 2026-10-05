import YangMills.OSGramHilbertSemigroup

namespace RequestProject.YangMills

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : ℕ → V →ₗ[ℝ] V)
    (hContract : ∀ t v, data.gram (T t v) (T t v) ≤ data.gram v v)
    (hZero : ∀ v, T 0 v = v) :
    data.hilbertTranslation (T 0) (hContract 0) = ContinuousLinearMap.id ℝ data.Hilbert :=
  data.hilbertTranslation_zero T hContract hZero

end RequestProject.YangMills
