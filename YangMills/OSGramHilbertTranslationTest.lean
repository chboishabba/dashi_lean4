import YangMills.OSGramHilbertTranslation

namespace RequestProject.YangMills

example
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (data : OSGramData V)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v, data.gram (T v) (T v) ≤ data.gram v v) :
    data.Hilbert →L[ℝ] data.Hilbert :=
  data.hilbertTranslation T hContract

end RequestProject.YangMills
