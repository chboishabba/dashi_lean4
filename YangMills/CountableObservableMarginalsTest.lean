import YangMills.CountableObservableMarginals

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → MeasureTheory.ProbabilityMeasure Ω)
    (φ : ℕ → Ω → ℝ)
    (hφ : ∀ i, Measurable (φ i)) :
    RealCanonicalProjectiveMarginalFamily Ω :=
  countableObservableMarginalFamily μ φ hφ

example
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → MeasureTheory.ProbabilityMeasure Ω)
    (φ : ℕ → Ω → ℝ)
    (hφ : ∀ i, Measurable (φ i))
    (m : ℕ) (x : Ω) (i : Fin m) :
    (countableObservablePrefix φ m x) i = φ i x := rfl

end RequestProject.YangMills
