import YangMills.ProjectiveCylinderOSContinuum

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (m : ℕ)
    (gram : BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (hcutoff : ∀ k : ℕ,
      0 ≤ ∫ x, gram x
        ∂(((source.family.marginal m (source.diagonal.subsequence k) :
          ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)))) :
    0 ≤ ∫ x, gram x
      ∂(((source.diagonal.limit m : ProbabilityMeasure (Fin m → ℝ)) :
        Measure (Fin m → ℝ))) :=
  source.diagonal_limit_nonnegative gram hcutoff

end RequestProject.YangMills
