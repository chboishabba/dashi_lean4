import YangMills.CountableObservableNormMomentContinuum

open Set MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω)
    (m : ℕ) :
    IsTightMeasureSet
      {ν : Measure (Fin m → ℝ) |
        ∃ p ∈ Set.range (source.family.marginal m),
          ((p : ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)) = ν} :=
  source.marginal_tight m

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω) :
    IsProbabilityMeasure source.globalMeasure := by infer_instance

end RequestProject.YangMills
