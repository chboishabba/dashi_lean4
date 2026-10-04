import YangMills.CountableObservableCoordinateMoment

open MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableCoordinateMomentSource Ω)
    (m k : ℕ) :
    (∫⁻ x : Ω,
      realFinitePrefixNormCost m
        (countableObservablePrefix source.observable m x)
      ∂((source.cutoffLaw k : ProbabilityMeasure Ω) : Measure Ω)) ≤
      source.prefixMomentBound m :=
  source.uniform_prefix_norm_moment m k

end RequestProject.YangMills
