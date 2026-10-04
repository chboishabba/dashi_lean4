import YangMills.CountableObservableDetermining

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableDeterminingSource Ω)
    (μ ν : Measure Ω)
    (h : Measure.map source.coordinateMap μ = Measure.map source.coordinateMap ν) :
    μ = ν :=
  source.measure_eq_of_coordinate_map_eq μ ν h

example
    {Ω : Type*} [MeasurableSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i)) :
    RealCountableObservableUniformBoundSource Ω :=
  tanhBoundedObservableSource cutoffLaw raw hMeas

end RequestProject.YangMills
