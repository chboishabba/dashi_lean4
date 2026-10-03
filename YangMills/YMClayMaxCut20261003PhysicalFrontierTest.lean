import YangMills.YMClayMaxCut20261003PhysicalFrontier

open Set MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableNormMomentSource Ω) :
    IsProbabilityMeasure (ym_20261003_selected_observable_continuum source) := by
  infer_instance

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    IsProbabilityMeasure
      (ym_20261003_bounded_selected_observable_continuum source) := by
  infer_instance

example
    {Ω : Type*} [MeasurableSpace Ω]
    (source : RealCountableObservableUniformBoundSource Ω) :
    YM20261003D3SelectedPrefixNormMomentProducerExists
      source.cutoffLaw source.observable :=
  ym_20261003_d3_bounded_source_closes_moment_leaf source

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left : SU2PositiveInteriorLinks n)
    (b₁ b₂ : SU2BoundaryTemporalLinks n)
    (r₁ r₂ : SU2PositiveInteriorLinks n) :
    su2EvenTimePositiveWilsonHalf n (su2AssembleReflectedPair n left b₁ r₁) β =
      su2EvenTimePositiveWilsonHalf n (su2AssembleReflectedPair n left b₂ r₂) β :=
  ym_20261003_block_a_positive_half_boundary_independent
    n β left b₁ b₂ r₁ r₂

end RequestProject.YangMills
