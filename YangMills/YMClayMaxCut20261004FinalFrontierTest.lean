import YangMills.YMClayMaxCut20261004FinalFrontier

open MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (raw : ℕ → Ω → ℝ)
    (h : YM20261004DPhysicalSeparatingProducer raw) :
    RealCountableObservableDeterminingSource.ProducerExists
      cutoffLaw (fun i x => Real.tanh (raw i x)) :=
  ym_20261004_d_physical_separating_to_determining cutoffLaw raw h

example
    {X : Type*}
    (cut : CMP119FunctionalResidualReflectionCut X) :
    ReflectionPositiveKernel cut.sourceKernel :=
  ym_20261004_b_functional_residual_rp cut

end RequestProject.YangMills
