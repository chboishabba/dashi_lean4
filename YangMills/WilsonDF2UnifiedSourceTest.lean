import YangMills.WilsonDF2UnifiedSource

open MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [StandardBorelSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω]
    (cutoffLaw : ℕ → ProbabilityMeasure Ω)
    (source : CountableWilsonDF2Source Ω) :
    RealCountableObservableDeterminingSource Ω :=
  source.determiningSource cutoffLaw

example
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [StandardBorelSpace Ω] [CompactSpace Ω]
    [SecondCountableTopology Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (source : CountableWilsonDF2Source Ω) :
    ((wilsonGeneratedAlgebra source.wilson).toSubmodule.map
      (ContinuousMap.toLp (E := ℝ) (2 : ℝ≥0∞) μ ℝ).toLinearMap).topologicalClosure = ⊤ :=
  source.L2_dense μ

end RequestProject.YangMills
