import YangMills.WilsonUniformToL2Density

open MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [BorelSpace Ω] [SecondCountableTopology Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (wilsonSubmodule : Submodule ℝ (Ω →ᵇ ℝ))
    (hDense : wilsonSubmodule.topologicalClosure = ⊤) :
    (wilsonSubmodule.map
      (BoundedContinuousFunction.toLp (2 : ℝ≥0∞) μ ℝ).toLinearMap).topologicalClosure = ⊤ :=
  wilson_uniform_dense_to_L2_dense μ wilsonSubmodule hDense

end RequestProject.YangMills
