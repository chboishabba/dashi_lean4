import YangMills.WilsonCountableToL2Density

open MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (wilson : ℕ → C(Ω, ℝ))
    (hInjective : Function.Injective (fun x i => wilson i x)) :
    ((wilsonGeneratedAlgebra wilson).toSubmodule.map
      (ContinuousMap.toLp (E := ℝ) (2 : ℝ≥0∞) μ ℝ).toLinearMap).topologicalClosure = ⊤ :=
  countable_wilson_generated_algebra_L2_dense μ wilson hInjective

end RequestProject.YangMills
