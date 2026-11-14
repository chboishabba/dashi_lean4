import YangMills.YMClayMaxCut20261005FinalFrontier

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    RealCountableObservableDeterminingSource (WilsonCylinderState raw) :=
  ym20261005CylinderContinuumSource raw hMeas cutoffLaw

example
    {n : ℕ} [NeZero n] {X : Type*}
    (source : CMP119SelectedSourceFunctionalReflectionCut n X) :
    ReflectionPositiveKernel source.sourceKernel :=
  ym20261005BCCompiler source

end RequestProject.YangMills
