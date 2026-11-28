import YangMills.WilsonCylinderCutoffLaw

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    ℕ → ProbabilityMeasure (WilsonCylinderState raw) :=
  wilsonCylinderCutoffLaw raw hMeas cutoffLaw

end RequestProject.YangMills
