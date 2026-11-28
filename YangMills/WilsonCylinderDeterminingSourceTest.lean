import YangMills.WilsonCylinderDeterminingSource

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (raw : ℕ → Ω → ℝ)
    (hMeas : ∀ i, Measurable (raw i))
    (cutoffLaw : ℕ → ProbabilityMeasure Ω) :
    RealCountableObservableDeterminingSource (WilsonCylinderState raw) :=
  wilsonCylinderDeterminingSource raw hMeas cutoffLaw

end RequestProject.YangMills
