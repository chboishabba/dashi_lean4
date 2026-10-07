import YangMills.ProjectiveFinIicRoundTrip

open Set MeasureTheory Preorder

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family)
    (n : ℕ) :
    Measure.map (realNatPrefix (n + 1)) diag.conditionalGlobalMeasure =
      (diag.limit (n + 1) : Measure (Fin (n + 1) → ℝ)) :=
  diag.conditionalGlobalMeasure_finSucc_prefix n

end RequestProject.YangMills
