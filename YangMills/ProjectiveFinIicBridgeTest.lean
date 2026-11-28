import YangMills.ProjectiveFinIicBridge

open Set MeasureTheory Preorder

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family)
    (a b : ℕ) (hab : a ≤ b) :
    ((diag.toSequentialProjectiveFamily.marginal b :
        ProbabilityMeasure ((i : Set.Iic b) → ℝ)) :
      Measure ((i : Set.Iic b) → ℝ)).map (frestrictLe₂ hab) =
    ((diag.toSequentialProjectiveFamily.marginal a :
        ProbabilityMeasure ((i : Set.Iic a) → ℝ)) :
      Measure ((i : Set.Iic a) → ℝ)) :=
  diag.toSequentialProjectiveFamily.consistent a b hab

end RequestProject.YangMills
