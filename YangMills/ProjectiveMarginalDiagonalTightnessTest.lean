import Mathlib
import YangMills.ProjectiveMarginalDiagonalTightness

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (hTight :
      ∀ m : ℕ,
        MeasureTheory.IsTightMeasureSet
          {ν : MeasureTheory.Measure (Fin m → ℝ) |
            ∃ p ∈ Set.range (family.marginal m),
              ((p : MeasureTheory.ProbabilityMeasure (Fin m → ℝ)) :
                MeasureTheory.Measure (Fin m → ℝ)) = ν}) :
    Nonempty (RealSimultaneousMarginalSubsequence family) :=
  exists_simultaneous_marginal_subsequence_of_tight family hTight

end RequestProject.YangMills
