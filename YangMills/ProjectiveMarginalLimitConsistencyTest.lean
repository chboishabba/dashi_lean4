import Mathlib
import YangMills.ProjectiveMarginalLimitConsistency

open Filter MeasureTheory

namespace RequestProject.YangMills

example
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (diag : RealSimultaneousMarginalSubsequence family)
    (m n : ℕ) (h : m ≤ n) :
    realFinPrefixMap m n h (diag.limit n) = diag.limit m :=
  diag.limit_consistent m n h

end RequestProject.YangMills
