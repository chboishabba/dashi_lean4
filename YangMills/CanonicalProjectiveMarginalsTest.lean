import Mathlib
import YangMills.CanonicalProjectiveMarginals

open Filter MeasureTheory

namespace RequestProject.YangMills

example
    (m n : ℕ) (h : m ≤ n) :
    Continuous (realFinPrefixProjection m n h) :=
  real_fin_prefix_projection_continuous m n h

example
    {Ω : Type*} [MeasurableSpace Ω]
    (family : RealCanonicalProjectiveMarginalFamily Ω)
    (m n k : ℕ) (h : m ≤ n) :
    realFinPrefixMap m n h (family.marginal n k) =
      family.marginal m k :=
  family.finiteCutoffConsistency m n h k

end RequestProject.YangMills
