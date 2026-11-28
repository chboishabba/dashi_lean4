import Mathlib
import YangMills.LiteralSU2FullBoundaryHaarDoubleAverage

open MeasureTheory

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (k : SU2BoundaryTemporalLinks n → ℝ) :
    (∫ b, ∫ c, k (su2RelativeBoundaryField b c)
      ∂(literalSU2BoundaryTemporalHaar n)
      ∂(literalSU2BoundaryTemporalHaar n)) =
      ∫ u, k u ∂(literalSU2BoundaryTemporalHaar n) :=
  literal_su2_full_boundary_haar_double_relative n k

end RequestProject.YangMills
