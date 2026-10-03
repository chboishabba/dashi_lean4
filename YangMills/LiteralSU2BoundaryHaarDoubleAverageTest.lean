import Mathlib
import YangMills.LiteralSU2BoundaryHaarDoubleAverage

open MeasureTheory

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (k : SU2UpperBoundaryTemporalLinks n → ℝ) :
    (∫ g, ∫ h, k (g⁻¹ * h) ∂(literalSU2UpperBoundaryTemporalHaar n)
      ∂(literalSU2UpperBoundaryTemporalHaar n)) =
      ∫ u, k u ∂(literalSU2UpperBoundaryTemporalHaar n) :=
  literal_su2_upper_boundary_haar_double_relative n k

example
    (n : ℕ) [NeZero n]
    (k : SU2LowerBoundaryTemporalLinks n → ℝ) :
    (∫ g, ∫ h, k (g⁻¹ * h) ∂(literalSU2LowerBoundaryTemporalHaar n)
      ∂(literalSU2LowerBoundaryTemporalHaar n)) =
      ∫ u, k u ∂(literalSU2LowerBoundaryTemporalHaar n) :=
  literal_su2_lower_boundary_haar_double_relative n k

end RequestProject.YangMills
