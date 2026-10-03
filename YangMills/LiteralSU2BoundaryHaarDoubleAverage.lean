import Mathlib
import YangMills.BoundaryHaarDoubleAverage
import YangMills.LiteralSU2BoundaryHaarTranslation

/-!
# Literal SU(2) boundary-plane double-Haar collapse

The generic relative-Haar theorem is specialized here to the exact upper and
lower temporal boundary-plane laws used by the projected Wilson kernel.  This
pays the remaining abstract Haar/Fubini change-of-variables seam without
introducing a second boundary carrier.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Independent upper-plane Haar copies reduce to one relative upper boundary. -/
theorem literal_su2_upper_boundary_haar_double_relative
    (n : ℕ) [NeZero n]
    (k : SU2UpperBoundaryTemporalLinks n → ℝ) :
    (∫ g, ∫ h, k (g⁻¹ * h) ∂(literalSU2UpperBoundaryTemporalHaar n)
      ∂(literalSU2UpperBoundaryTemporalHaar n)) =
      ∫ u, k u ∂(literalSU2UpperBoundaryTemporalHaar n) := by
  exact haar_double_integral_relative_eq_single
    (literalSU2UpperBoundaryTemporalHaar n) k

/-- Independent lower-plane Haar copies reduce to one relative lower boundary. -/
theorem literal_su2_lower_boundary_haar_double_relative
    (n : ℕ) [NeZero n]
    (k : SU2LowerBoundaryTemporalLinks n → ℝ) :
    (∫ g, ∫ h, k (g⁻¹ * h) ∂(literalSU2LowerBoundaryTemporalHaar n)
      ∂(literalSU2LowerBoundaryTemporalHaar n)) =
      ∫ u, k u ∂(literalSU2LowerBoundaryTemporalHaar n) := by
  exact haar_double_integral_relative_eq_single
    (literalSU2LowerBoundaryTemporalHaar n) k

end RequestProject.YangMills
