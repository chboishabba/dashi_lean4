import Mathlib
import YangMills.BoundaryHaarDoubleAverage
import YangMills.LiteralSU2BoundaryHaarTranslation
import YangMills.LiteralSU2CrossingDoubleGaugeRelative

/-!
# Full temporal-boundary double-Haar collapse

After the local crossing algebra has reduced two independently gauged half-space
copies to the pointwise relative boundary field `b * c⁻¹`, the two full temporal
boundary Haar integrals collapse to the original single temporal-boundary Haar
integral.  This is the full-carrier version of the plane-wise result and matches
the carrier used by `literalSU2BoundaryGaugeProjectedWilsonKernel` directly.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Full temporal-boundary product Haar is invariant under pointwise right translation. -/
theorem literal_su2_full_boundary_haar_mul_right_invariant
    (n : ℕ) [NeZero n]
    (g : SU2BoundaryTemporalLinks n) :
    Measure.map
      (fun b : SU2BoundaryTemporalLinks n => fun p => b p * g p)
      (literalSU2BoundaryTemporalHaar n) =
      literalSU2BoundaryTemporalHaar n := by
  simpa [literalSU2BoundaryTemporalHaar] using
    (MeasureTheory.map_mul_right_eq_self
      (literalSU2BoundaryTemporalHaar n) g)

instance literalSU2FullBoundaryHaarIsMulRightInvariant
    (n : ℕ) [NeZero n] :
    Measure.IsMulRightInvariant (literalSU2BoundaryTemporalHaar n) where
  map_mul_right_eq_self := literal_su2_full_boundary_haar_mul_right_invariant n

/-- Two independent full boundary fields collapse to one relative Haar field. -/
theorem literal_su2_full_boundary_haar_double_relative
    (n : ℕ) [NeZero n]
    (k : SU2BoundaryTemporalLinks n → ℝ) :
    (∫ b, ∫ c, k (su2RelativeBoundaryField b c)
      ∂(literalSU2BoundaryTemporalHaar n)
      ∂(literalSU2BoundaryTemporalHaar n)) =
      ∫ u, k u ∂(literalSU2BoundaryTemporalHaar n) := by
  change
    (∫ b, ∫ c, k (fun p => b p * (c p)⁻¹)
      ∂(literalSU2BoundaryTemporalHaar n)
      ∂(literalSU2BoundaryTemporalHaar n)) =
      ∫ u, k u ∂(literalSU2BoundaryTemporalHaar n)
  exact haar_double_integral_mul_inv_eq_single
    (literalSU2BoundaryTemporalHaar n) k

end RequestProject.YangMills
