import Synthesis.MillenniumHodgeDicksonOriginalGeneratedChartWeldExact

/-!
The original coordinate-generated affine algebra is the precise same
quotient as its source projective h=1 lift. No assertion that all
denominators of the full open A are already generated.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- Equality of actual affine coordinate polynomials is exactly
equality of their ORIGINAL projective h-chart representatives.
Unlike a set-of-points comparison this holds in the original
possibly nonreduced source algebra. -/
theorem original_generated_chart_equality_iff
    (p q : MvPolynomial OriginalCoord ℚ) :
    originalCoordinateEval p = originalCoordinateEval q ↔
      coneAtOne (projectiveCoordinateLift p) =
        coneAtOne (projectiveCoordinateLift q) := by
  rw [originalCoordinateEval_eq_cone_lift,
      originalCoordinateEval_eq_cone_lift]

/-- The same ideal of affine relations is recovered by original
projective numerator evaluation, not by a new coordinate scheme. -/
theorem original_generated_chart_kernel_iff
    (p : MvPolynomial OriginalCoord ℚ) :
    p ∈ originalCoordinateEval.ker ↔
      projectiveCoordinateLift p ∈ coneAtOne.ker := by
  change originalCoordinateEval p = 0 ↔
    coneAtOne (projectiveCoordinateLift p) = 0
  rw [originalCoordinateEval_eq_cone_lift]

/-- Bidirectional factorization at the quotient level: an affine
polynomial relation is exactly an h-chart polynomial relation.
This does NOT yet assert generated B = the entire original open A. -/
theorem original_generated_chart_difference_kernel
    (p q : MvPolynomial OriginalCoord ℚ) :
    p - q ∈ originalCoordinateEval.ker ↔
      projectiveCoordinateLift (p - q) ∈ coneAtOne.ker := by
  exact original_generated_chart_kernel_iff (p - q)

end
end DASHI.Hodge.DicksonCoupled
