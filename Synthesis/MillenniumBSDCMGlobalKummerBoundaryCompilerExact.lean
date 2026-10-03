import Synthesis.MillenniumBSDCMGlobalKummerOrdinaryExact
import Synthesis.MillenniumBSDRationalTwoTorsionExact
import Synthesis.MillenniumBSDCMXTOrientationExact
import Mathlib.Tactic

/-!
# Selected CM curve: full global comparison reduced to four finite boundaries

The ordinary non-two-torsion affine case is now source-written.  The only
points not covered by that theorem are exactly

  O, (0,0), (1,0), (-1,0).

This owner packages those four literal equalities and proves that they are
sufficient for the full repository target
`CMGeometricXTKummerOrientationTheorem`.  No new cohomology or Kummer map is
introduced.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

/-- Exact finite boundary left after the ordinary-point global comparison. -/
structure CMGeometricXTKummerFiniteBoundary : Prop where
  infinity :
    cmRationalCohomologicalKummerSquareClass
        (.infinity : RationalProjectivePoint) =
      ratSquareClassPairSwap
        (totalGlobalKummer (.infinity : RationalProjectivePoint))
  zeroTorsion :
    cmRationalCohomologicalKummerSquareClass rationalZeroTorsionPoint =
      ratSquareClassPairSwap (totalGlobalKummer rationalZeroTorsionPoint)
  oneTorsion :
    cmRationalCohomologicalKummerSquareClass rationalOneTorsionPoint =
      ratSquareClassPairSwap (totalGlobalKummer rationalOneTorsionPoint)
  minusOneTorsion :
    cmRationalCohomologicalKummerSquareClass rationalMinusOneTorsionPoint =
      ratSquareClassPairSwap (totalGlobalKummer rationalMinusOneTorsionPoint)

/-- The four finite boundary equalities plus the already-paid ordinary theorem
imply the full raw geometric/x-T orientation theorem on every rational point. -/
theorem cmGeometricXTKummerOrientation_of_finiteBoundary
    (hboundary : CMGeometricXTKummerFiniteBoundary) :
    CMGeometricXTKummerOrientationTheorem := by
  intro P
  cases P with
  | infinity =>
      exact hboundary.infinity
  | affine x y hcurve =>
      by_cases hy0 : y = 0
      · have hx : x = 0 ∨ x = 1 ∨ x = -1 := by
          have hpoly : x ^ 3 - x = 0 := by
            rw [← hcurve]
            simp [hy0]
          have hfac : x * (x - 1) * (x + 1) = 0 := by
            calc
              x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
              _ = 0 := hpoly
          rcases mul_eq_zero.mp hfac with hleft | hplus
          · rcases mul_eq_zero.mp hleft with hx0 | hx1
            · exact Or.inl hx0
            · exact Or.inr (Or.inl (sub_eq_zero.mp hx1))
          · exact Or.inr (Or.inr (by linarith))
        rcases hx with hx0 | hx1 | hxneg
        · subst x; subst y
          simpa [rationalZeroTorsionPoint] using hboundary.zeroTorsion
        · subst x; subst y
          simpa [rationalOneTorsionPoint] using hboundary.oneTorsion
        · subst x; subst y
          simpa [rationalMinusOneTorsionPoint] using hboundary.minusOneTorsion
      · have hx0 : x ≠ 0 := by
          intro hx
          subst x
          have : y ^ 2 = 0 := by simpa using hcurve
          exact hy0 (sq_eq_zero_iff.mp this)
        have hx1 : x ≠ 1 := by
          intro hx
          subst x
          have : y ^ 2 = 0 := by norm_num at hcurve ⊢; exact hcurve
          exact hy0 (sq_eq_zero_iff.mp this)
        exact cmRationalCohomologicalKummer_raw_eq_swap_totalGlobal_ordinary
          hcurve hy0 hx0 hx1

/-- Once the four finite quarter-point computations are supplied, the
x-T-oriented geometric Kummer map agrees literally with `totalGlobalKummer`
on every rational point. -/
theorem cmRationalCohomologicalKummerXT_eq_totalGlobalKummer_of_finiteBoundary
    (hboundary : CMGeometricXTKummerFiniteBoundary)
    (P : RationalProjectivePoint) :
    cmRationalCohomologicalKummerXTSquareClass P = totalGlobalKummer P :=
  cmRationalCohomologicalKummerXT_eq_totalGlobalKummer
    (cmGeometricXTKummerOrientation_of_finiteBoundary hboundary) P

/-!
MAX-CUT STATUS

The selected-curve GLOBAL comparison is now reduced to exactly four finite
geometric computations and nothing else:

* O;
* (0,0);
* (1,0);
* (-1,0).

The ordinary affine theorem, Galois root-sign table, E[2] orientation,
continuous H¹ normalization, square-class comparison and canonical-half
independence are all upstream of this compiler.

After the four boundary fields are inhabited, the next mathematical phase is
local scalar Kummer compatibility; no additional global architecture is
needed.
-/

end

end Synthesis.Millennium.BSD
