import Synthesis.MillenniumBSDCMUnitAreaTriangleCurveWeldExact
import Synthesis.MillenniumBSDRationalTwoTorsionExact
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic

/-!
# K3: direct rational rank-zero reduction via Fermat's square-area obstruction

A second, INDEPENDENT rank route on the literal original selected
elliptic point group:
* if no rational right triangle of area 1 exists,
  the actual curve y²=x³-x has no affine point with y != 0;
* thus EVERY genuine rational point is killed by 2;
* therefore the original Mordell–Weil ℤ-module has rank 0,
  without any separate finite-generation hypothesis.

The missing theorem is specifically
  ¬ CMHasRationalRightTriangleAreaOne.
Do not invent this as an axiom or automatically equate it with
Mathlib.Fermat42.not_fermat_42. The integral infinite-descent
bridge to the FLT(4) library remains an OPEN arithmetic producer.

This is a conditional IMPLICATION on the original objects, not
a completed rank-zero theorem. Source-written until kernel checked.
-/

namespace Synthesis.Millennium.BSD

/-- Fermat's no-square-area-right-triangle assertion directly
excludes every nonexceptional original rational affine curve point. -/
theorem cmNoUnitAreaTriangle_forces_affineY_zero
    (hNo : ¬ CMHasRationalRightTriangleAreaOne)
    (x y : ℚ) (hcurve : y ^ 2 = x ^ 3 - x) :
    y = 0 := by
  by_contra hy
  exact hNo
    (cmSelectedCurvePoint_implies_unitAreaTriangle x y hcurve hy)

/-- The exact first-principles consequence for the ACTUAL original
rational elliptic point group: every point is killed by doubling.
This is stronger than a quotient-cardinality result. -/
theorem cmNoUnitAreaTriangle_forces_allRationalTwoTorsion
    (hNo : ¬ CMHasRationalRightTriangleAreaOne)
    (P : RationalProjectivePoint) :
    (2 : ℕ) • P = 0 := by
  cases P with
  | infinity =>
      simp [rationalProjective_zero_eq_infinity]
  | affine x y hcurve =>
      have hy : y = 0 :=
        cmNoUnitAreaTriangle_forces_affineY_zero hNo x y hcurve
      have hself :
          (.affine x y hcurve : RationalProjectivePoint) =
            -(.affine x y hcurve : RationalProjectivePoint) := by
        rw [rationalProjective_neg_affine]
        simp [hy]
      rw [two_nsmul]
      exact add_eq_zero_iff_eq_neg.mpr hself

/-- An unconditional source-level original-curve IMPLICATION:
Fermat's no-square-area-triangle theorem, once kernel-established,
immediately implies rank(E(Q))=0, without needing the formal
general Mordell–Weil finite-generation theorem. -/
theorem cmOriginalMordellWeil_ZRank_zero_of_noUnitAreaTriangle
    (hNo : ¬ CMHasRationalRightTriangleAreaOne) :
    Module.rank ℤ RationalProjectivePoint = 0 := by
  have hT : AddMonoid.IsTorsion RationalProjectivePoint := by
    intro P
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    exact ⟨2, by norm_num,
      cmNoUnitAreaTriangle_forces_allRationalTwoTorsion hNo P⟩
  exact (rank_eq_zero_iff_isTorsion
    (R := ℤ) (M := RationalProjectivePoint)).mpr
    ((AddMonoid.isTorsion_iff_isTorsion_int).mp hT)

end Synthesis.Millennium.BSD
