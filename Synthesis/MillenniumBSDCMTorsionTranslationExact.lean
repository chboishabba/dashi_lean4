import Synthesis.MillenniumBSDCMHalfSignActionExact
import Synthesis.MillenniumBSDActualE2AdditiveEquiv
import Mathlib.Tactic

/-!
# Selected CM curve: actual two-torsion translation x-coordinate formulas

For E : y² = x³ - x over Qbar, translation by the three nonzero rational
2-torsion points acts on the affine x-coordinate by the familiar involutions

  T₀=(0,0):    x(P+T₀) = -1/x(P),
  T₁=(1,0):    (x(P)-1)(x(P+T₁)-1) = 2,
  T₋₁=(-1,0):  (x(P)+1)(x(P+T₋₁)+1) = 2.

This owner proves those relations using Mathlib's actual affine elliptic group
law (`Point.xRep_add_of_X_ne`).  They are the group-theoretic counterpart of
the root-sign identities in `MillenniumBSDCMHalfSignActionExact`.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

noncomputable section

/-- A nonzero-y point on the selected curve cannot have x-coordinate 0. -/
theorem cmAlgClosure_x_ne_zero_of_y_ne_zero
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) : x ≠ 0 := by
  intro hx
  subst x
  simp at hcurve
  exact hy (sq_eq_zero_iff.mp hcurve)

/-- Nor x-coordinate 1. -/
theorem cmAlgClosure_x_ne_one_of_y_ne_zero
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) : x ≠ 1 := by
  intro hx
  subst x
  norm_num at hcurve
  exact hy (sq_eq_zero_iff.mp hcurve)

/-- Nor x-coordinate -1. -/
theorem cmAlgClosure_x_ne_neg_one_of_y_ne_zero
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) : x ≠ -1 := by
  intro hx
  subst x
  norm_num at hcurve
  exact hy (sq_eq_zero_iff.mp hcurve)

private theorem selected_nonsingular
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x) :
    cmAlgClosureWeierstrass.toAffine.Nonsingular x y := by
  exact (cmAlgClosure_equation_iff x y).mpr hcurve

private theorem torsion0_nonsingular :
    cmAlgClosureWeierstrass.toAffine.Nonsingular (0 : RatAlgClosure) 0 := by
  exact selected_nonsingular (by norm_num)

private theorem torsion1_nonsingular :
    cmAlgClosureWeierstrass.toAffine.Nonsingular (1 : RatAlgClosure) 0 := by
  exact selected_nonsingular (by norm_num)

private theorem torsionNeg1_nonsingular :
    cmAlgClosureWeierstrass.toAffine.Nonsingular (-1 : RatAlgClosure) 0 := by
  exact selected_nonsingular (by norm_num)

/-- Translation by (0,0) has x-coordinate -1/x on the literal Mathlib group. -/
theorem cmAlgClosure_add_torsion0_xRep
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    (WeierstrassCurve.Affine.Point.some x y (selected_nonsingular hcurve) +
      WeierstrassCurve.Affine.Point.some 0 0 torsion0_nonsingular).xRep
      = ![-1 / x, 1] := by
  have hx0 := cmAlgClosure_x_ne_zero_of_y_ne_zero hcurve hy
  rw [WeierstrassCurve.Affine.Point.xRep_add_of_X_ne
    (selected_nonsingular hcurve) torsion0_nonsingular hx0]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  apply congrArg (fun z : RatAlgClosure => ![z, 1])
  field_simp [hx0]
  nlinarith [hcurve]

/-- Translation by (1,0) gives the exact shifted-product relation used by the
(a,c)-sign flip. -/
theorem cmAlgClosure_add_torsion1_xRep_shifted
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    let P := WeierstrassCurve.Affine.Point.some x y (selected_nonsingular hcurve)
    let T := WeierstrassCurve.Affine.Point.some 1 0 torsion1_nonsingular
    (x - 1) * ((P + T).xRep 0 - 1) = 2 := by
  dsimp
  have hx1 := cmAlgClosure_x_ne_one_of_y_ne_zero hcurve hy
  rw [WeierstrassCurve.Affine.Point.xRep_add_of_X_ne
    (selected_nonsingular hcurve) torsion1_nonsingular hx1]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  field_simp [hx1]
  nlinarith [hcurve]

/-- Translation by (-1,0) gives the third exact shifted-product relation. -/
theorem cmAlgClosure_add_torsionNeg1_xRep_shifted
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    let P := WeierstrassCurve.Affine.Point.some x y (selected_nonsingular hcurve)
    let T := WeierstrassCurve.Affine.Point.some (-1) 0 torsionNeg1_nonsingular
    (x + 1) * ((P + T).xRep 0 + 1) = 2 := by
  dsimp
  have hxn1 := cmAlgClosure_x_ne_neg_one_of_y_ne_zero hcurve hy
  rw [WeierstrassCurve.Affine.Point.xRep_add_of_X_ne
    (selected_nonsingular hcurve) torsionNeg1_nonsingular hxn1]
  simp [cmAlgClosureWeierstrass, cmWeierstrass]
  field_simp [hxn1]
  nlinarith [hcurve]

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head Lean certification):
* the three x-coordinate translation laws for the literal selected Mathlib
  elliptic group and its actual rational 2-torsion points;
* exact match, at the level of x-coordinate involutions, with the three even
  root-sign flips of the explicit geometric half.

NEXT FINITE IDENTIFICATION:
* show each sign-flipped half is `Q + T` (or equivalently classify the
  difference as the unique E[2] point compatible with the corresponding
  x-coordinate relation);
* conclude the two raw geometric Kummer bits are `(sign b, sign a)`;
* discharge `CMGeometricXTKummerOrientationTheorem` and hence the global
  cohomological/x-T equality.
-/

end

end Synthesis.Millennium.BSD
