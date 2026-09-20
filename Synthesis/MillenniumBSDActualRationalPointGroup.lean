import Synthesis.MillenniumBSDExplicitSelmerSubgroup
import Synthesis.MillenniumBSDActualLocalPointGroup
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Tactic

/-!
# Actual rational elliptic group and total global Kummer map

This file replaces the earlier split rational Kummer carriers by one literal
projective point group for E : y^2 = x^3 - x over Q.  The group structure is
transported from mathlib's actual WeierstrassCurve.Affine.Point group.

The total global Kummer map uses the same exceptional values at O, (0,0),
and (1,0) as the local map, and [x],[x-1] on the ordinary affine locus.

Every rational point is proved to satisfy the already-constructed explicit
all-place Selmer conditions, and localization of the total global Kummer map
is proved to be literally the total local Kummer map at every prime.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

inductive RationalProjectivePoint : Type where
  | infinity
  | affine (x y : ℚ) (onCurve : y ^ 2 = x ^ 3 - x)

noncomputable def rationalProjectivePointEquivMathlib :
    RationalProjectivePoint ≃ cmWeierstrass.toAffine.Point where
  toFun
    | .infinity => .zero
    | .affine x y h =>
        WeierstrassCurve.Affine.Point.mk
          ((cmWeierstrass_equation_iff x y).mpr h)
  invFun
    | .zero => .infinity
    | .some x y h =>
        .affine x y
          ((cmWeierstrass_equation_iff x y).mp
            (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))
  left_inv := by
    intro P
    cases P <;> rfl
  right_inv := by
    intro P
    cases P <;> rfl

noncomputable instance rationalProjectivePointAddCommGroup :
    AddCommGroup RationalProjectivePoint :=
  rationalProjectivePointEquivMathlib.addCommGroup

noncomputable def rationalProjectivePointAddEquivMathlib :
    RationalProjectivePoint ≃+ cmWeierstrass.toAffine.Point :=
  rationalProjectivePointEquivMathlib.addEquiv

@[simp] theorem rationalProjective_zero_eq_infinity :
    (0 : RationalProjectivePoint) = .infinity := by
  apply rationalProjectivePointEquivMathlib.injective
  simp [rationalProjectivePointAddEquivMathlib]

theorem rationalProjective_add_transport
    (P Q : RationalProjectivePoint) :
    rationalProjectivePointEquivMathlib (P + Q)
      =
    rationalProjectivePointEquivMathlib P
      + rationalProjectivePointEquivMathlib Q := by
  exact rationalProjectivePointAddEquivMathlib.map_add P Q

def totalGlobalKummer :
    RationalProjectivePoint →
      RatSquareClass × RatSquareClass
  | .infinity => torsionKummer .infinity
  | .affine x y h =>
      if hx0 : x = 0 then
        torsionKummer .zero
      else if hx1 : x = 1 then
        torsionKummer .one
      else
        ordinaryKummer
          { x := x
          , y := y
          , onCurve := h
          , x_ne_zero := hx0
          , x_ne_one := hx1 }

@[simp] theorem totalGlobalKummer_infinity :
    totalGlobalKummer .infinity = torsionKummer .infinity :=
  rfl

@[simp] theorem totalGlobalKummer_zeroTorsion :
    totalGlobalKummer (.affine 0 0 (by norm_num))
      = torsionKummer .zero := by
  simp [totalGlobalKummer]

@[simp] theorem totalGlobalKummer_oneTorsion :
    totalGlobalKummer (.affine 1 0 (by norm_num))
      = torsionKummer .one := by
  simp [totalGlobalKummer]

theorem totalGlobalKummer_ordinary
    (P : OrdinaryKummerPoint) :
    totalGlobalKummer
      (.affine P.x P.y P.onCurve)
      = ordinaryKummer P := by
  simp [totalGlobalKummer, P.x_ne_zero, P.x_ne_one]

theorem rational_y_eq_zero_of_x_eq_zero
    {x y : ℚ}
    (h : y ^ 2 = x ^ 3 - x)
    (hx : x = 0) : y = 0 := by
  subst x
  simp at h
  exact sq_eq_zero_iff.mp h

theorem rational_y_eq_zero_of_x_eq_one
    {x y : ℚ}
    (h : y ^ 2 = x ^ 3 - x)
    (hx : x = 1) : y = 0 := by
  subst x
  simp at h
  exact sq_eq_zero_iff.mp h

theorem totalGlobalKummer_mem_explicitTwoSelmer
    (P : RationalProjectivePoint) :
    totalGlobalKummer P ∈ explicitTwoSelmerSubgroup := by
  cases P with
  | infinity =>
      simpa [totalGlobalKummer] using
        torsionKummer_mem_explicitTwoSelmerSubgroup
          RationalTwoTorsionPoint.infinity
  | affine x y h =>
      by_cases hx0 : x = 0
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_zero h rfl
        subst y
        simpa [totalGlobalKummer] using
          torsionKummer_mem_explicitTwoSelmerSubgroup
            RationalTwoTorsionPoint.zero
      by_cases hx1 : x = 1
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_one h rfl
        subst y
        simpa [totalGlobalKummer] using
          torsionKummer_mem_explicitTwoSelmerSubgroup
            RationalTwoTorsionPoint.one
      · have hmem :
          ordinaryKummer
            { x := x, y := y, onCurve := h,
              x_ne_zero := hx0, x_ne_one := hx1 }
            ∈ explicitTwoSelmerSubgroup :=
          ordinaryKummer_mem_explicitTwoSelmerSubgroup _
        simpa [totalGlobalKummer, hx0, hx1] using hmem

def globalKummerToSelmer
    (P : RationalProjectivePoint) :
    explicitTwoSelmerSubgroup :=
  ⟨totalGlobalKummer P, totalGlobalKummer_mem_explicitTwoSelmer P⟩

@[simp] theorem globalKummerToSelmer_coe
    (P : RationalProjectivePoint) :
    (globalKummerToSelmer P : RatSquareClass × RatSquareClass)
      = totalGlobalKummer P :=
  rfl

def localizeRationalProjectivePoint
    (p : ℕ) [Fact p.Prime] :
    RationalProjectivePoint → PadicProjectivePoint p
  | .infinity => .infinity
  | .affine x y h =>
      .affine (x : ℚ_[p]) (y : ℚ_[p]) (by
        exact_mod_cast h)

theorem totalGlobalKummer_localizes
    (p : ℕ) [Fact p.Prime]
    (P : RationalProjectivePoint) :
    totalLocalKummer p (localizeRationalProjectivePoint p P)
      =
    localizeKummerPair p (totalGlobalKummer P) := by
  cases P with
  | infinity =>
      rfl
  | affine x y h =>
      by_cases hx0 : x = 0
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_zero h rfl
        subst y
        simp [localizeRationalProjectivePoint, totalGlobalKummer,
          totalLocalKummer, localizeKummerPair, torsionKummer,
          localZeroKummer, localRationalClass]
      by_cases hx1 : x = 1
      · subst x
        have hy : y = 0 := rational_y_eq_zero_of_x_eq_one h rfl
        subst y
        simp [localizeRationalProjectivePoint, totalGlobalKummer,
          totalLocalKummer, localizeKummerPair, torsionKummer,
          localOneKummer, localRationalClass]
      · have hx0p : (x : ℚ_[p]) ≠ 0 := by
          exact_mod_cast hx0
        have hx1p : (x : ℚ_[p]) ≠ 1 := by
          exact_mod_cast hx1
        simp [localizeRationalProjectivePoint, totalGlobalKummer,
          totalLocalKummer, hx0, hx1, hx0p, hx1p]
        exact ordinaryKummer_localizes p
          { x := x, y := y, onCurve := h,
            x_ne_zero := hx0, x_ne_one := hx1 }

end Synthesis.Millennium.BSD
