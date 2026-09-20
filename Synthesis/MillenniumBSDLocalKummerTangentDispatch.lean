import Synthesis.MillenniumBSDLocalKummerTangent
import Synthesis.MillenniumBSDActualLocalPointGroup
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-!
# Dispatch the tangent identities through the actual elliptic doubling law

For a non-2-torsion affine point P=(x,y), mathlib's actual group law doubles P
with tangent slope

  λ = (3x²-1)/(2y).

This file identifies that formula with the explicit tangent coordinates used
by the two-descent algebra and proves Kummer multiplicativity for every
ordinary input/output doubling case.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

def tangentSumY
    {p : ℕ} [Fact p.Prime]
    (x y : ℚ_[p]) : ℚ_[p] :=
  -(tangentSlope x y * (tangentSumX x y - x) + y)

theorem cmPadic_negY_eq_neg
    {p : ℕ} [Fact p.Prime]
    (x y : ℚ_[p]) :
    (cmPadicWeierstrass p).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY,
    cmPadicWeierstrass, cmWeierstrass]

theorem cmPadic_y_ne_negY_of_ne_zero
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hy : y ≠ 0) :
    y ≠ (cmPadicWeierstrass p).toAffine.negY x y := by
  rw [cmPadic_negY_eq_neg]
  intro h
  have h2 : 2 * y = 0 := by linarith
  exact hy (by nlinarith)

theorem cmPadic_tangent_slope_eq
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hy : y ≠ 0) :
    (cmPadicWeierstrass p).toAffine.slope x x y y
      =
    tangentSlope x y := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl
    (cmPadic_y_ne_negY_of_ne_zero hy)]
  simp [tangentSlope, cmPadicWeierstrass, cmWeierstrass,
    WeierstrassCurve.Affine.negY]
  ring

theorem cmPadic_tangent_addX_eq
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hy : y ≠ 0) :
    (cmPadicWeierstrass p).toAffine.addX x x
      ((cmPadicWeierstrass p).toAffine.slope x x y y)
      =
    tangentSumX x y := by
  rw [cmPadic_tangent_slope_eq hy]
  simp [tangentSumX, WeierstrassCurve.Affine.addX,
    cmPadicWeierstrass, cmWeierstrass]

theorem cmPadic_tangent_addY_eq
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hy : y ≠ 0) :
    (cmPadicWeierstrass p).toAffine.addY x x y
      ((cmPadicWeierstrass p).toAffine.slope x x y y)
      =
    tangentSumY x y := by
  rw [cmPadic_tangent_slope_eq hy]
  simp [tangentSumY, tangentSumX,
    WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    cmPadicWeierstrass, cmWeierstrass]

theorem tangentSum_onCurve
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    (tangentSumY x y) ^ 2
      =
    (tangentSumX x y) ^ 3 - tangentSumX x y := by
  have heq :
      (cmPadicWeierstrass p).toAffine.Equation x y :=
    (cmPadic_equation_iff p x y).mpr hcurve
  have hadd :=
    WeierstrassCurve.Affine.equation_add
      heq heq
      (fun hxy =>
        (cmPadic_y_ne_negY_of_ne_zero hy) hxy.2)
  rw [cmPadic_tangent_addX_eq hy,
      cmPadic_tangent_addY_eq hy] at hadd
  exact (cmPadic_equation_iff p
    (tangentSumX x y)
    (tangentSumY x y)).mp hadd

theorem padicProjective_tangent_double
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    (.affine x y hcurve : PadicProjectivePoint p)
      + .affine x y hcurve
      =
    .affine
      (tangentSumX x y)
      (tangentSumY x y)
      (tangentSum_onCurve hcurve hy) := by
  apply (padicProjectivePointEquivMathlib p).injective
  rw [padicProjective_add_transport]
  simp only [padicProjectivePointEquivMathlib]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (cmPadic_y_ne_negY_of_ne_zero hy)]
  congr
  · exact cmPadic_tangent_addX_eq hy
  · exact cmPadic_tangent_addY_eq hy

theorem tangentKummerWitnessZero_ne_zero
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (hx : x ≠ 0)
    (hxR : tangentSumX x y ≠ 0) :
    tangentKummerWitnessZero x y ≠ 0 := by
  intro hw
  have hsq := tangent_x_square_identity hcurve hy
  rw [hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  exact mul_ne_zero hxR (pow_ne_zero 2 hx) hsq

theorem tangentKummerWitnessOne_ne_zero
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (hx : x ≠ 1)
    (hxR : tangentSumX x y ≠ 1) :
    tangentKummerWitnessOne x y ≠ 0 := by
  intro hw
  have hsq := tangent_x_sub_one_square_identity hcurve hy
  rw [hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  exact mul_ne_zero
    (sub_ne_zero.mpr hxR)
    (pow_ne_zero 2 (sub_ne_zero.mpr hx))
    hsq

theorem totalLocalKummer_tangent_ordinary
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hxR0 : tangentSumX x y ≠ 0)
    (hxR1 : tangentSumX x y ≠ 1) :
    totalLocalKummer p
      ((.affine x y hcurve : PadicProjectivePoint p)
        + .affine x y hcurve)
      =
    totalLocalKummer p (.affine x y hcurve)
      * totalLocalKummer p (.affine x y hcurve) := by
  rw [padicProjective_tangent_double hcurve hy]
  simp only [totalLocalKummer]
  split_ifs with hR0 hR1 h0 h1 h0' h1'
  · exact (hxR0 hR0).elim
  · exact (hxR1 hR1).elim
  · exact (hx0 h0).elim
  · exact (hx1 h1).elim
  · exact (hx0 h0').elim
  · exact (hx1 h1').elim
  · apply Prod.ext
    · calc
        padicSquareClassOf p
            ⟨tangentSumX x y, hxR0⟩
            = 1 :=
          tangent_first_squareClass_trivial
            hcurve hy hx0 hxR0
            (tangentKummerWitnessZero_ne_zero
              hcurve hy hx0 hxR0)
        _ = padicSquareClassOf p ⟨x, hx0⟩
              * padicSquareClassOf p ⟨x, hx0⟩ := by
          symm
          exact padicSquareClass_sq_eq_one _
    · calc
        padicSquareClassOf p
            ⟨tangentSumX x y - 1, sub_ne_zero.mpr hxR1⟩
            = 1 :=
          tangent_second_squareClass_trivial
            hcurve hy hx1 hxR1
            (tangentKummerWitnessOne_ne_zero
              hcurve hy hx1 hxR1)
        _ = padicSquareClassOf p
              ⟨x - 1, sub_ne_zero.mpr hx1⟩
              * padicSquareClassOf p
              ⟨x - 1, sub_ne_zero.mpr hx1⟩ := by
          symm
          exact padicSquareClass_sq_eq_one _

end Synthesis.Millennium.BSD
