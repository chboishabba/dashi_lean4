import Synthesis.MillenniumBSDLocalKummerSecant
import Mathlib.Tactic

/-!
# Tangent/doubling Kummer identities for y² = x³ - x

For an affine point P=(x,y) with y ≠ 0, the tangent slope is

  λ = (3x²-1)/(2y)

and x(2P)=λ²-2x.  Direct algebra on y²=x³-x proves

  x(2P) * x²
    = (x(x²+1)/(2y))²,

and

  (x(2P)-1) * (x-1)²
    = ((x-1)(x²-2x-1)/(2y))².

Therefore both square-class coordinates of 2P are trivial, exactly as required
by δ(2P)=δ(P)²=1 in an elementary 2-group.
-/

namespace Synthesis.Millennium.BSD

def tangentSlope
    {p : ℕ} [Fact p.Prime]
    (x y : ℚ_[p]) : ℚ_[p] :=
  (3 * x ^ 2 - 1) / (2 * y)

def tangentSumX
    {p : ℕ} [Fact p.Prime]
    (x y : ℚ_[p]) : ℚ_[p] :=
  (tangentSlope x y) ^ 2 - 2 * x

def tangentKummerWitnessZero
    {p : ℕ} [Fact p.Prime]
    (x y : ℚ_[p]) : ℚ_[p] :=
  x * (x ^ 2 + 1) / (2 * y)

def tangentKummerWitnessOne
    {p : ℕ} [Fact p.Prime]
    (x y : ℚ_[p]) : ℚ_[p] :=
  (x - 1) * (x ^ 2 - 2 * x - 1) / (2 * y)

theorem tangent_x_square_identity
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    tangentSumX x y * x ^ 2
      =
    (tangentKummerWitnessZero x y) ^ 2 := by
  unfold tangentSumX tangentSlope tangentKummerWitnessZero
  field_simp [hy]
  nlinarith [hcurve]

theorem tangent_x_sub_one_square_identity
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    (tangentSumX x y - 1) * (x - 1) ^ 2
      =
    (tangentKummerWitnessOne x y) ^ 2 := by
  unfold tangentSumX tangentSlope tangentKummerWitnessOne
  field_simp [hy]
  nlinarith [hcurve]

theorem padicSquareClass_eq_one_of_mul_self_square
    {p : ℕ} [Fact p.Prime]
    {a x q : ℚ_[p]}
    (ha : a ≠ 0) (hx : x ≠ 0) (hq : q ≠ 0)
    (h : a * x ^ 2 = q ^ 2) :
    padicSquareClassOf p ⟨a, ha⟩ = 1 := by
  apply Quotient.sound
  refine ⟨⟨x, hx⟩, nzPadicOne p, ?_⟩
  dsimp [nzPadicOne]
  simpa using h

theorem tangent_first_squareClass_trivial
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (hx : x ≠ 0)
    (hxR : tangentSumX x y ≠ 0)
    (hw : tangentKummerWitnessZero x y ≠ 0) :
    padicSquareClassOf p ⟨tangentSumX x y, hxR⟩ = 1 := by
  apply padicSquareClass_eq_one_of_mul_self_square
    hxR hx hw
  exact tangent_x_square_identity hcurve hy

theorem tangent_second_squareClass_trivial
    {p : ℕ} [Fact p.Prime]
    {x y : ℚ_[p]}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (hx : x ≠ 1)
    (hxR : tangentSumX x y ≠ 1)
    (hw : tangentKummerWitnessOne x y ≠ 0) :
    padicSquareClassOf p
      ⟨tangentSumX x y - 1, sub_ne_zero.mpr hxR⟩
      =
    1 := by
  apply padicSquareClass_eq_one_of_mul_self_square
    (sub_ne_zero.mpr hxR)
    (sub_ne_zero.mpr hx)
    hw
  exact tangent_x_sub_one_square_identity hcurve hy

end Synthesis.Millennium.BSD
