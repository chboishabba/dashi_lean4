import Synthesis.MillenniumBSDLocalKummerSecant
import Synthesis.MillenniumBSDActualLocalPointGroup
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-!
# Dispatch the secant identities through the actual elliptic group law

This file identifies the explicit secant coordinates used by the two-descent
algebra with mathlib's actual affine addition formula for the curve

  E : y² = x³ - x.

For x₁ ≠ x₂ the transported sum of our literal local points is exactly the
affine point with coordinates

  λ  = (y₁-y₂)/(x₁-x₂),
  xR = λ²-x₁-x₂,
  yR = -(λ(xR-x₁)+y₁).

The earlier square identities can therefore be applied directly to
`totalLocalKummer p (P+Q)`, rather than to a parallel coordinate model.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

def secantSumY
    {p : ℕ} [Fact p.Prime]
    (x₁ y₁ x₂ y₂ : ℚ_[p]) : ℚ_[p] :=
  -(secantSlope x₁ y₁ x₂ y₂
      * (secantSumX x₁ y₁ x₂ y₂ - x₁) + y₁)

theorem cmPadic_slope_eq_secant
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (hx : x₁ ≠ x₂) :
    (cmPadicWeierstrass p).toAffine.slope x₁ x₂ y₁ y₂
      =
    secantSlope x₁ y₁ x₂ y₂ := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rfl

theorem cmPadic_addX_eq_secantSumX
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (hx : x₁ ≠ x₂) :
    (cmPadicWeierstrass p).toAffine.addX x₁ x₂
      ((cmPadicWeierstrass p).toAffine.slope x₁ x₂ y₁ y₂)
      =
    secantSumX x₁ y₁ x₂ y₂ := by
  rw [cmPadic_slope_eq_secant hx]
  simp [secantSumX, WeierstrassCurve.Affine.addX,
    cmPadicWeierstrass, cmWeierstrass]

theorem cmPadic_addY_eq_secantSumY
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (hx : x₁ ≠ x₂) :
    (cmPadicWeierstrass p).toAffine.addY x₁ x₂ y₁
      ((cmPadicWeierstrass p).toAffine.slope x₁ x₂ y₁ y₂)
      =
    secantSumY x₁ y₁ x₂ y₂ := by
  rw [cmPadic_slope_eq_secant hx]
  simp [secantSumY, secantSumX,
    WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    cmPadicWeierstrass, cmWeierstrass]

theorem secantSum_onCurve
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) :
    (secantSumY x₁ y₁ x₂ y₂) ^ 2
      =
    (secantSumX x₁ y₁ x₂ y₂) ^ 3
      - secantSumX x₁ y₁ x₂ y₂ := by
  have heq₁ :
      (cmPadicWeierstrass p).toAffine.Equation x₁ y₁ :=
    (cmPadic_equation_iff p x₁ y₁).mpr h₁
  have heq₂ :
      (cmPadicWeierstrass p).toAffine.Equation x₂ y₂ :=
    (cmPadic_equation_iff p x₂ y₂).mpr h₂
  have hadd :=
    WeierstrassCurve.Affine.equation_add
      heq₁ heq₂
      (fun hxy => hx hxy.1)
  rw [cmPadic_addX_eq_secantSumX hx,
      cmPadic_addY_eq_secantSumY hx] at hadd
  exact (cmPadic_equation_iff p
    (secantSumX x₁ y₁ x₂ y₂)
    (secantSumY x₁ y₁ x₂ y₂)).mp hadd

theorem padicProjective_secant_add
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) :
    (.affine x₁ y₁ h₁ : PadicProjectivePoint p)
      + .affine x₂ y₂ h₂
      =
    .affine
      (secantSumX x₁ y₁ x₂ y₂)
      (secantSumY x₁ y₁ x₂ y₂)
      (secantSum_onCurve h₁ h₂ hx) := by
  apply (padicProjectivePointEquivMathlib p).injective
  rw [padicProjective_add_transport]
  simp only [padicProjectivePointEquivMathlib]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  congr
  · exact cmPadic_addX_eq_secantSumX hx
  · exact cmPadic_addY_eq_secantSumY hx

theorem totalLocalKummer_secant_ordinary
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂)
    (hx₁0 : x₁ ≠ 0) (hx₁1 : x₁ ≠ 1)
    (hx₂0 : x₂ ≠ 0) (hx₂1 : x₂ ≠ 1)
    (hxR0 : secantSumX x₁ y₁ x₂ y₂ ≠ 0)
    (hxR1 : secantSumX x₁ y₁ x₂ y₂ ≠ 1) :
    totalLocalKummer p
      ((.affine x₁ y₁ h₁ : PadicProjectivePoint p)
        + .affine x₂ y₂ h₂)
      =
    totalLocalKummer p (.affine x₁ y₁ h₁)
      * totalLocalKummer p (.affine x₂ y₂ h₂) := by
  rw [padicProjective_secant_add h₁ h₂ hx]
  simp only [totalLocalKummer]
  split_ifs with hR0 hR1 h10 h11 h20 h21
  · exact (hxR0 hR0).elim
  · exact (hxR1 hR1).elim
  · exact (hx₁0 h10).elim
  · exact (hx₁1 h11).elim
  · exact (hx₂0 h20).elim
  · exact (hx₂1 h21).elim
  · apply Prod.ext
    · exact secant_first_squareClass_mul_auto
        h₁ h₂ hx hx₁0 hx₂0 hxR0
    · exact secant_second_squareClass_mul_auto
        h₁ h₂ hx hx₁1 hx₂1 hxR1

end Synthesis.Millennium.BSD
