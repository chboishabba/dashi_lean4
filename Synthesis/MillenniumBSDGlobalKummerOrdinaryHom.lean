import Synthesis.MillenniumBSDGlobalKummerBoundaryCases
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-!
# Ordinary rational secant/tangent Kummer multiplicativity

This is the Q-valued analogue of the already-proved Q_p descent algebra, but
it is dispatched through the actual rational elliptic group.  It proves the
global Kummer multiplication law whenever both inputs and the output avoid
the exceptional x=0,1 branches.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

def rationalSecantSlope (x₁ y₁ x₂ y₂ : ℚ) : ℚ :=
  (y₁ - y₂) / (x₁ - x₂)

def rationalSecantSumX (x₁ y₁ x₂ y₂ : ℚ) : ℚ :=
  rationalSecantSlope x₁ y₁ x₂ y₂ ^ 2 - x₁ - x₂

def rationalSecantSumY (x₁ y₁ x₂ y₂ : ℚ) : ℚ :=
  -(rationalSecantSlope x₁ y₁ x₂ y₂ *
      (rationalSecantSumX x₁ y₁ x₂ y₂ - x₁) + y₁)

def rationalSecantWitnessZero (x₁ y₁ x₂ y₂ : ℚ) : ℚ :=
  (y₁ * x₂ - y₂ * x₁) / (x₁ - x₂)

def rationalSecantWitnessOne (x₁ y₁ x₂ y₂ : ℚ) : ℚ :=
  (y₁ * (x₂ - 1) - y₂ * (x₁ - 1)) / (x₁ - x₂)

theorem rational_secant_x_square_identity
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) :
    rationalSecantSumX x₁ y₁ x₂ y₂ * x₁ * x₂
      = rationalSecantWitnessZero x₁ y₁ x₂ y₂ ^ 2 := by
  unfold rationalSecantSumX rationalSecantSlope rationalSecantWitnessZero
  field_simp [sub_ne_zero.mpr hx]
  linear_combination
    (x₁ - x₂) * x₂ * h₁ - (x₁ - x₂) * x₁ * h₂

theorem rational_secant_x_sub_one_square_identity
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) :
    (rationalSecantSumX x₁ y₁ x₂ y₂ - 1)
        * (x₁ - 1) * (x₂ - 1)
      = rationalSecantWitnessOne x₁ y₁ x₂ y₂ ^ 2 := by
  unfold rationalSecantSumX rationalSecantSlope rationalSecantWitnessOne
  field_simp [sub_ne_zero.mpr hx]
  linear_combination
    -(x₁ - x₂) * (1 - x₂) * h₁
      - (x₁ - x₂) * (x₁ - 1) * h₂

theorem ratSquareClass_eq_of_product_square
    {a b q : ℚ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : q ≠ 0)
    (h : a * b = q ^ 2) :
    squareClassOf ⟨a, ha⟩ = squareClassOf ⟨b, hb⟩ := by
  apply Quotient.sound
  refine ⟨⟨b, hb⟩, ⟨q, hq⟩, ?_⟩
  dsimp [nzRatMul]
  calc
    a * b ^ 2 = b * (a * b) := by ring
    _ = b * q ^ 2 := by rw [h]

theorem rationalSecantWitnessZero_ne_zero
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hxR : rationalSecantSumX x₁ y₁ x₂ y₂ ≠ 0) :
    rationalSecantWitnessZero x₁ y₁ x₂ y₂ ≠ 0 := by
  intro hw
  have hsq := rational_secant_x_square_identity h₁ h₂ hx
  rw [hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  exact mul_ne_zero (mul_ne_zero hxR hx₁) hx₂ hsq

theorem rationalSecantWitnessOne_ne_zero
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1)
    (hxR : rationalSecantSumX x₁ y₁ x₂ y₂ ≠ 1) :
    rationalSecantWitnessOne x₁ y₁ x₂ y₂ ≠ 0 := by
  intro hw
  have hsq := rational_secant_x_sub_one_square_identity h₁ h₂ hx
  rw [hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  exact mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr hxR) (sub_ne_zero.mpr hx₁))
    (sub_ne_zero.mpr hx₂) hsq

theorem rational_secant_first_squareClass_mul
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hxR : rationalSecantSumX x₁ y₁ x₂ y₂ ≠ 0) :
    squareClassOf ⟨rationalSecantSumX x₁ y₁ x₂ y₂, hxR⟩
      = squareClassOf ⟨x₁, hx₁⟩ * squareClassOf ⟨x₂, hx₂⟩ := by
  rw [← squareClassOf_mul]
  apply ratSquareClass_eq_of_product_square
    hxR (mul_ne_zero hx₁ hx₂)
    (rationalSecantWitnessZero_ne_zero h₁ h₂ hx hx₁ hx₂ hxR)
  simpa [nzRatMul, mul_assoc] using
    rational_secant_x_square_identity h₁ h₂ hx

theorem rational_secant_second_squareClass_mul
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂)
    (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1)
    (hxR : rationalSecantSumX x₁ y₁ x₂ y₂ ≠ 1) :
    squareClassOf
      ⟨rationalSecantSumX x₁ y₁ x₂ y₂ - 1, sub_ne_zero.mpr hxR⟩
      = squareClassOf ⟨x₁ - 1, sub_ne_zero.mpr hx₁⟩
          * squareClassOf ⟨x₂ - 1, sub_ne_zero.mpr hx₂⟩ := by
  rw [← squareClassOf_mul]
  apply ratSquareClass_eq_of_product_square
    (sub_ne_zero.mpr hxR)
    (mul_ne_zero (sub_ne_zero.mpr hx₁) (sub_ne_zero.mpr hx₂))
    (rationalSecantWitnessOne_ne_zero h₁ h₂ hx hx₁ hx₂ hxR)
  simpa [nzRatMul, mul_assoc] using
    rational_secant_x_sub_one_square_identity h₁ h₂ hx

theorem cmRational_slope_eq_secant
    {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    cmWeierstrass.toAffine.slope x₁ x₂ y₁ y₂
      = rationalSecantSlope x₁ y₁ x₂ y₂ := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rfl

theorem cmRational_addX_eq_secantSumX
    {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    cmWeierstrass.toAffine.addX x₁ x₂
      (cmWeierstrass.toAffine.slope x₁ x₂ y₁ y₂)
      = rationalSecantSumX x₁ y₁ x₂ y₂ := by
  rw [cmRational_slope_eq_secant hx]
  simp [rationalSecantSumX, WeierstrassCurve.Affine.addX, cmWeierstrass]

theorem cmRational_addY_eq_secantSumY
    {x₁ y₁ x₂ y₂ : ℚ} (hx : x₁ ≠ x₂) :
    cmWeierstrass.toAffine.addY x₁ x₂ y₁
      (cmWeierstrass.toAffine.slope x₁ x₂ y₁ y₂)
      = rationalSecantSumY x₁ y₁ x₂ y₂ := by
  rw [cmRational_slope_eq_secant hx]
  simp [rationalSecantSumY, rationalSecantSumX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    cmWeierstrass]

theorem rationalSecantSum_onCurve
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) :
    rationalSecantSumY x₁ y₁ x₂ y₂ ^ 2
      = rationalSecantSumX x₁ y₁ x₂ y₂ ^ 3
          - rationalSecantSumX x₁ y₁ x₂ y₂ := by
  have heq₁ := (cmWeierstrass_equation_iff x₁ y₁).mpr h₁
  have heq₂ := (cmWeierstrass_equation_iff x₂ y₂).mpr h₂
  have hadd := WeierstrassCurve.Affine.equation_add
    heq₁ heq₂ (fun hxy => hx hxy.1)
  rw [cmRational_addX_eq_secantSumX hx,
      cmRational_addY_eq_secantSumY hx] at hadd
  exact (cmWeierstrass_equation_iff
    (rationalSecantSumX x₁ y₁ x₂ y₂)
    (rationalSecantSumY x₁ y₁ x₂ y₂)).mp hadd

theorem rationalProjective_secant_add
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) :
    (.affine x₁ y₁ h₁ : RationalProjectivePoint)
      + .affine x₂ y₂ h₂
      = .affine
          (rationalSecantSumX x₁ y₁ x₂ y₂)
          (rationalSecantSumY x₁ y₁ x₂ y₂)
          (rationalSecantSum_onCurve h₁ h₂ hx) := by
  apply rationalProjectivePointEquivMathlib.injective
  rw [rationalProjective_add_transport]
  simp only [rationalProjectivePointEquivMathlib]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  congr
  · exact cmRational_addX_eq_secantSumX hx
  · exact cmRational_addY_eq_secantSumY hx

theorem totalGlobalKummer_secant_ordinary
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂)
    (hx₁0 : x₁ ≠ 0) (hx₁1 : x₁ ≠ 1)
    (hx₂0 : x₂ ≠ 0) (hx₂1 : x₂ ≠ 1)
    (hxR0 : rationalSecantSumX x₁ y₁ x₂ y₂ ≠ 0)
    (hxR1 : rationalSecantSumX x₁ y₁ x₂ y₂ ≠ 1) :
    totalGlobalKummer
      ((.affine x₁ y₁ h₁ : RationalProjectivePoint) + .affine x₂ y₂ h₂)
      = totalGlobalKummer (.affine x₁ y₁ h₁)
          * totalGlobalKummer (.affine x₂ y₂ h₂) := by
  rw [rationalProjective_secant_add h₁ h₂ hx]
  simp only [totalGlobalKummer]
  split_ifs with hR0 hR1 h10 h11 h20 h21
  · exact (hxR0 hR0).elim
  · exact (hxR1 hR1).elim
  · exact (hx₁0 h10).elim
  · exact (hx₁1 h11).elim
  · exact (hx₂0 h20).elim
  · exact (hx₂1 h21).elim
  · apply Prod.ext
    · exact rational_secant_first_squareClass_mul
        h₁ h₂ hx hx₁0 hx₂0 hxR0
    · exact rational_secant_second_squareClass_mul
        h₁ h₂ hx hx₁1 hx₂1 hxR1

def rationalTangentSlope (x y : ℚ) : ℚ :=
  (3 * x ^ 2 - 1) / (2 * y)

def rationalTangentSumX (x y : ℚ) : ℚ :=
  rationalTangentSlope x y ^ 2 - 2 * x

def rationalTangentSumY (x y : ℚ) : ℚ :=
  -(rationalTangentSlope x y * (rationalTangentSumX x y - x) + y)

def rationalTangentWitnessZero (x y : ℚ) : ℚ :=
  x * (x ^ 2 + 1) / (2 * y)

def rationalTangentWitnessOne (x y : ℚ) : ℚ :=
  (x - 1) * (x ^ 2 - 2 * x - 1) / (2 * y)

theorem rational_tangent_x_square_identity
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    rationalTangentSumX x y * x ^ 2
      = rationalTangentWitnessZero x y ^ 2 := by
  unfold rationalTangentSumX rationalTangentSlope rationalTangentWitnessZero
  field_simp [hy]
  linear_combination -8 * x ^ 3 * h

theorem rational_tangent_x_sub_one_square_identity
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    (rationalTangentSumX x y - 1) * (x - 1) ^ 2
      = rationalTangentWitnessOne x y ^ 2 := by
  unfold rationalTangentSumX rationalTangentSlope rationalTangentWitnessOne
  field_simp [hy]
  linear_combination -4 * (x - 1) ^ 2 * (2 * x + 1) * h

theorem ratSquareClass_eq_one_of_mul_self_square
    {a x q : ℚ} (ha : a ≠ 0) (hx : x ≠ 0) (hq : q ≠ 0)
    (h : a * x ^ 2 = q ^ 2) :
    squareClassOf ⟨a, ha⟩ = 1 := by
  apply Quotient.sound
  refine ⟨⟨x, hx⟩, nzRatOne, ?_⟩
  dsimp [nzRatOne]
  simpa using h

theorem rationalTangentWitnessZero_ne_zero
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0)
    (hx : x ≠ 0) (hxR : rationalTangentSumX x y ≠ 0) :
    rationalTangentWitnessZero x y ≠ 0 := by
  intro hw
  have hsq := rational_tangent_x_square_identity h hy
  rw [hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  exact mul_ne_zero hxR (pow_ne_zero 2 hx) hsq

theorem rationalTangentWitnessOne_ne_zero
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0)
    (hx : x ≠ 1) (hxR : rationalTangentSumX x y ≠ 1) :
    rationalTangentWitnessOne x y ≠ 0 := by
  intro hw
  have hsq := rational_tangent_x_sub_one_square_identity h hy
  rw [hw, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  exact mul_ne_zero (sub_ne_zero.mpr hxR)
    (pow_ne_zero 2 (sub_ne_zero.mpr hx)) hsq

theorem cmRational_negY_eq_neg (x y : ℚ) :
    cmWeierstrass.toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, cmWeierstrass]

theorem cmRational_y_ne_negY_of_ne_zero
    {x y : ℚ} (hy : y ≠ 0) :
    y ≠ cmWeierstrass.toAffine.negY x y := by
  rw [cmRational_negY_eq_neg]
  intro h
  have h2 : (2 : ℚ) * y = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with htwo | hy0
  · norm_num at htwo
  · exact hy hy0

theorem cmRational_tangent_slope_eq
    {x y : ℚ} (hy : y ≠ 0) :
    cmWeierstrass.toAffine.slope x x y y
      = rationalTangentSlope x y := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl
    (cmRational_y_ne_negY_of_ne_zero hy)]
  simp [rationalTangentSlope, cmWeierstrass,
    WeierstrassCurve.Affine.negY]
  ring

theorem cmRational_tangent_addX_eq
    {x y : ℚ} (hy : y ≠ 0) :
    cmWeierstrass.toAffine.addX x x
      (cmWeierstrass.toAffine.slope x x y y)
      = rationalTangentSumX x y := by
  rw [cmRational_tangent_slope_eq hy]
  simp [rationalTangentSumX, WeierstrassCurve.Affine.addX, cmWeierstrass]

theorem cmRational_tangent_addY_eq
    {x y : ℚ} (hy : y ≠ 0) :
    cmWeierstrass.toAffine.addY x x y
      (cmWeierstrass.toAffine.slope x x y y)
      = rationalTangentSumY x y := by
  rw [cmRational_tangent_slope_eq hy]
  simp [rationalTangentSumY, rationalTangentSumX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    cmWeierstrass]

theorem rationalTangentSum_onCurve
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    rationalTangentSumY x y ^ 2
      = rationalTangentSumX x y ^ 3 - rationalTangentSumX x y := by
  have heq := (cmWeierstrass_equation_iff x y).mpr h
  have hadd := WeierstrassCurve.Affine.equation_add
    heq heq (fun hxy => (cmRational_y_ne_negY_of_ne_zero hy) hxy.2)
  rw [cmRational_tangent_addX_eq hy, cmRational_tangent_addY_eq hy] at hadd
  exact (cmWeierstrass_equation_iff
    (rationalTangentSumX x y) (rationalTangentSumY x y)).mp hadd

theorem rationalProjective_tangent_double
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0) :
    (.affine x y h : RationalProjectivePoint) + .affine x y h
      = .affine (rationalTangentSumX x y) (rationalTangentSumY x y)
          (rationalTangentSum_onCurve h hy) := by
  apply rationalProjectivePointEquivMathlib.injective
  rw [rationalProjective_add_transport]
  simp only [rationalProjectivePointEquivMathlib]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (cmRational_y_ne_negY_of_ne_zero hy)]
  congr
  · exact cmRational_tangent_addX_eq hy
  · exact cmRational_tangent_addY_eq hy

theorem totalGlobalKummer_tangent_ordinary
    {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) (hy : y ≠ 0)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hxR0 : rationalTangentSumX x y ≠ 0)
    (hxR1 : rationalTangentSumX x y ≠ 1) :
    totalGlobalKummer
      ((.affine x y h : RationalProjectivePoint) + .affine x y h)
      = totalGlobalKummer (.affine x y h) * totalGlobalKummer (.affine x y h) := by
  rw [rationalProjective_tangent_double h hy]
  simp only [totalGlobalKummer]
  split_ifs with hR0 hR1 h0 h1 h0' h1'
  · exact (hxR0 hR0).elim
  · exact (hxR1 hR1).elim
  · exact (hx0 h0).elim
  · exact (hx1 h1).elim
  · exact (hx0 h0').elim
  · exact (hx1 h1').elim
  · apply Prod.ext
    · calc
        squareClassOf ⟨rationalTangentSumX x y, hxR0⟩ = 1 :=
          ratSquareClass_eq_one_of_mul_self_square hxR0 hx0
            (rationalTangentWitnessZero_ne_zero h hy hx0 hxR0)
            (rational_tangent_x_square_identity h hy)
        _ = squareClassOf ⟨x, hx0⟩ * squareClassOf ⟨x, hx0⟩ := by
          symm; exact ratSquareClass_sq_eq_one _
    · calc
        squareClassOf
            ⟨rationalTangentSumX x y - 1, sub_ne_zero.mpr hxR1⟩ = 1 :=
          ratSquareClass_eq_one_of_mul_self_square
            (sub_ne_zero.mpr hxR1) (sub_ne_zero.mpr hx1)
            (rationalTangentWitnessOne_ne_zero h hy hx1 hxR1)
            (rational_tangent_x_sub_one_square_identity h hy)
        _ = squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩
              * squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩ := by
          symm; exact ratSquareClass_sq_eq_one _

theorem rational_affine_y_eq_or_eq_neg_of_same_x
    {x y₁ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x ^ 3 - x)
    (h₂ : y₂ ^ 2 = x ^ 3 - x) :
    y₁ = y₂ ∨ y₁ = -y₂ := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  exact h₁.trans h₂.symm

theorem rational_same_x_noninverse_forces_same_y
    {x y₁ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x ^ 3 - x)
    (h₂ : y₂ ^ 2 = x ^ 3 - x)
    (hQnegP :
      (.affine x y₂ h₂ : RationalProjectivePoint)
        ≠ -(.affine x y₁ h₁ : RationalProjectivePoint)) :
    y₁ = y₂ := by
  rcases rational_affine_y_eq_or_eq_neg_of_same_x h₁ h₂ with h | h
  · exact h
  · exfalso
    apply hQnegP
    rw [rationalProjective_neg_affine x y₁ h₁]
    congr
    exact h.symm

theorem rational_same_x_noninverse_y_ne_zero
    {x y₁ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x ^ 3 - x)
    (h₂ : y₂ ^ 2 = x ^ 3 - x)
    (hQnegP :
      (.affine x y₂ h₂ : RationalProjectivePoint)
        ≠ -(.affine x y₁ h₁ : RationalProjectivePoint)) :
    y₁ ≠ 0 := by
  have hy := rational_same_x_noninverse_forces_same_y h₁ h₂ hQnegP
  intro hy0
  apply hQnegP
  rw [rationalProjective_neg_affine x y₁ h₁]
  congr
  calc y₂ = y₁ := hy.symm
       _ = 0 := hy0
       _ = -y₁ := by simp [hy0]

theorem totalGlobalKummer_affine_ordinary
    {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx₁0 : x₁ ≠ 0) (hx₁1 : x₁ ≠ 1)
    (hx₂0 : x₂ ≠ 0) (hx₂1 : x₂ ≠ 1)
    (hQnegP :
      (.affine x₂ y₂ h₂ : RationalProjectivePoint)
        ≠ -(.affine x₁ y₁ h₁ : RationalProjectivePoint))
    (hSumOrd : ∃ xR yR hR,
      (.affine x₁ y₁ h₁ : RationalProjectivePoint) + .affine x₂ y₂ h₂
        = .affine xR yR hR ∧ xR ≠ 0 ∧ xR ≠ 1) :
    totalGlobalKummer
      ((.affine x₁ y₁ h₁ : RationalProjectivePoint) + .affine x₂ y₂ h₂)
      = totalGlobalKummer (.affine x₁ y₁ h₁)
          * totalGlobalKummer (.affine x₂ y₂ h₂) := by
  by_cases hx : x₁ = x₂
  · subst x₂
    have hy := rational_same_x_noninverse_forces_same_y h₁ h₂ hQnegP
    subst y₂
    have hy0 := rational_same_x_noninverse_y_ne_zero h₁ h₁ hQnegP
    rcases hSumOrd with ⟨xR, yR, hR, hsum, hxR0, hxR1⟩
    have htan := rationalProjective_tangent_double h₁ hy0
    have hxEq : rationalTangentSumX x₁ y₁ = xR := by
      rw [htan] at hsum; cases hsum; rfl
    apply totalGlobalKummer_tangent_ordinary h₁ hy0 hx₁0 hx₁1
    · rwa [hxEq]
    · rwa [hxEq]
  · have hsec := rationalProjective_secant_add h₁ h₂ hx
    rcases hSumOrd with ⟨xR, yR, hR, hsum, hxR0, hxR1⟩
    have hxEq : rationalSecantSumX x₁ y₁ x₂ y₂ = xR := by
      rw [hsec] at hsum; cases hsum; rfl
    apply totalGlobalKummer_secant_ordinary
      h₁ h₂ hx hx₁0 hx₁1 hx₂0 hx₂1
    · rwa [hxEq]
    · rwa [hxEq]

end Synthesis.Millennium.BSD
