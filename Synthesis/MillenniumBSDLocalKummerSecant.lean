import Synthesis.MillenniumBSDLocalKummerBoundaryCases
import Synthesis.MillenniumBSDSquareClassGroups
import Mathlib.Tactic

/-!
# Secant-case Kummer multiplicativity for y² = x³ - x

For two affine points P=(x₁,y₁), Q=(x₂,y₂) with x₁ ≠ x₂, let

  λ  = (y₁-y₂)/(x₁-x₂),
  xR = λ²-x₁-x₂.

Then direct algebra on the curve proves

  xR*x₁*x₂
    = ((y₁*x₂-y₂*x₁)/(x₁-x₂))²,

and

  (xR-1)*(x₁-1)*(x₂-1)
    = ((y₁*(x₂-1)-y₂*(x₁-1))/(x₁-x₂))².

These are the classical two-descent identities.  They immediately imply the
two square-class coordinates of R=P+Q are the products of the corresponding
coordinates of P and Q whenever all ordinary coordinates are nonzero.
-/

namespace Synthesis.Millennium.BSD

def secantSlope
    {p : ℕ} [Fact p.Prime]
    (x₁ y₁ x₂ y₂ : ℚ_[p]) : ℚ_[p] :=
  (y₁ - y₂) / (x₁ - x₂)

def secantSumX
    {p : ℕ} [Fact p.Prime]
    (x₁ y₁ x₂ y₂ : ℚ_[p]) : ℚ_[p] :=
  (secantSlope x₁ y₁ x₂ y₂) ^ 2 - x₁ - x₂

def secantKummerWitnessZero
    {p : ℕ} [Fact p.Prime]
    (x₁ y₁ x₂ y₂ : ℚ_[p]) : ℚ_[p] :=
  (y₁ * x₂ - y₂ * x₁) / (x₁ - x₂)

def secantKummerWitnessOne
    {p : ℕ} [Fact p.Prime]
    (x₁ y₁ x₂ y₂ : ℚ_[p]) : ℚ_[p] :=
  (y₁ * (x₂ - 1) - y₂ * (x₁ - 1)) / (x₁ - x₂)

theorem secant_x_square_identity
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) :
    secantSumX x₁ y₁ x₂ y₂ * x₁ * x₂
      =
    (secantKummerWitnessZero x₁ y₁ x₂ y₂) ^ 2 := by
  unfold secantSumX secantSlope secantKummerWitnessZero
  field_simp [sub_ne_zero.mpr hx]
  nlinarith [h₁, h₂]

theorem secant_x_sub_one_square_identity
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂) :
    (secantSumX x₁ y₁ x₂ y₂ - 1)
        * (x₁ - 1) * (x₂ - 1)
      =
    (secantKummerWitnessOne x₁ y₁ x₂ y₂) ^ 2 := by
  unfold secantSumX secantSlope secantKummerWitnessOne
  field_simp [sub_ne_zero.mpr hx]
  nlinarith [h₁, h₂]

theorem padicSquareClass_eq_of_product_square
    {p : ℕ} [Fact p.Prime]
    {a b q : ℚ_[p]}
    (ha : a ≠ 0) (hb : b ≠ 0) (hq : q ≠ 0)
    (h : a * b = q ^ 2) :
    padicSquareClassOf p ⟨a, ha⟩
      =
    padicSquareClassOf p ⟨b, hb⟩ := by
  apply Quotient.sound
  refine ⟨⟨b, hb⟩, ⟨q, hq⟩, ?_⟩
  dsimp [nzPadicMul]
  calc
    a * b ^ 2 = b * (a * b) := by ring
    _ = b * q ^ 2 := by rw [h]

@[simp] theorem padicSquareClassOf_mul
    (p : ℕ) [Fact p.Prime]
    (a b : NonzeroPadic p) :
    padicSquareClassOf p (nzPadicMul p a b)
      =
    padicSquareClassOf p a * padicSquareClassOf p b := rfl

theorem secant_first_squareClass_mul
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hxR : secantSumX x₁ y₁ x₂ y₂ ≠ 0)
    (hw : secantKummerWitnessZero x₁ y₁ x₂ y₂ ≠ 0) :
    padicSquareClassOf p
      ⟨secantSumX x₁ y₁ x₂ y₂, hxR⟩
      =
    padicSquareClassOf p ⟨x₁, hx₁⟩
      * padicSquareClassOf p ⟨x₂, hx₂⟩ := by
  rw [← padicSquareClassOf_mul]
  apply padicSquareClass_eq_of_product_square
    hxR (mul_ne_zero hx₁ hx₂) hw
  simpa [nzPadicMul, mul_assoc] using
    secant_x_square_identity h₁ h₂ hx

theorem secant_second_squareClass_mul
    {p : ℕ} [Fact p.Prime]
    {x₁ y₁ x₂ y₂ : ℚ_[p]}
    (h₁ : y₁ ^ 2 = x₁ ^ 3 - x₁)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 - x₂)
    (hx : x₁ ≠ x₂)
    (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1)
    (hxR : secantSumX x₁ y₁ x₂ y₂ ≠ 1)
    (hw : secantKummerWitnessOne x₁ y₁ x₂ y₂ ≠ 0) :
    padicSquareClassOf p
      ⟨secantSumX x₁ y₁ x₂ y₂ - 1, sub_ne_zero.mpr hxR⟩
      =
    padicSquareClassOf p ⟨x₁ - 1, sub_ne_zero.mpr hx₁⟩
      * padicSquareClassOf p ⟨x₂ - 1, sub_ne_zero.mpr hx₂⟩ := by
  rw [← padicSquareClassOf_mul]
  apply padicSquareClass_eq_of_product_square
    (sub_ne_zero.mpr hxR)
    (mul_ne_zero (sub_ne_zero.mpr hx₁) (sub_ne_zero.mpr hx₂))
    hw
  simpa [nzPadicMul, mul_assoc] using
    secant_x_sub_one_square_identity h₁ h₂ hx

end Synthesis.Millennium.BSD
