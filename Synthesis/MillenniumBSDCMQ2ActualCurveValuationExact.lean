import Synthesis.MillenniumBSDCMTwoAdicValuationArithmeticExact
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

/-!
# BSD: original Q_2 curve equation under the actual integer p-adic valuation

This proves the genuine valuation identity for affine points of
E : y² = x³ - x over Q_[2], not just a free integer trichotomy.

The integer-valued Padic.valuation is essential: the natural-valued
padicValNat cannot represent negative valuations of Q_2 coordinates.

The shifted-valuation ultrametric implications and the map from
valuation parity to the repository's literal local square-class
representation are not constructed in this file and remain open.

Source: Mathlib.NumberTheory.Padics.PadicNumbers,
Padic.valuation_mul, Padic.valuation_pow.
-/

namespace Synthesis.Millennium.BSD

/-- The original affine cubic has the exact split-factor form over Q_2. -/
theorem cmQ2Affine_factorization
    (x y : ℚ_[2]) (hcurve : y ^ 2 = x ^ 3 - x) :
    y ^ 2 = x * (x - 1) * (x + 1) := by
  calc
    y ^ 2 = x ^ 3 - x := hcurve
    _ = x * (x - 1) * (x + 1) := by ring

/-- A nonexceptional Q_2 curve point has nonzero x and shifted factors. -/
theorem cmQ2Affine_nonzero_factors
    (x y : ℚ_[2]) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    x ≠ 0 ∧ x - 1 ≠ 0 ∧ x + 1 ≠ 0 := by
  have hfactor := cmQ2Affine_factorization x y hcurve
  have hprod : x * (x - 1) * (x + 1) ≠ 0 := by
    rw [← hfactor]
    exact pow_ne_zero 2 hy
  have hx : x ≠ 0 := by
    intro hzero
    simp [hzero] at hprod
  have hm : x - 1 ≠ 0 := by
    intro hzero
    rw [hzero] at hprod
    simp at hprod
  have hp : x + 1 ≠ 0 := by
    intro hzero
    rw [hzero] at hprod
    simp at hprod
  exact ⟨hx, hm, hp⟩

/-- The genuine integer-valued 2-adic valuations of the original
affine equation satisfy the exact sum relation. -/
theorem cmQ2ValuationCurveIdentity
    (x y : ℚ_[2]) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    2 * y.valuation =
      x.valuation + (x - 1).valuation + (x + 1).valuation := by
  obtain ⟨hx, hm, hp⟩ := cmQ2Affine_nonzero_factors x y hcurve hy
  have hfactor := cmQ2Affine_factorization x y hcurve
  calc
    2 * y.valuation = (y ^ 2).valuation := by
      rw [Padic.valuation_pow]
      ring
    _ = (x * (x - 1) * (x + 1)).valuation := by rw [hfactor]
    _ = x.valuation + (x - 1).valuation + (x + 1).valuation := by
      rw [Padic.valuation_mul (mul_ne_zero hx hm) hp]
      rw [Padic.valuation_mul hx hm]

/-- Same Q_2 curve, original field valuations. Only the two genuine
ultrametric shifted-valuation implications are assumed. Their proof
must use the Q_2 valuation API, not an invented arithmetic carrier. -/
theorem cmQ2ValuationParity_of_shiftedValuations
    (x y : ℚ_[2]) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0)
    (hPos :
      0 < x.valuation →
        (x - 1).valuation = 0 ∧ (x + 1).valuation = 0)
    (hNeg :
      x.valuation < 0 →
        (x - 1).valuation = x.valuation ∧
          (x + 1).valuation = x.valuation) :
    Even x.valuation := by
  exact cmTwoAdicValuationParity_even
    x.valuation y.valuation (x - 1).valuation (x + 1).valuation
    (cmQ2ValuationCurveIdentity x y hcurve hy) hPos hNeg

end Synthesis.Millennium.BSD
