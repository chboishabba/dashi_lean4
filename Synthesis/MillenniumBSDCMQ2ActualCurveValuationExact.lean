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


/-- Integer valuation of minus one in the genuine 2-adic field.
Derived from the multiplicative valuation of (-1)^2=1. -/
theorem cmQ2Valuation_negOne :
    ((-1 : ℚ_[2]).valuation) = 0 := by
  have h : (2 : ℤ) * ((-1 : ℚ_[2]).valuation) = 0 := by
    calc
      (2 : ℤ) * ((-1 : ℚ_[2]).valuation) =
          (((-1 : ℚ_[2]) ^ 2).valuation) := by
            rw [Padic.valuation_pow]
            ring
      _ = 0 := by norm_num [Padic.valuation_one]
  omega

/-- Genuine p-adic valuation is invariant under negation away from zero. -/
theorem cmQ2Valuation_neg (x : ℚ_[2]) (hx : x ≠ 0) :
    (-x).valuation = x.valuation := by
  calc
    (-x).valuation = ((-1 : ℚ_[2]) * x).valuation := by
      congr 1
      ring
    _ = ((-1 : ℚ_[2]).valuation) + x.valuation :=
      Padic.valuation_mul (by norm_num) hx
    _ = x.valuation := by rw [cmQ2Valuation_negOne]; omega

/-- The strict-min ultrametric valuation law on the ACTUAL Q_2 field,
derived from Mathlib's min <= valuation(add) inequality in both directions. -/
theorem cmQ2Valuation_add_of_lt
    (a b : ℚ_[2])
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0)
    (hlt : a.valuation < b.valuation) :
    (a + b).valuation = a.valuation := by
  have hforward : a.valuation ≤ (a + b).valuation := by
    have h := Padic.le_valuation_add hab
    simpa [min_eq_left (le_of_lt hlt)] using h
  have hback : min (a + b).valuation b.valuation ≤ a.valuation := by
    have h : (a + b) + (-b) ≠ 0 := by
      simpa [add_assoc] using ha
    have hh := Padic.le_valuation_add h
    rw [cmQ2Valuation_neg b hb] at hh
    simpa [add_assoc] using hh
  have hreverse : (a + b).valuation ≤ a.valuation := by
    by_contra hcontra
    have hg : a.valuation < (a + b).valuation := lt_of_not_ge hcontra
    have hmin : a.valuation < min (a + b).valuation b.valuation :=
      lt_min hg hlt
    omega
  exact le_antisymm hreverse hforward

/-- Positive actual 2-adic valuation means both x±1 are units. -/
theorem cmQ2ShiftedValuationPositive
    (x : ℚ_[2]) (hx : 0 < x.valuation) :
    (x - 1).valuation = 0 ∧ (x + 1).valuation = 0 := by
  have hxne : x ≠ 0 := by
    intro h
    simp [h, Padic.valuation_zero] at hx
  have hxone : x ≠ 1 := by
    intro h
    simp [h, Padic.valuation_one] at hx
  have hxnegone : x ≠ -1 := by
    intro h
    rw [h, cmQ2Valuation_negOne] at hx
    omega
  have hxplus : x + 1 ≠ 0 := by
    intro heq
    apply hxnegone
    calc
      x = (x + 1) - 1 := by ring
      _ = -1 := by rw [heq]; ring
  constructor
  · have h := cmQ2Valuation_add_of_lt
      (-1 : ℚ_[2]) x (by norm_num) hxne
      (by simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hxone)
      (by rw [cmQ2Valuation_negOne]; exact hx)
    simpa [sub_eq_add_neg, add_comm, cmQ2Valuation_negOne] using h
  · have h := cmQ2Valuation_add_of_lt
      (1 : ℚ_[2]) x (by norm_num) hxne
      (by simpa [add_comm] using hxplus)
      (by simpa [Padic.valuation_one] using hx)
    simpa [add_comm, Padic.valuation_one] using h

/-- Negative actual 2-adic valuation is inherited by x±1. -/
theorem cmQ2ShiftedValuationNegative
    (x : ℚ_[2]) (hx : x.valuation < 0) :
    (x - 1).valuation = x.valuation ∧
      (x + 1).valuation = x.valuation := by
  have hxne : x ≠ 0 := by
    intro h
    simp [h, Padic.valuation_zero] at hx
  have hxone : x ≠ 1 := by
    intro h
    simp [h, Padic.valuation_one] at hx
  have hxnegone : x ≠ -1 := by
    intro h
    rw [h, cmQ2Valuation_negOne] at hx
    omega
  have hxplus : x + 1 ≠ 0 := by
    intro heq
    apply hxnegone
    calc
      x = (x + 1) - 1 := by ring
      _ = -1 := by rw [heq]; ring
  constructor
  · have h := cmQ2Valuation_add_of_lt
      x (-1 : ℚ_[2]) hxne (by norm_num)
      (by simpa [sub_eq_add_neg] using sub_ne_zero.mpr hxone)
      (by rw [cmQ2Valuation_negOne]; exact hx)
    simpa [sub_eq_add_neg] using h
  · have h := cmQ2Valuation_add_of_lt
      x (1 : ℚ_[2]) hxne (by norm_num)
      hxplus
      (by simpa [Padic.valuation_one] using hx)
    exact h

/-- Actual nonexceptional Q_2 points of y²=x³-x have even
integer 2-adic valuation in their first ordinary x-T coordinate. -/
theorem cmQ2NonexceptionalXValuationEven
    (x y : ℚ_[2]) (hcurve : y ^ 2 = x ^ 3 - x)
    (hy : y ≠ 0) :
    Even x.valuation := by
  apply cmQ2ValuationParity_of_shiftedValuations x y hcurve hy
  · exact cmQ2ShiftedValuationPositive x
  · exact cmQ2ShiftedValuationNegative x

end Synthesis.Millennium.BSD
