import Mathlib

namespace Synthesis.KottlerHorizonRoots

/-- Horizon polynomial for M=1/4, Λ=3/16 after clearing the positive factor 16r. -/
def horizonPolynomial (r : ℝ) : ℝ := r ^ 3 - 16 * r + 8

@[simp] theorem innerLeft_value : horizonPolynomial (1 / 2 : ℝ) = 1 / 8 := by
  norm_num [horizonPolynomial]

@[simp] theorem innerRight_value :
    horizonPolynomial (13 / 25 : ℝ) = -(2803 / 15625 : ℝ) := by
  norm_num [horizonPolynomial]

@[simp] theorem outerLeft_value :
    horizonPolynomial (37 / 10 : ℝ) = -(547 / 1000 : ℝ) := by
  norm_num [horizonPolynomial]

@[simp] theorem outerRight_value :
    horizonPolynomial (15 / 4 : ℝ) = 47 / 64 := by
  norm_num [horizonPolynomial]

private theorem horizonPolynomial_continuous : Continuous horizonPolynomial := by
  fun_prop

/-- The black-hole-side positive Kottler horizon exists in the rational bracket [1/2,13/25]. -/
theorem innerHorizon_exists :
    ∃ r ∈ Set.Icc (1 / 2 : ℝ) (13 / 25 : ℝ), horizonPolynomial r = 0 := by
  have hab : (1 / 2 : ℝ) ≤ 13 / 25 := by norm_num
  have hcont := horizonPolynomial_continuous.continuousOn
  have himg := intermediate_value_Icc' hab hcont
  have hz : (0 : ℝ) ∈ Set.Icc (horizonPolynomial (13 / 25 : ℝ)) (horizonPolynomial (1 / 2 : ℝ)) := by
    constructor <;> norm_num [horizonPolynomial]
  rcases himg hz with ⟨r, hr, hzero⟩
  exact ⟨r, hr, hzero⟩

/-- The cosmological-side positive Kottler horizon exists in [37/10,15/4]. -/
theorem outerHorizon_exists :
    ∃ r ∈ Set.Icc (37 / 10 : ℝ) (15 / 4 : ℝ), horizonPolynomial r = 0 := by
  have hab : (37 / 10 : ℝ) ≤ 15 / 4 := by norm_num
  have hcont := horizonPolynomial_continuous.continuousOn
  have himg := intermediate_value_Icc hab hcont
  have hz : (0 : ℝ) ∈ Set.Icc (horizonPolynomial (37 / 10 : ℝ)) (horizonPolynomial (15 / 4 : ℝ)) := by
    constructor <;> norm_num [horizonPolynomial]
  rcases himg hz with ⟨r, hr, hzero⟩
  exact ⟨r, hr, hzero⟩

def realPositiveHorizonExistenceOwned : Bool := true

def maximalAnalyticExtensionStillRequired : Bool := true

def globalGeodesicCompletenessStillRequired : Bool := true

end Synthesis.KottlerHorizonRoots
