import Synthesis.MillenniumBSDCMHasseBound
import Synthesis.MillenniumBSDFullGlobalAnalyticLFunction
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Hasse-strength Euler convergence for Re(s) > 3/2

The Hasse bound |a_p| <= 2 sqrt(p) sharpens the primewise perturbation to

  ||-a_p p^{-s} + p p^{-2s}||
    <= 2 p^(1/2-Re(s)) + p^(1-2Re(s)).

Both prime sums converge for Re(s)>3/2.  Since the p=2 factor is exactly 1,
this is a theorem about the complete literal global Euler product.
-/

namespace Synthesis.Millennium.BSD

def hasseEulerMajorant (p : Nat.Primes) (s : ℂ) : ℝ :=
  2 * (p.1 : ℝ) ^ ((1 : ℝ) / 2 - s.re)
    + (p.1 : ℝ) ^ (1 - 2 * s.re)

theorem hasseEulerMajorant_summable
    {s : ℂ} (hs : (3 : ℝ) / 2 < s.re) :
    Summable fun p : Nat.Primes => hasseEulerMajorant p s := by
  unfold hasseEulerMajorant
  apply Summable.add
  · exact (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left 2
  · exact Nat.Primes.summable_rpow.mpr (by linarith)

theorem explicitEulerPerturbation_norm_le_hasseMajorant
    {s : ℂ} (hs : (3 : ℝ) / 2 < s.re)
    (p : Nat.Primes) :
    ‖explicitEulerPerturbation p s‖ ≤ hasseEulerMajorant p s := by
  by_cases hp2 : p.1 = 2
  · simp [explicitEulerPerturbation, hasseEulerMajorant, hp2]
    positivity
  · letI : Fact p.1.Prime := ⟨p.2⟩
    have hpR : 0 < (p.1 : ℝ) := by positivity
    have hcoefReal :
        |(frobeniusCoefficient p.1 : ℝ)| ≤
          2 * Real.sqrt (p.1 : ℝ) :=
      frobeniusCoefficient_abs_le_two_mul_sqrt hp2
    have hcoef :
        ‖(frobeniusCoefficient p.1 : ℂ)‖ ≤
          2 * (p.1 : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Complex.norm_intCast]
      norm_cast at hcoefReal ⊢
      simpa [Real.sqrt_eq_rpow] using hcoefReal
    have hpow1 :
        ‖(p.1 : ℂ) ^ (-s)‖ = (p.1 : ℝ) ^ (-s.re) := by
      simpa using norm_natCast_cpow_of_pos p.2.pos (-s)
    have hpow2 :
        ‖(p.1 : ℂ) ^ (-(2 : ℂ) * s)‖ =
          (p.1 : ℝ) ^ (-2 * s.re) := by
      simpa using norm_natCast_cpow_of_pos p.2.pos (-(2 : ℂ) * s)
    have hfirst :
        (2 * (p.1 : ℝ) ^ ((1 : ℝ)/2)) *
            (p.1 : ℝ)^(-s.re)
          = 2 * (p.1 : ℝ)^((1 : ℝ)/2 - s.re) := by
      rw [mul_assoc, ← Real.rpow_add hpR]
      congr 2
      ring
    have hsecond :
        (p.1 : ℝ) * (p.1 : ℝ)^(-2*s.re)
          = (p.1 : ℝ)^(1-2*s.re) := by
      rw [show (p.1 : ℝ) = (p.1 : ℝ)^((1 : ℝ)) by rw [Real.rpow_one],
        ← Real.rpow_add hpR]
      congr 2
      ring
    rw [explicitEulerPerturbation, dif_neg hp2]
    calc
      ‖-(frobeniusCoefficient p.1 : ℂ) * (p.1 : ℂ)^(-s)
          + (p.1 : ℂ) * (p.1 : ℂ)^(-(2 : ℂ)*s)‖
        ≤ ‖(frobeniusCoefficient p.1 : ℂ)‖ * ‖(p.1 : ℂ)^(-s)‖
          + ‖(p.1 : ℂ)‖ * ‖(p.1 : ℂ)^(-(2 : ℂ)*s)‖ := by
            simpa [norm_mul] using norm_add_le
              (-(frobeniusCoefficient p.1 : ℂ) * (p.1 : ℂ)^(-s))
              ((p.1 : ℂ) * (p.1 : ℂ)^(-(2 : ℂ)*s))
      _ ≤ (2 * (p.1 : ℝ)^((1 : ℝ)/2)) * (p.1 : ℝ)^(-s.re)
          + (p.1 : ℝ) * (p.1 : ℝ)^(-2*s.re) := by
            rw [hpow1, hpow2]
            gcongr
      _ = hasseEulerMajorant p s := by
            rw [hfirst, hsecond]
            rfl

theorem explicitEulerPerturbation_summable_hasse
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    Summable fun p : Nat.Primes => explicitEulerPerturbation p s := by
  exact ((hasseEulerMajorant_summable hs).of_nonneg_of_le
    (fun p => norm_nonneg (explicitEulerPerturbation p s))
    (explicitEulerPerturbation_norm_le_hasseMajorant hs)).of_norm

theorem hasseEulerMajorant_lt_one_of_odd_prime
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re)
    (p : Nat.Primes) (hp2 : p.1 ≠ 2) :
    hasseEulerMajorant p s < 1 := by
  have hp3 : (3 : ℝ) ≤ p.1 := by
    exact_mod_cast p.2.three_le_of_ne_two hp2
  have hp1 : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hfirst :
      (p.1 : ℝ)^((1 : ℝ)/2-s.re) < (p.1 : ℝ)^(-1) := by
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hsecond :
      (p.1 : ℝ)^(1-2*s.re) < (p.1 : ℝ)^(-2) := by
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hinv : (p.1 : ℝ)^(-1) ≤ (3 : ℝ)^(-1) := by
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    exact one_div_le_one_div_of_le (by norm_num) hp3
  have hinv2 : (p.1 : ℝ)^(-2) ≤ (3 : ℝ)^(-2) := by
    rw [show (-2 : ℝ) = - (2 : ℝ) by norm_num, Real.rpow_neg, Real.rpow_neg]
    gcongr
    exact Real.rpow_le_rpow (by positivity) hp3 (by norm_num)
  unfold hasseEulerMajorant
  calc
    2 * (p.1 : ℝ)^((1 : ℝ)/2-s.re) + (p.1 : ℝ)^(1-2*s.re)
      < 2 * (p.1 : ℝ)^(-1) + (p.1 : ℝ)^(-2) := by linarith
    _ ≤ 2 * (3 : ℝ)^(-1) + (3 : ℝ)^(-2) := by gcongr
    _ < 1 := by norm_num [Real.rpow_neg_one, Real.rpow_neg]

theorem explicitEulerPerturbation_norm_lt_one_hasse
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) (p : Nat.Primes) :
    ‖explicitEulerPerturbation p s‖ < 1 := by
  by_cases hp2 : p.1 = 2
  · simp [explicitEulerPerturbation, hp2]
  · exact (explicitEulerPerturbation_norm_le_hasseMajorant hs p).trans_lt
      (hasseEulerMajorant_lt_one_of_odd_prime hs p hp2)

theorem explicitEulerDenominator_ne_zero_hasse
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) (p : Nat.Primes) :
    explicitEulerDenominator p s ≠ 0 := by
  intro hzero
  have hu : explicitEulerPerturbation p s = -1 := by
    simp only [explicitEulerDenominator] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have := explicitEulerPerturbation_norm_lt_one_hasse hs p
  rw [hu] at this
  simpa using this

theorem explicitEulerDenominators_multipliable_hasse
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    Multipliable fun p : Nat.Primes => explicitEulerDenominator p s := by
  simpa [explicitEulerDenominator] using
    multipliable_one_add_of_summable
      (explicitEulerPerturbation_summable_hasse hs).norm

theorem explicitEulerDenominatorProduct_ne_zero_hasse
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    explicitEulerDenominatorProduct s ≠ 0 := by
  unfold explicitEulerDenominatorProduct
  apply tprod_one_add_ne_zero_of_summable
  · intro p
    simpa [explicitEulerDenominator] using
      explicitEulerDenominator_ne_zero_hasse hs p
  · exact (explicitEulerPerturbation_summable_hasse hs).norm

theorem explicitAnalyticEulerProduct_ne_zero_hasse
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    explicitAnalyticEulerProduct s ≠ 0 := by
  exact inv_ne_zero (explicitEulerDenominatorProduct_ne_zero_hasse hs)

theorem cmActualGlobalEulerDenominatorProduct_ne_zero_hasse
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    cmActualGlobalEulerDenominatorProduct s ≠ 0 := by
  rw [cmActualGlobalEulerDenominatorProduct_eq_previous,
    cmPrimeToTwoEulerDenominatorProduct_eq_explicit]
  exact explicitEulerDenominatorProduct_ne_zero_hasse hs

theorem cmActualGlobalAnalyticEulerProduct_ne_zero_hasse
    {s : ℂ} (hs : (3 : ℝ)/2 < s.re) :
    cmActualGlobalAnalyticEulerProduct s ≠ 0 := by
  exact inv_ne_zero (cmActualGlobalEulerDenominatorProduct_ne_zero_hasse hs)

end Synthesis.Millennium.BSD
