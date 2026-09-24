import Synthesis.MillenniumBSDChebyshevUBound
import Synthesis.MillenniumBSDCMHasseBound
import Synthesis.MillenniumBSDExplicitLocalRecurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Hasse-strength bounds for prime-power Euler coefficients

For an odd prime p, put r = sqrt(p) and x = a_p/r.  The reciprocal Euler
coefficients satisfy

  A_p(k) = r^k S_k(x),

where S is the rescaled Chebyshev polynomial of the second kind.  Hasse gives
|x| <= 2, while the uniform Chebyshev bound gives |S_k(x)| <= k+1.  Hence

  |A_p(k)| <= (k+1) p^(k/2).
-/

namespace Synthesis.Millennium.BSD

open Polynomial
open Polynomial.Chebyshev

theorem sqrt_prime_pos
    {p : ℕ} (hp : p.Prime) :
    0 < Real.sqrt (p : ℝ) := by
  exact Real.sqrt_pos.2 (by exact_mod_cast hp.pos)

theorem sqrt_prime_ne_zero
    {p : ℕ} (hp : p.Prime) :
    Real.sqrt (p : ℝ) ≠ 0 :=
  ne_of_gt (sqrt_prime_pos hp)

theorem sqrt_prime_sq
    {p : ℕ} (hp : p.Prime) :
    (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) := by
  rw [sq_sqrt]
  positivity

theorem frobenius_normalized_abs_le_two
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) :
    |(frobeniusCoefficient p : ℝ) / Real.sqrt p| ≤ 2 := by
  have hsqrt := sqrt_prime_pos hp.out
  have hhasse := frobeniusCoefficient_abs_le_two_mul_sqrt hp2
  rw [abs_div, abs_of_pos hsqrt]
  exact (div_le_iff₀ hsqrt).2 (by
    simpa [mul_assoc] using hhasse)

theorem explicitPrimePowerCoefficient_eq_sqrt_pow_chebyshevS
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) :
    ∀ k : ℕ,
      (explicitPrimePowerCoefficient p k : ℝ)
        = (Real.sqrt p) ^ k *
            (S ℝ (k : ℤ)).eval
              ((frobeniusCoefficient p : ℝ) / Real.sqrt p) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp [explicitPrimePowerCoefficient]
  | one =>
      have hsqrt0 : Real.sqrt (p : ℝ) ≠ 0 := sqrt_prime_ne_zero hp.out
      simp [explicitPrimePowerCoefficient, S_one]
      field_simp
  | more k hk hk1 =>
      rw [explicitPrimePowerCoefficient_recurrence]
      push_cast
      rw [S_add_two]
      simp only [eval_sub, eval_mul, eval_X]
      rw [hk, hk1]
      have hsqrt2 := sqrt_prime_sq hp.out
      have hsqrt0 : Real.sqrt (p : ℝ) ≠ 0 := sqrt_prime_ne_zero hp.out
      field_simp
      ring_nf at hsqrt2 ⊢
      nlinarith

theorem explicitPrimePowerCoefficient_abs_le_hasse
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    |(explicitPrimePowerCoefficient p k : ℝ)|
      ≤ (k + 1) * (Real.sqrt p) ^ k := by
  rw [explicitPrimePowerCoefficient_eq_sqrt_pow_chebyshevS hp2 k]
  rw [abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hS := chebyshevS_abs_le_natSucc k
    (frobenius_normalized_abs_le_two hp2)
  have hsqrtpow : 0 ≤ (Real.sqrt (p : ℝ)) ^ k := pow_nonneg (Real.sqrt_nonneg _) _
  calc
    (Real.sqrt (p : ℝ)) ^ k *
        |(S ℝ (k : ℤ)).eval
          ((frobeniusCoefficient p : ℝ) / Real.sqrt p)|
      ≤ (Real.sqrt p)^k * (k + 1) := by gcongr
    _ = (k + 1) * (Real.sqrt p)^k := by ring

theorem explicitPrimePowerCoefficient_abs_le_hasse_rpow
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    |(explicitPrimePowerCoefficient p k : ℝ)|
      ≤ (k + 1) * (p : ℝ) ^ ((k : ℝ) / 2) := by
  have h := explicitPrimePowerCoefficient_abs_le_hasse hp2 k
  simpa [Real.sqrt_eq_rpow, ← Real.rpow_natCast] using h

theorem explicitPrimePowerCoefficient_norm_le_hasse
    {p : ℕ} [Fact hp : p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    ‖(explicitPrimePowerCoefficient p k : ℂ)‖
      ≤ (k + 1) * (p : ℝ) ^ ((k : ℝ) / 2) := by
  rw [Complex.norm_intCast]
  exact_mod_cast explicitPrimePowerCoefficient_abs_le_hasse_rpow hp2 k

end Synthesis.Millennium.BSD
