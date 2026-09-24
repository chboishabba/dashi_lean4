import Synthesis.MillenniumBSDCMEta32QuarterTurn
import Mathlib.Tactic

/-!
# Factor the eta32 q-series through q^4

The literal product admits the stronger structural factorization

  f(q) = q * H(q^4),

where

  H(u) = (∏_{n≥0}(1-u^(n+1)))^2
         (∏_{n≥0}(1-u^(2(n+1))))^2.

This isolates the entire nonzero Fourier support in the progression 4m+1
before any coefficient API is invoked.
-/

namespace Synthesis.Millennium.BSD

noncomputable def cmEta32QuarterFactor (u : ℂ) : ℂ :=
  (∏' n : ℕ, (1 - u ^ (n + 1))) ^ 2 *
    (∏' n : ℕ, (1 - u ^ (2 * (n + 1)))) ^ 2

theorem pow_four_mul_natSucc (q : ℂ) (n : ℕ) :
    (q ^ 4) ^ (n + 1) = q ^ (4 * (n + 1)) := by
  rw [← pow_mul]

theorem pow_four_two_mul_natSucc (q : ℂ) (n : ℕ) :
    (q ^ 4) ^ (2 * (n + 1)) = q ^ (8 * (n + 1)) := by
  rw [← pow_mul]
  congr 2
  ring

theorem cmEta32QProduct_eq_q_mul_quarterFactor (q : ℂ) :
    cmEta32QProduct q = q * cmEta32QuarterFactor (q ^ 4) := by
  unfold cmEta32QProduct cmEta32QuarterFactor
  simp_rw [pow_four_mul_natSucc, pow_four_two_mul_natSucc]
  ring

theorem cmEta32QuarterFactor_zero :
    cmEta32QuarterFactor 0 = 1 := by
  simp [cmEta32QuarterFactor]

theorem cmEta32QuarterFactor_one_step (q : ℂ) :
    cmEta32QProduct q / q = cmEta32QuarterFactor (q ^ 4) := by
  by_cases hq : q = 0
  · subst q
    simp [cmEta32QProduct_zero, cmEta32QuarterFactor_zero]
  · rw [cmEta32QProduct_eq_q_mul_quarterFactor]
    field_simp [hq]

/-- The quarter-turn covariance is now an immediate corollary of q*H(q^4). -/
theorem cmEta32QProduct_mul_I_from_factorization (q : ℂ) :
    cmEta32QProduct (Complex.I * q) =
      Complex.I * cmEta32QProduct q := by
  rw [cmEta32QProduct_eq_q_mul_quarterFactor,
      cmEta32QProduct_eq_q_mul_quarterFactor]
  have hI4 : Complex.I ^ 4 = (1 : ℂ) := by norm_num
  rw [mul_pow, hI4, one_mul]
  ring

end Synthesis.Millennium.BSD
