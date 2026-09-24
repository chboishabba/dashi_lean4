import Synthesis.RiemannRvMMuHighPositive

/-!
# A crude uniform positive lower bound for the exact RvM density

For the quartic negative-window argument we do not need a sharp asymptotic for
mu.  A fixed positive lower bound above a fixed height is enough because the
physical negative window has width proportional to t whereas the Backlund
discrepancy is only logarithmic.

Using the already-proved explicit Stirling estimate

  |mu(tau) - (1/(2*pi)) log(|tau|/(2*pi))|
    <= (20/(2*pi))/tau^2,

together with pi<4, pi>3 and the standard numerical lower bound on log 2, we
obtain the deliberately coarse bound

  tau >= 100  ->  mu(tau) > 1/20.

The constants are chosen for proof robustness, not optimization.
-/

noncomputable section

open scoped Real

namespace Synthesis

theorem zetaMu_gt_one_twentieth_of_hundred_le
    {tau : ℝ} (htau : 100 <= tau) :
    (1/20 : ℝ) < Zeta23.mu tau := by
  have htauPos : 0 < tau := by linarith
  have habs : |tau| = tau := abs_of_pos htauPos
  have h1 : 1 <= |tau| := by
    rw [habs]
    linarith
  have hst := zetaMu_stirling_explicit h1
  have hlo := (abs_le.mp hst).1

  have hdenPos : 0 < 2 * Real.pi := by positivity
  have hratio2 : 2 < |tau| / (2 * Real.pi) := by
    rw [habs]
    rw [lt_div_iff₀ hdenPos]
    nlinarith [Real.pi_lt_four]

  have hlog :
      Real.log 2 < Real.log (|tau| / (2 * Real.pi)) :=
    Real.log_lt_log (by norm_num) hratio2
  have hlogLower :
      (0.6931471803 : ℝ)
        < Real.log (|tau| / (2 * Real.pi)) :=
    Real.log_two_gt_d9.trans hlog

  have hcoef :
      (1/8 : ℝ) < 1 / (2 * Real.pi) := by
    rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 8) hdenPos]
    nlinarith [Real.pi_lt_four]

  have hlogPos :
      0 < Real.log (|tau| / (2 * Real.pi)) := by
    linarith
  have hmain1 :
      (1/8 : ℝ) * (0.6931471803 : ℝ)
        <
      (1/8 : ℝ) * Real.log (|tau| / (2 * Real.pi)) :=
    mul_lt_mul_of_pos_left hlogLower (by norm_num)
  have hmain2 :
      (1/8 : ℝ) * Real.log (|tau| / (2 * Real.pi))
        <
      (1 / (2 * Real.pi))
        * Real.log (|tau| / (2 * Real.pi)) :=
    mul_lt_mul_of_pos_right hcoef hlogPos
  have hmain :
      (0.08 : ℝ)
        <
      (1 / (2 * Real.pi))
        * Real.log (|tau| / (2 * Real.pi)) := by
    have hnum :
        (0.08 : ℝ) < (1/8 : ℝ) * (0.6931471803 : ℝ) := by
      norm_num
    exact hnum.trans (hmain1.trans hmain2)

  have hcoefErr :
      (20 / (2 * Real.pi) : ℝ) < 4 := by
    rw [div_lt_iff₀ hdenPos]
    nlinarith [Real.pi_gt_three]
  have htauSq : (10000 : ℝ) <= tau^2 := by
    nlinarith
  have htauSqPos : 0 < tau^2 := sq_pos_of_pos htauPos
  have herr :
      (20 / (2 * Real.pi)) / tau^2 < (1/100 : ℝ) := by
    rw [div_lt_iff₀ htauSqPos]
    have h100 : (100 : ℝ) <= tau^2 / 100 := by
      nlinarith
    nlinarith [hcoefErr]

  have hgap :
      (1/20 : ℝ)
        <
      (1 / (2 * Real.pi))
          * Real.log (|tau| / (2 * Real.pi))
        - (20 / (2 * Real.pi)) / tau^2 := by
    nlinarith [hmain, herr]

  linarith

theorem zetaMu_ge_one_twentieth_of_hundred_le
    {tau : ℝ} (htau : 100 <= tau) :
    (1/20 : ℝ) <= Zeta23.mu tau :=
  (zetaMu_gt_one_twentieth_of_hundred_le htau).le

end Synthesis
