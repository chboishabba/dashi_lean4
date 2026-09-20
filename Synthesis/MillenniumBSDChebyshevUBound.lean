import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# Uniform bound for Chebyshev U on [-1,1]

We isolate the elementary analytic estimate needed by the BSD local-factor lane:

  |U_n(x)| <= n+1,   -1 <= x <= 1.

The proof uses U_n(cos θ) sin θ = sin((n+1)θ) together with
|sin(mθ)| <= m |sin θ|.  Endpoints are handled by the exact mathlib
evaluations at ±1.
-/

namespace Synthesis.Millennium.BSD

open Polynomial
open Polynomial.Chebyshev

theorem abs_sin_nat_mul_le (n : ℕ) (θ : ℝ) :
    |Real.sin ((n : ℝ) * θ)| ≤ n * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hadd := Real.abs_sin_add_le ((n : ℝ) * θ) θ
      rw [show ((n + 1 : ℕ) : ℝ) * θ = (n : ℝ) * θ + θ by push_cast; ring]
      calc
        |Real.sin ((n : ℝ) * θ + θ)|
            ≤ |Real.sin ((n : ℝ) * θ)| + |Real.sin θ| := hadd
        _ ≤ n * |Real.sin θ| + |Real.sin θ| := by gcongr
        _ = (n + 1) * |Real.sin θ| := by push_cast; ring

theorem abs_sin_int_natSucc_mul_le (n : ℕ) (θ : ℝ) :
    |Real.sin (((n : ℤ) + 1 : ℤ) * θ)|
      ≤ (n + 1) * |Real.sin θ| := by
  simpa using abs_sin_nat_mul_le (n + 1) θ

theorem chebyshevU_abs_le_natSucc
    (n : ℕ) {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) :
    |(U ℝ (n : ℤ)).eval x| ≤ n + 1 := by
  rcases eq_or_ne x (-1) with rfl | hxNeg
  · rw [U_eval_neg_one]
    simp [abs_mul]
  rcases eq_or_ne x 1 with rfl | hxPos
  · rw [U_eval_one]
    simp
  let θ := Real.arccos x
  have hcos : Real.cos θ = x := by
    dsimp [θ]
    exact Real.cos_arccos hx₁ hx₂
  have hxNegStrict : -1 < x := lt_of_le_of_ne hx₁ (Ne.symm hxNeg)
  have hxPosStrict : x < 1 := lt_of_le_of_ne hx₂ hxPos
  have hsq : x ^ 2 < 1 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (1 - x)]
  have hsinPos : 0 < Real.sin θ := by
    rw [show Real.sin θ = Real.sqrt (1 - x^2) by
      dsimp [θ]; exact Real.sin_arccos x]
    exact Real.sqrt_pos.2 (by linarith)
  have hsinNe : Real.sin θ ≠ 0 := ne_of_gt hsinPos
  have hU := U_real_cos θ (n : ℤ)
  rw [hcos] at hU
  have hmul :
      |(U ℝ (n : ℤ)).eval x| * |Real.sin θ|
        = |Real.sin (((n : ℤ) + 1) * θ)| := by
    rw [← abs_mul, hU]
  have hbound := abs_sin_int_natSucc_mul_le n θ
  rw [← hmul] at hbound
  have habsSin : 0 < |Real.sin θ| := abs_pos.mpr hsinNe
  exact (mul_le_mul_right habsSin).mp (by
    simpa [mul_assoc] using hbound)

theorem chebyshevU_abs_le_natSucc_of_abs_le_one
    (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(U ℝ (n : ℤ)).eval x| ≤ n + 1 := by
  exact chebyshevU_abs_le_natSucc n (neg_le_of_abs_le hx) (le_of_abs_le hx)

theorem chebyshevS_abs_le_natSucc
    (n : ℕ) {x : ℝ} (hx : |x| ≤ 2) :
    |(S ℝ (n : ℤ)).eval x| ≤ n + 1 := by
  have hxhalf : |x / 2| ≤ 1 := by
    rw [abs_div, abs_ofNat]
    linarith
  rw [S_eq_U_comp_half_mul_X]
  simp only [eval_comp, eval_mul, eval_C, eval_X]
  have hhalf : (⅟(2 : ℝ)) * x = x / 2 := by norm_num; ring
  rw [hhalf]
  exact chebyshevU_abs_le_natSucc_of_abs_le_one n hxhalf

end Synthesis.Millennium.BSD
