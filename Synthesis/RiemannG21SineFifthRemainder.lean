import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import Synthesis.RiemannG21OddContinuumToRadius

/-!
# G21 exact fifth-order sine remainder

The old G21 quantitative ledger left

  |sin x - (x - x^3/6)| <= |x|^5 / 120

as an analytic producer.  It is actually ordinary real calculus.  This owner
source-writes it from Mathlib's Lagrange Taylor remainder and the exact iterated
derivatives of `Real.sin`.

The six-scaled form used by the odd determinant expansion follows immediately:

  |6 (sin x - x + x^3/6)| <= |x|^5 / 20.

No zeta/RH input appears here.
-/

noncomputable section

open Set

namespace Synthesis

private theorem sin_taylor4_nonneg
    {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.sin 4 (Icc (0 : ℝ) x) 0 x = x - x^3/6 := by
  rw [taylor_within_apply]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) x := ⟨le_rfl, hx.le⟩
  simp [Real.iteratedDerivWithin_sin_Icc, hx, h0,
    Real.iteratedDeriv_even_sin, Real.iteratedDeriv_odd_sin]
  ring

private theorem sin_cubic_fifth_remainder_of_pos
    {x : ℝ} (hx : 0 < x) :
    |Real.sin x - (x - x^3/6)| <= x^5 / 120 := by
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sin) (x₀ := (0 : ℝ)) (x := x) (n := 4)
      hx Real.contDiff_sin.contDiffOn
  have hpoly := sin_taylor4_nonneg hx
  rw [hpoly] at hrem
  have hderiv : iteratedDeriv 5 Real.sin ξ = Real.cos ξ := by
    simpa using congrFun (Real.iteratedDeriv_odd_sin 2) ξ
  have hcos : |Real.cos ξ| <= 1 := Real.abs_cos_le_one ξ
  have h120 : ((5 : ℕ)! : ℝ) = 120 := by norm_num
  rw [hderiv, h120, sub_zero] at hrem
  rw [hrem, abs_div, abs_mul, abs_pow, abs_of_nonneg hx.le]
  norm_num
  nlinarith [hcos]

/-- Exact fifth-order cubic sine remainder. -/
theorem sin_cubic_fifth_remainder (x : ℝ) :
    |Real.sin x - (x - x^3/6)| <= |x|^5 / 120 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    have h := sin_cubic_fifth_remainder_of_pos hpos
    have hrewrite :
        Real.sin (-x) - ((-x) - (-x)^3/6)
          = -(Real.sin x - (x - x^3/6)) := by
      rw [Real.sin_neg]
      ring
    rw [hrewrite, abs_neg, abs_neg] at h
    simpa [abs_of_neg hx] using h
  · norm_num
  · simpa [abs_of_pos hx] using sin_cubic_fifth_remainder_of_pos hx

/-- Six-scaled form used by the determinant remainder bookkeeping. -/
theorem six_scaled_sin_cubic_remainder (x : ℝ) :
    |6 * (Real.sin x - (x - x^3/6))| <= |x|^5 / 20 := by
  have h := sin_cubic_fifth_remainder x
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) <= 6)]
  nlinarith

end Synthesis
