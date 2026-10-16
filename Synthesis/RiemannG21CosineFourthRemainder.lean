import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
import Synthesis.RiemannG21LiteralOddMinorExists

/-!
# G21 exact fourth-order cosine remainder

The even G21 response uses the quadratic cosine truncation

  cos x = 1 - x^2/2 + O(x^4).

Mathlib's Lagrange remainder and the fourth iterated derivative of cosine give

  |cos x - (1 - x^2/2)| <= |x|^4/24.

This is ordinary calculus, not an RH producer.
-/

noncomputable section

open Set

namespace Synthesis

private theorem cos_taylor3_nonneg
    {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.cos 3 (Icc (0 : ℝ) x) 0 x = 1 - x^2/2 := by
  rw [taylor_within_apply]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) x := ⟨le_rfl, hx.le⟩
  simp [Real.iteratedDerivWithin_cos_Icc, hx, h0,
    Real.iteratedDeriv_even_cos, Real.iteratedDeriv_odd_cos]
  ring

private theorem cos_quadratic_fourth_remainder_of_pos
    {x : ℝ} (hx : 0 < x) :
    |Real.cos x - (1 - x^2/2)| <= x^4/24 := by
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (x₀ := (0 : ℝ)) (x := x) (n := 3)
      hx Real.contDiff_cos.contDiffOn
  have hpoly := cos_taylor3_nonneg hx
  rw [hpoly] at hrem
  have hderiv : iteratedDeriv 4 Real.cos ξ = Real.cos ξ := by
    simpa using congrFun (Real.iteratedDeriv_even_cos 2) ξ
  have hcos : |Real.cos ξ| <= 1 := Real.abs_cos_le_one ξ
  have h24 : ((4 : ℕ)! : ℝ) = 24 := by norm_num
  rw [hderiv, h24, sub_zero] at hrem
  rw [hrem, abs_div, abs_mul, abs_pow, abs_of_nonneg hx.le]
  norm_num
  nlinarith [hcos]

/-- Exact fourth-order quadratic cosine remainder. -/
theorem cos_quadratic_fourth_remainder (x : ℝ) :
    |Real.cos x - (1 - x^2/2)| <= |x|^4/24 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hpos : 0 < -x := neg_pos.mpr hx
    have h := cos_quadratic_fourth_remainder_of_pos hpos
    have hrewrite :
        Real.cos (-x) - (1 - (-x)^2/2)
          = Real.cos x - (1 - x^2/2) := by
      rw [Real.cos_neg]
      ring
    rw [hrewrite, abs_neg] at h
    simpa [abs_of_neg hx] using h
  · norm_num
  · simpa [abs_of_pos hx] using cos_quadratic_fourth_remainder_of_pos hx

end Synthesis
