import Synthesis.RiemannGammaCenteredQuadraticMass
import Zeta23Bridge.LiteralWeilProjectiveStripConstant

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveStripConstant

def gammaCenteredTaperDeriv (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  fun u =>
    deriv g u * (Real.cos (r * u) - 1)
      - r * g u * Real.sin (r * u)

def gammaCenteredTaperDeriv2 (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  fun u =>
    deriv (deriv g) u * (Real.cos (r * u) - 1)
      - 2 * r * deriv g u * Real.sin (r * u)
      - r ^ 2 * g u * Real.cos (r * u)

theorem deriv_gammaCenteredTaper {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (r : ℝ) :
    deriv (gammaCenteredTaper g r) = gammaCenteredTaperDeriv g r := by
  have hd : Differentiable ℝ g := hgs.differentiable (by norm_num)
  funext u
  have hc :
      HasDerivAt (fun v : ℝ => Real.cos (r * v) - 1)
        (-r * Real.sin (r * u)) u := by
    simpa [mul_assoc] using
      (((hasDerivAt_id u).const_mul r).cos.sub_const 1)
  have hp := (hd u).hasDerivAt.mul hc
  rw [hp.deriv]
  unfold gammaCenteredTaperDeriv
  ring

theorem deriv2_gammaCenteredTaper {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (r : ℝ) :
    deriv (deriv (gammaCenteredTaper g r))
      = gammaCenteredTaperDeriv2 g r := by
  have hd : Differentiable ℝ g := hgs.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv g) := hgs.differentiable_deriv_two
  rw [deriv_gammaCenteredTaper hgs r]
  funext u
  have hc :
      HasDerivAt (fun v : ℝ => Real.cos (r * v) - 1)
        (-r * Real.sin (r * u)) u := by
    simpa [mul_assoc] using
      (((hasDerivAt_id u).const_mul r).cos.sub_const 1)
  have hs :
      HasDerivAt (fun v : ℝ => Real.sin (r * v))
        (r * Real.cos (r * u)) u := by
    simpa [mul_assoc] using
      (((hasDerivAt_id u).const_mul r).sin)
  have h1 := (hd2 u).hasDerivAt.mul hc
  have h2 := (((hd u).hasDerivAt.mul hs).const_mul (-r))
  have hsum := h1.add h2
  rw [hsum.deriv]
  unfold gammaCenteredTaperDeriv2
  ring

theorem abs_gammaCenteredTaperDeriv_le {g : ℝ → ℝ} {Λ r u : ℝ}
    (hsupp : ∀ v, g v ≠ 0 → |v| ≤ Λ) (hΛ : 0 ≤ Λ) :
    |gammaCenteredTaperDeriv g r u|
      ≤ r ^ 2 * ((Λ ^ 2 / 2) * |deriv g u| + Λ * |g u|) := by
  by_cases hu : |u| ≤ Λ
  · have hcos := abs_cos_sub_one_le_sq_div_two (r * u)
    have hsin := Real.abs_sin_le_abs (r * u)
    have hu2 : u ^ 2 ≤ Λ ^ 2 := by nlinarith [sq_abs u, sq_nonneg Λ]
    have hcos' : |Real.cos (r * u) - 1| ≤ r ^ 2 * Λ ^ 2 / 2 := by
      have hsq : (r * u) ^ 2 ≤ r ^ 2 * Λ ^ 2 := by
        nlinarith [sq_nonneg r]
      linarith
    have hsin' : |Real.sin (r * u)| ≤ |r| * Λ := by
      calc
        |Real.sin (r * u)| ≤ |r * u| := hsin
        _ = |r| * |u| := abs_mul _ _
        _ ≤ |r| * Λ := mul_le_mul_of_nonneg_left hu (abs_nonneg r)
    unfold gammaCenteredTaperDeriv
    have htri := abs_sub
      (deriv g u * (Real.cos (r * u) - 1))
      (r * g u * Real.sin (r * u))
    have hA :
        |deriv g u * (Real.cos (r * u) - 1)|
          ≤ |deriv g u| * (r ^ 2 * Λ ^ 2 / 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hcos' (abs_nonneg _)
    have hB :
        |r * g u * Real.sin (r * u)|
          ≤ r ^ 2 * Λ * |g u| := by
      rw [abs_mul, abs_mul]
      have hm := mul_le_mul_of_nonneg_left hsin' (abs_nonneg (r * g u))
      rw [abs_mul] at hm
      nlinarith [sq_abs r]
    nlinarith [htri, hA, hB]
  · have hg : g u = 0 := by
      by_contra hne
      exact hu (hsupp u hne)
    have hd : deriv g u = 0 := by
      by_contra hne
      exact hu (support_radius_deriv hsupp u hne)
    simp [gammaCenteredTaperDeriv, hg, hd]

theorem abs_gammaCenteredTaperDeriv2_le {g : ℝ → ℝ} {Λ r u : ℝ}
    (hsupp : ∀ v, g v ≠ 0 → |v| ≤ Λ) (hΛ : 0 ≤ Λ) :
    |gammaCenteredTaperDeriv2 g r u|
      ≤ r ^ 2 *
        ((Λ ^ 2 / 2) * |deriv (deriv g) u|
          + 2 * Λ * |deriv g u| + |g u|) := by
  by_cases hu : |u| ≤ Λ
  · have hcos := abs_cos_sub_one_le_sq_div_two (r * u)
    have hsin := Real.abs_sin_le_abs (r * u)
    have hu2 : u ^ 2 ≤ Λ ^ 2 := by nlinarith [sq_abs u, sq_nonneg Λ]
    have hcos' : |Real.cos (r * u) - 1| ≤ r ^ 2 * Λ ^ 2 / 2 := by
      have hsq : (r * u) ^ 2 ≤ r ^ 2 * Λ ^ 2 := by
        nlinarith [sq_nonneg r]
      linarith
    have hsin' : |Real.sin (r * u)| ≤ |r| * Λ := by
      calc
        |Real.sin (r * u)| ≤ |r * u| := hsin
        _ = |r| * |u| := abs_mul _ _
        _ ≤ |r| * Λ := mul_le_mul_of_nonneg_left hu (abs_nonneg r)
    have hcos1 : |Real.cos (r * u)| ≤ 1 := Real.abs_cos_le_one _
    unfold gammaCenteredTaperDeriv2
    have htri1 := abs_sub
      (deriv (deriv g) u * (Real.cos (r * u) - 1))
      (2 * r * deriv g u * Real.sin (r * u))
    have htri2 := abs_sub
      (deriv (deriv g) u * (Real.cos (r * u) - 1)
        - 2 * r * deriv g u * Real.sin (r * u))
      (r ^ 2 * g u * Real.cos (r * u))
    have hA :
        |deriv (deriv g) u * (Real.cos (r * u) - 1)|
          ≤ |deriv (deriv g) u| * (r ^ 2 * Λ ^ 2 / 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hcos' (abs_nonneg _)
    have hB :
        |2 * r * deriv g u * Real.sin (r * u)|
          ≤ r ^ 2 * (2 * Λ * |deriv g u|) := by
      rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      have hm := mul_le_mul_of_nonneg_left hsin'
        (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg r))
          (abs_nonneg (deriv g u)))
      nlinarith [sq_abs r]
    have hC :
        |r ^ 2 * g u * Real.cos (r * u)| ≤ r ^ 2 * |g u| := by
      rw [abs_mul, abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left hcos1
        (mul_nonneg (sq_nonneg r) (abs_nonneg (g u)))
    nlinarith [htri1, htri2, hA, hB, hC]
  · have hg : g u = 0 := by
      by_contra hne
      exact hu (hsupp u hne)
    have hd : deriv g u = 0 := by
      by_contra hne
      exact hu (support_radius_deriv hsupp u hne)
    have hd2 : deriv (deriv g) u = 0 := by
      by_contra hne
      exact hu (support_radius_deriv (support_radius_deriv hsupp) u hne)
    simp [gammaCenteredTaperDeriv2, hg, hd, hd2]

end Synthesis
