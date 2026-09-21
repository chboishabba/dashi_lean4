import Synthesis.RiemannGammaCenteredConeExact
import Zeta23Bridge.LiteralWeilProjectiveStripConstant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quadratic mass gain for the centered Gamma taper

For h_r(u) = g(u) (cos(r u) - 1), the centering itself supplies the small
parameter:

    |cos x - 1| <= x^2 / 2.

Hence on support |u| <= Lambda,

    |h_r(u)| <= (r^2 Lambda^2 / 2) |g(u)|

and therefore

    ||h_r||_1 <= (r^2 Lambda^2 / 2) ||g||_1.

This is the first quantitative piece of the Gamma bypass.  Unlike the coarse
stripConst estimate, it does not pay the raw second-derivative norm of g.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

theorem abs_cos_sub_one_le_sq_div_two (x : ℝ) :
    |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  have hcos : Real.cos x ≤ 1 := Real.cos_le_one x
  have hrewrite : |Real.cos x - 1| = 1 - Real.cos x := by
    rw [abs_of_nonpos]
    linarith
  have hsin := Real.abs_sin_le_abs (x / 2)
  have hsinSq : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
    nlinarith [sq_nonneg (Real.sin (x / 2)), sq_nonneg (x / 2)]
  have htrig : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have h := Real.sin_sq_eq_half_sub (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    nlinarith
  rw [hrewrite, htrig]
  nlinarith

theorem abs_gammaCenteredTaper_le {g : ℝ → ℝ} {Λ r u : ℝ}
    (hsupp : ∀ v, g v ≠ 0 → |v| ≤ Λ)
    (hΛ : 0 ≤ Λ) :
    |gammaCenteredTaper g r u|
      ≤ (r ^ 2 * Λ ^ 2 / 2) * |g u| := by
  by_cases hgu : g u = 0
  · simp [gammaCenteredTaper, hgu]
  · have hu : |u| ≤ Λ := hsupp u hgu
    have hsqU : u ^ 2 ≤ Λ ^ 2 := by
      have h := sq_le_sq.mpr (by simpa [abs_of_nonneg hΛ] using hu)
      simpa [sq_abs] using h
    have hcos := abs_cos_sub_one_le_sq_div_two (r * u)
    have hru : (r * u) ^ 2 ≤ r ^ 2 * Λ ^ 2 := by
      nlinarith [sq_nonneg r, hsqU]
    unfold gammaCenteredTaper
    rw [abs_mul]
    have hfac : |Real.cos (r * u) - 1| ≤ r ^ 2 * Λ ^ 2 / 2 := by
      linarith
    exact mul_le_mul_of_nonneg_left hfac (abs_nonneg (g u))

theorem taperMass_gammaCenteredTaper_le {g : ℝ → ℝ} {Λ r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) :
    taperMass (gammaCenteredTaper g r)
      ≤ (r ^ 2 * Λ ^ 2 / 2) * taperMass g := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hc : Continuous (gammaCenteredTaper g r) :=
    gammaCenteredTaper_continuous hgs.continuous r
  have hcc : HasCompactSupport (gammaCenteredTaper g r) :=
    gammaCenteredTaper_hasCompactSupport hgc r
  exact taperMass_le_of_pointwise hc hcc hgs.continuous hgc
    (abs_gammaCenteredTaper_le hsupp hΛ)

end Synthesis
