import Synthesis.RiemannQuantitativeScaledBump
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Positive weighted integral for the scaled fixed bump

The fixed unit bump equals one on the inner half-ball.  After affine rescaling,
psi_{c,R} equals one on |u-c| <= R/2 and is supported in |u-c|<R.

Hence any continuous weight that is strictly positive throughout the outer
window has strictly positive integral against psi_{c,R}.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

theorem scaledUnitBump_one_of_half_window
    {c R u : ℝ} (hR : 0 < R)
    (hu : |u - c| <= R / 2) :
    scaledUnitBump c R u = 1 := by
  unfold scaledUnitBump unitBump
  apply unitContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hR]
  exact (div_le_iff₀ hR).2 (by nlinarith)

theorem scaledUnitBump_positive_integral
    {c R : ℝ} (hR : 0 < R)
    {w : ℝ → ℝ}
    (hw : Continuous w)
    (hwpos : ∀ u, |u - c| < R → 0 < w u) :
    0 < ∫ u : ℝ, scaledUnitBump c R u * w u := by
  have hnonneg :
      0 <= fun u : ℝ => scaledUnitBump c R u * w u := by
    intro u
    by_cases hu : scaledUnitBump c R u = 0
    · simp [hu]
    · exact mul_nonneg
        (scaledUnitBump_nonneg c R u)
        (hwpos u (scaledUnitBump_support hR hu)).le
  have hint : Integrable
      (fun u : ℝ => scaledUnitBump c R u * w u) :=
    Zeta23Bridge.LiteralWeilParityBalance.taper_integrable
      (scaledUnitBump_continuous hR.ne' c)
      (scaledUnitBump_hasCompactSupport hR)
      hw
  rw [integral_pos_iff_support_of_nonneg hnonneg hint]
  have hsub :
      Metric.closedBall c (R / 2)
        ⊆ Function.support
          (fun u : ℝ => scaledUnitBump c R u * w u) := by
    intro u hu
    have hdist := Metric.mem_closedBall.mp hu
    rw [Real.dist_eq] at hdist
    have hpsi := scaledUnitBump_one_of_half_window hR hdist
    have houter : |u-c| < R := by linarith
    have hw0 : 0 < w u := hwpos u houter
    simp only [Function.mem_support, hpsi, one_mul]
    exact hw0.ne'
  have hmeasure :
      (0 : ENNReal) < volume (Metric.closedBall c (R / 2)) := by
    rw [Real.volume_closedBall]
    simp only [ENNReal.ofReal_pos]
    positivity
  exact lt_of_lt_of_le hmeasure (measure_mono hsub)

end Synthesis
