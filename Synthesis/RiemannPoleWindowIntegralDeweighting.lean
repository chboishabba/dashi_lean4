import Synthesis.RiemannPoleWindowDeweighting

/-!
# Integral form of the pole-window de-weighting mechanism

This file upgrades the scalar de-weighting lemma to localized integrals.

Outer window:
  7*pi/(4t) < u < 9*pi/(4t)
  F >= 0
  => integral F(u) cos(tu/16) <= outerCosUpper * integral F.

Inner window:
  3*pi/(4t) < u < 5*pi/(4t)
  F <= 0
  => innerCosLower * (- integral F)
       <= - integral F(u) cos(tu/16).

These are the exact inequalities needed by the two-bump pole-killing
construction.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

theorem outer_window_weighted_integral_le
    {F : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hF : Integrable F)
    (hnn : ∀ u, 0 ≤ F u)
    (hsupp : ∀ u, F u ≠ 0 →
      7 * Real.pi / (4 * t) < u ∧ u < 9 * Real.pi / (4 * t)) :
    (∫ u : ℝ, F u * Real.cos ((t / 16) * u))
      ≤ outerCosUpper * ∫ u : ℝ, F u := by
  have hcosInt : Integrable (fun u : ℝ => F u * Real.cos ((t / 16) * u)) :=
    hF.mul_const_of_bounded (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))
      ⟨1, fun u => by simpa using Real.abs_cos_le_one ((t / 16) * u)⟩
  have hconstInt : Integrable (fun u : ℝ => outerCosUpper * F u) :=
    hF.const_mul _
  have hpoint :
      ∀ u, F u * Real.cos ((t / 16) * u) ≤ outerCosUpper * F u := by
    intro u
    by_cases hFu : F u = 0
    · simp [hFu]
    · have hwin := hsupp u hFu
      have hcos := sampleCos_le_outerCosUpper ht hwin.1 hwin.2
      exact mul_le_mul_of_nonneg_left hcos (hnn u)
  have h := integral_mono hcosInt hconstInt hpoint
  rw [integral_const_mul] at h
  simpa [mul_comm] using h

theorem inner_window_weighted_negative_magnitude
    {F : ℝ → ℝ} {t : ℝ}
    (ht : 0 < t)
    (hF : Integrable F)
    (hnp : ∀ u, F u ≤ 0)
    (hsupp : ∀ u, F u ≠ 0 →
      3 * Real.pi / (4 * t) < u ∧ u < 5 * Real.pi / (4 * t)) :
    innerCosLower * (-(∫ u : ℝ, F u))
      ≤ -(∫ u : ℝ, F u * Real.cos ((t / 16) * u)) := by
  let G : ℝ → ℝ := fun u => -F u
  have hG : Integrable G := hF.neg
  have hGnn : ∀ u, 0 ≤ G u := by
    intro u
    dsimp [G]
    linarith [hnp u]
  have hGsupp : ∀ u, G u ≠ 0 →
      3 * Real.pi / (4 * t) < u ∧ u < 5 * Real.pi / (4 * t) := by
    intro u hu
    apply hsupp u
    dsimp [G] at hu
    exact neg_ne_zero.mp hu
  have hcosInt : Integrable (fun u : ℝ => G u * Real.cos ((t / 16) * u)) :=
    hG.mul_const_of_bounded (Real.continuous_cos.comp
      (continuous_const.mul continuous_id))
      ⟨1, fun u => by simpa using Real.abs_cos_le_one ((t / 16) * u)⟩
  have hconstInt : Integrable (fun u : ℝ => innerCosLower * G u) :=
    hG.const_mul _
  have hpoint :
      ∀ u, innerCosLower * G u ≤ G u * Real.cos ((t / 16) * u) := by
    intro u
    by_cases hGu : G u = 0
    · simp [hGu]
    · have hwin := hGsupp u hGu
      have hcos := innerCosLower_le_sampleCos ht hwin.1 hwin.2
      exact mul_le_mul_of_nonneg_left hcos (hGnn u)
  have h := integral_mono hconstInt hcosInt hpoint
  rw [integral_const_mul] at h
  have hGint : (∫ u : ℝ, G u) = -(∫ u : ℝ, F u) := by
    dsimp [G]
    rw [integral_neg]
  have hGw :
      (∫ u : ℝ, G u * Real.cos ((t / 16) * u))
        = -(∫ u : ℝ, F u * Real.cos ((t / 16) * u)) := by
    dsimp [G]
    rw [show (fun u : ℝ => -F u * Real.cos ((t / 16) * u))
      = fun u : ℝ => -(F u * Real.cos ((t / 16) * u)) by
        funext u; ring,
      integral_neg]
  rw [hGint, hGw] at h
  exact h

theorem two_window_integral_cancellation_leaves_positive_residue
    {F1 F2 : ℝ → ℝ} {t lam : ℝ}
    (ht : 0 < t)
    (hF1 : Integrable F1)
    (hF2 : Integrable F2)
    (hF1nn : ∀ u, 0 ≤ F1 u)
    (hF2np : ∀ u, F2 u ≤ 0)
    (hF1supp : ∀ u, F1 u ≠ 0 →
      7 * Real.pi / (4 * t) < u ∧ u < 9 * Real.pi / (4 * t))
    (hF2supp : ∀ u, F2 u ≠ 0 →
      3 * Real.pi / (4 * t) < u ∧ u < 5 * Real.pi / (4 * t))
    (hA1 : 0 < ∫ u : ℝ, F1 u)
    (hA2 : (∫ u : ℝ, F2 u) < 0)
    (hP1 : 0 < ∫ u : ℝ, F1 u * Real.cos ((t / 16) * u))
    (hP2 : (∫ u : ℝ, F2 u * Real.cos ((t / 16) * u)) < 0)
    (hlam :
      lam =
        -(∫ u : ℝ, F2 u * Real.cos ((t / 16) * u))
          / (∫ u : ℝ, F1 u * Real.cos ((t / 16) * u))) :
    0 < (∫ u : ℝ, F2 u) + lam * ∫ u : ℝ, F1 u := by
  apply positive_unweighted_of_separated_weighted_cancellation
    hA1 hA2 hP1 hP2 outerCosUpper_pos
    outerCosUpper_lt_innerCosLower
  · exact outer_window_weighted_integral_le ht hF1 hF1nn hF1supp
  · exact inner_window_weighted_negative_magnitude ht hF2 hF2np hF2supp
  · exact hlam

end Synthesis
