import Synthesis.RiemannProjectiveZetaMuContinuousAbel
import Synthesis.RiemannNormalizedProjectiveRvMMissingTailBound

/-!
# Physical endpoint decay for the projective signed Abel consumer

The finite-window Abel identity contains the endpoint

  phi_t(B) E_A(B),

where

  phi_t(B) = Phi_t((B-t)/t).

The projective transform has exact q^-2 decay, while the theorem-bearing
Zeta23 cumulative discrepancy is only logarithmic.  This file combines those
facts on the physical ordinate variable, retaining the literal distance
(B-t)^2 in the denominator.

This is the quantitative endpoint input for the full signed Abel limit.  It is
not a signed-correlation theorem.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

/-- q^-2 decay rewritten on the physical ordinate variable. -/
theorem normalizedProjectiveOrdinateTest_abs_le_gap_sq
    {t B : ℝ} (ht : 0 < t) (hBt : B ≠ t) :
    |normalizedProjectiveOrdinateTest t B|
      ≤ normalizedProjectiveBaseCurvature t * t^2 / (B - t)^2 := by
  unfold normalizedProjectiveOrdinateTest
  have hq : (B - t) / t ≠ 0 := by
    apply div_ne_zero
    · exact sub_ne_zero.mpr hBt
    · exact ne_of_gt ht
  have hdec :=
    normalizedProjectiveBaseTransform_abs_le_invSq
      (t := t) (q := (B - t) / t) hq
  have ht0 : t ≠ 0 := ne_of_gt ht
  calc
    |normalizedProjectiveBaseTransform t ((B-t)/t)|
      ≤ normalizedProjectiveBaseCurvature t / (((B-t)/t)^2) := hdec
    _ = normalizedProjectiveBaseCurvature t * t^2 / (B-t)^2 := by
      field_simp [ht0, sub_ne_zero.mpr hBt]
      ring

/--
The literal Abel endpoint is bounded by logarithmic discrepancy times a
quadratically decaying physical-gap factor.
-/
theorem exists_projectiveZetaMu_endpoint_gap_sq_bound :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t A B : ℝ,
        18 ≤ t ->
        max T0 4 ≤ A ->
        A < B ->
        B ≠ t ->
        |normalizedProjectiveOrdinateTest t B
          * zetaMuCumulativeDiscrepancy A B|
          ≤
        (normalizedProjectiveBaseCurvature t * t^2 / (B-t)^2)
          *
        (C * (Real.log (A+3) + Real.log (B+4))) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t A B ht hA hAB hBt
  have htpos : 0 < t := by linarith
  have hphi :=
    normalizedProjectiveOrdinateTest_abs_le_gap_sq
      (t := t) (B := B) htpos hBt
  have hdisc :
      |zetaMuCumulativeDiscrepancy A B|
        ≤ C * (Real.log (A+3) + Real.log (B+4)) := by
    rw [zetaMuCumulativeDiscrepancy_endpoint]
    exact hD A B hA hAB
  have hcurv : 0 ≤ normalizedProjectiveBaseCurvature t :=
    normalizedProjectiveBaseCurvature_nonneg t
  have hden : 0 < (B-t)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hBt)
  have hfactor :
      0 ≤ normalizedProjectiveBaseCurvature t * t^2 / (B-t)^2 := by
    positivity
  rw [abs_mul]
  exact mul_le_mul hphi hdisc (abs_nonneg _) hfactor

end Synthesis
