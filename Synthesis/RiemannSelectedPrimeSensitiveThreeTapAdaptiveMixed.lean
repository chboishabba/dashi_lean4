import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveRemainder
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleEighthRemainder

/-!
# Generic adaptive mixed remainder and transformed local debt

This file lifts the old selected-profile mixed eighth-order Taylor estimate to
an arbitrary continuous compact profile with an explicit support radius S.

It is then instantiated on the actual normalized transformed signed projective
profile P_eps with S = pi+1+|(t/16)log 2|.  This is the reusable core needed by
the adaptive local/far compiler.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real

def compactMixedSixthRemainder
    (P : ℝ → ℝ) (alpha q : ℝ) : ℝ :=
  ∫ v : ℝ,
    P v *
      (Real.cosh (alpha*v) * Real.cos (q*v)
        - quarticSignedPoleMixedDegreeSixTaylor (alpha*v) (q*v))

theorem compactMixedSixthRemainder_abs_le_eighth
    {P : ℝ → ℝ} {S alpha q : ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (hS : 0 <= S)
    (hsupp : ∀ v, P v ≠ 0 → |v| <= S)
    (ha : |alpha| <= 1/S)
    (hq : |q| <= 1/S)
    (hSpos : 0 < S) :
    |compactMixedSixthRemainder P alpha q|
      <=
    quarticSignedPoleMixedEighthEnvelope alpha q
      * compactProfileAbsMoment P 8 := by
  have hi :
      Integrable
        (fun v : ℝ =>
          P v *
            (Real.cosh (alpha*v) * Real.cos (q*v)
              - quarticSignedPoleMixedDegreeSixTaylor
                  (alpha*v) (q*v))) :=
    Continuous.integrable_of_hasCompactSupport
      (by
        unfold quarticSignedPoleMixedDegreeSixTaylor
          quarticSignedPoleSixthPhaseReal
        fun_prop)
      hPc.mul_right
  have hmaj :
      Integrable
        (fun v : ℝ =>
          quarticSignedPoleMixedEighthEnvelope alpha q
            * (|P v| * |v|^8)) :=
    (compactProfile_absMoment_integrable hP hPc 8).const_mul _
  unfold compactMixedSixthRemainder
  calc
    |∫ v : ℝ,
      P v *
        (Real.cosh (alpha*v) * Real.cos (q*v)
          - quarticSignedPoleMixedDegreeSixTaylor
              (alpha*v) (q*v))|
      <=
    ∫ v : ℝ,
      |P v *
        (Real.cosh (alpha*v) * Real.cos (q*v)
          - quarticSignedPoleMixedDegreeSixTaylor
              (alpha*v) (q*v))| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ v : ℝ,
      quarticSignedPoleMixedEighthEnvelope alpha q
        * (|P v| * |v|^8) := by
      apply integral_mono hi.abs hmaj
      intro v
      by_cases hz : P v = 0
      · simp [hz]
      · have hv := hsupp v hz
        have haS :
            |alpha| * S <= 1 := by
          calc
            |alpha| * S <= (1/S) * S :=
              mul_le_mul_of_nonneg_right ha hS
            _ = 1 := by field_simp [ne_of_gt hSpos]
        have hqS :
            |q| * S <= 1 := by
          calc
            |q| * S <= (1/S) * S :=
              mul_le_mul_of_nonneg_right hq hS
            _ = 1 := by field_simp [ne_of_gt hSpos]
        have hav : |alpha*v| <= 1 := by
          rw [abs_mul]
          exact
            (mul_le_mul_of_nonneg_left hv (abs_nonneg alpha)).trans haS
        have hqv : |q*v| <= 1 := by
          rw [abs_mul]
          exact
            (mul_le_mul_of_nonneg_left hv (abs_nonneg q)).trans hqS
        have hscalar :=
          real_cosh_mul_cos_sub_mixedSixth_abs_le_eighth hav hqv
        have hfactor :
            quarticSignedPoleMixedEighthEnvelope (alpha*v) (q*v)
              =
            |v|^8 * quarticSignedPoleMixedEighthEnvelope alpha q := by
          unfold quarticSignedPoleMixedEighthEnvelope
          rw [← abs_pow]
          ring_nf
          rw [abs_pow]
          ring
        rw [abs_mul, hfactor] at hscalar
        have hE :
            0 <= quarticSignedPoleMixedEighthEnvelope alpha q := by
          unfold quarticSignedPoleMixedEighthEnvelope
          positivity
        calc
          |P v| *
              |Real.cosh (alpha*v) * Real.cos (q*v)
                - quarticSignedPoleMixedDegreeSixTaylor
                    (alpha*v) (q*v)|
            <=
          |P v| *
            (|v|^8 * quarticSignedPoleMixedEighthEnvelope alpha q) :=
              mul_le_mul_of_nonneg_left hscalar (abs_nonneg _)
          _ =
          quarticSignedPoleMixedEighthEnvelope alpha q
            * (|P v| * |v|^8) := by ring
    _ =
    quarticSignedPoleMixedEighthEnvelope alpha q
      * compactProfileAbsMoment P 8 := by
      rw [integral_const_mul]
      rfl

def QuarticFourSignedPolePair.threeTapNormalizedMixedSixthRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha q : ℝ) : ℝ :=
  compactMixedSixthRemainder
    (W.threeTapNormalizedSignedProjectiveProfile eps) alpha q

theorem QuarticFourSignedPolePair.threeTapNormalizedMixedSixthRemainder_abs_le
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= W.threeTapAdaptiveLocalRadius)
    (hq : |q| <= W.threeTapAdaptiveLocalRadius) :
    |W.threeTapNormalizedMixedSixthRemainder eps alpha q|
      <=
    quarticSignedPoleMixedEighthEnvelope alpha q
      * W.threeTapNormalizedProjectiveAbsMomentEight eps := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedMixedSixthRemainder
    QuarticFourSignedPolePair.threeTapAdaptiveLocalRadius
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMomentEight
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMoment
  apply compactMixedSixthRemainder_abs_le_eighth
    W.threeTapNormalizedProjective_continuous
    W.threeTapNormalizedProjective_compact
    W.threeTapNormalizedSupportRadius_pos.le
  · intro v hv
    exact (W.threeTapNormalizedSignedProjective_support hv).le
  · exact ha
  · exact hq
  · exact W.threeTapNormalizedSupportRadius_pos

theorem QuarticFourSignedPolePair.threeTapNormalizedMixedSixthRemainder_abs_le_support
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= W.threeTapAdaptiveLocalRadius)
    (hq : |q| <= W.threeTapAdaptiveLocalRadius) :
    |W.threeTapNormalizedMixedSixthRemainder eps alpha q|
      <=
    quarticSignedPoleMixedEighthEnvelope alpha q
      *
    (W.threeTapNormalizedSupportRadius^8
      * W.threeTapNormalizedProjectiveAbsMass eps) := by
  calc
    |W.threeTapNormalizedMixedSixthRemainder eps alpha q|
      <=
    quarticSignedPoleMixedEighthEnvelope alpha q
      * W.threeTapNormalizedProjectiveAbsMomentEight eps :=
        W.threeTapNormalizedMixedSixthRemainder_abs_le ha hq
    _ <= _ := by
      have hE :
          0 <= quarticSignedPoleMixedEighthEnvelope alpha q := by
        unfold quarticSignedPoleMixedEighthEnvelope
        positivity
      exact mul_le_mul_of_nonneg_left
        W.threeTapNormalizedProjectiveAbsMomentEight_le hE

/-- Every adaptive-local zero lies in the complete transformed two-variable
Taylor domain. -/
theorem QuarticFourSignedPolePair.threeTap_zero_mixed_domain
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hl : quarticSignedPoleThreeTapAdaptiveLocal W rho) :
    |heightOf rho / (t/16)| <= W.threeTapAdaptiveLocalRadius
      ∧
    |quarticSignedPoleNormalizedOrdinateOffset t rho|
      <= W.threeTapAdaptiveLocalRadius := by
  exact ⟨W.threeTap_zero_alpha_abs_le_adaptive ht rho, hl⟩

end Synthesis
