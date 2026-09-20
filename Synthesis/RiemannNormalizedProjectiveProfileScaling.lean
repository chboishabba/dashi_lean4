import Synthesis.RiemannNormalizedProjectiveBaseZeroAtSameOrd
import Synthesis.RiemannNormalizedBaseTransformVariation
import Synthesis.RiemannNormalizedProjectiveBaseTransformDerivativeRegularity

/-!
# Explicit canonical scaling of the projective physical profile

The single projective physical profile contains the two on-line coefficients

  A0(r), A0(2r),   r=t/16.

The exact fixed-profile scaling already proves

  t A0(r)  = ∫ G_t(v) cos(v/16) dv,
  t A0(2r) = ∫ G_t(v) cos(v/8)  dv.

Hence both coefficients are O(1/t), with the constant controlled by the fixed
canonical profile mass.  Since the normalized support is contained in

  |v| < 9*pi/4,

the L1, first absolute moment, and second absolute moment of the full projective
profile are all O(1/t).

This converts the continuous N-mu Abel theorem from abstract profile norms to
literal canonical t-scaling.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedCanonicalProfileMassUpper : ℝ :=
  (Real.pi / 2) * unitBumpMass0 * (1 + quantitativeMixUpper)

theorem normalizedCanonicalProfileMassUpper_nonneg :
    0 ≤ normalizedCanonicalProfileMassUpper := by
  unfold normalizedCanonicalProfileMassUpper
  have hm : 0 ≤ unitBumpMass0 := unitBumpMass0_nonneg
  have hmix : 0 ≤ quantitativeMixUpper := by
    unfold quantitativeMixUpper
    positivity
  positivity

theorem normalizedCanonicalFixedProfile_abs_integrable (t : ℝ) :
    Integrable (fun v : ℝ => |normalizedCanonicalFixedProfile t v|) := by
  exact (normalizedCanonicalFixedProfile_contDiff t).continuous.abs
    .integrable_of_hasCompactSupport
      (normalizedCanonicalFixedProfile_compact t).abs

theorem normalizedCanonicalFixedProfile_abs_mass_le
    {t : ℝ} (ht : 18 ≤ t) :
    (∫ v : ℝ, |normalizedCanonicalFixedProfile t v|)
      ≤ normalizedCanonicalProfileMassUpper := by
  have h := normalizedCanonicalFixedProfile_mass_le ht
  unfold taperMass at h
  simpa [normalizedCanonicalProfileMassUpper] using h

private theorem normalizedCanonical_cosineIntegral_abs_le_mass
    (t k : ℝ) :
    |∫ v : ℝ,
      normalizedCanonicalFixedProfile t v * Real.cos (k * v)|
      ≤
    ∫ v : ℝ, |normalizedCanonicalFixedProfile t v| := by
  have hi :
      Integrable
        (fun v : ℝ =>
          normalizedCanonicalFixedProfile t v * Real.cos (k * v)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedCanonicalFixedProfile_compact t).mul_right)
  calc
    |∫ v : ℝ,
      normalizedCanonicalFixedProfile t v * Real.cos (k * v)|
      ≤
    ∫ v : ℝ,
      |normalizedCanonicalFixedProfile t v * Real.cos (k * v)| :=
      abs_integral_le_integral_abs
    _ ≤
    ∫ v : ℝ, |normalizedCanonicalFixedProfile t v| := by
      apply integral_mono hi.abs
        (normalizedCanonicalFixedProfile_abs_integrable t)
      intro v
      rw [abs_mul]
      exact mul_le_of_le_one_right
        (abs_nonneg _)
        (Real.abs_cos_le_one (k * v))

theorem onLineRadiusProfile_sample_abs_le
    {t : ℝ} (ht : 18 ≤ t) :
    |onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t)|
      ≤ normalizedCanonicalProfileMassUpper / t := by
  have ht0 : 0 < t := by linarith
  have hraw :=
    normalizedCanonical_cosineIntegral_abs_le_mass t (1 / 16)
  have hscale :=
    integral_normalizedCanonicalFixedProfile_cos_one ht0
  rw [hscale, abs_mul, abs_of_pos ht0] at hraw
  have hmass := normalizedCanonicalFixedProfile_abs_mass_le ht
  have h :
      t * |onLineRadiusProfile
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)|
        ≤ normalizedCanonicalProfileMassUpper :=
    hraw.trans hmass
  exact (le_div_iff₀ ht0).2 (by simpa [mul_comm] using h)

theorem onLineRadiusProfile_doubleSample_abs_le
    {t : ℝ} (ht : 18 ≤ t) :
    |onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (2 * quantitativeSampleRadius t)|
      ≤ normalizedCanonicalProfileMassUpper / t := by
  have ht0 : 0 < t := by linarith
  have hraw :=
    normalizedCanonical_cosineIntegral_abs_le_mass t (1 / 8)
  have hscale :=
    integral_normalizedCanonicalFixedProfile_cos_two ht0
  rw [hscale, abs_mul, abs_of_pos ht0] at hraw
  have hmass := normalizedCanonicalFixedProfile_abs_mass_le ht
  have h :
      t * |onLineRadiusProfile
        (quantitativeCanonicalTaper t)
        (2 * quantitativeSampleRadius t)|
        ≤ normalizedCanonicalProfileMassUpper :=
    hraw.trans hmass
  exact (le_div_iff₀ ht0).2 (by simpa [mul_comm] using h)

theorem normalizedProjectivePhysicalProfile_support_upper
    {t v : ℝ}
    (hv : normalizedProjectivePhysicalProfile t v ≠ 0) :
    |v| < 9 * Real.pi / 4 := by
  have hbase : normalizedCanonicalFixedProfile t v ≠ 0 := by
    intro hzero
    apply hv
    simp [normalizedProjectivePhysicalProfile, hzero]
  unfold normalizedCanonicalFixedProfile at hbase
  by_cases hi : normalizedInnerFixedProfile v = 0
  · have ho : normalizedOuterFixedProfile v ≠ 0 := by
      intro ho
      apply hbase
      simp [hi, ho]
    exact normalizedOuterFixedProfile_support_upper ho
  · have hin := normalizedInnerFixedProfile_support_upper hi
    nlinarith [Real.pi_pos]

theorem normalizedProjectiveProfileL1_le_inv_t
    {t : ℝ} (ht : 18 ≤ t) :
    normalizedProjectiveProfileL1 t
      ≤
    8 * normalizedCanonicalProfileMassUpper ^ 2 / t := by
  have ht0 : 0 < t := by linarith
  let A1 : ℝ :=
    onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t)
  let A2 : ℝ :=
    onLineRadiusProfile
      (quantitativeCanonicalTaper t)
      (2 * quantitativeSampleRadius t)
  let M : ℝ := normalizedCanonicalProfileMassUpper
  have hA1 : |A1| ≤ M / t := by
    dsimp [A1, M]
    exact onLineRadiusProfile_sample_abs_le ht
  have hA2 : |A2| ≤ M / t := by
    dsimp [A2, M]
    exact onLineRadiusProfile_doubleSample_abs_le ht
  have hM : 0 ≤ M := by
    dsimp [M]
    exact normalizedCanonicalProfileMassUpper_nonneg
  have hG :
      (∫ v : ℝ, |normalizedCanonicalFixedProfile t v|) ≤ M := by
    dsimp [M]
    exact normalizedCanonicalFixedProfile_abs_mass_le ht
  have hP :
      ∀ v : ℝ,
        |normalizedProjectivePhysicalProfile t v|
          ≤
        4 * (|A1| + |A2|)
          * |normalizedCanonicalFixedProfile t v| := by
    intro v
    unfold normalizedProjectivePhysicalProfile
    dsimp [A1, A2]
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    have htri :=
      abs_sub
        (A1 * Real.cos (v / 8))
        (A2 * Real.cos (v / 16))
    have h1 :
        |A1 * Real.cos (v/8)| ≤ |A1| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg A1)
        (Real.abs_cos_le_one _)
    have h2 :
        |A2 * Real.cos (v/16)| ≤ |A2| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg A2)
        (Real.abs_cos_le_one _)
    nlinarith [abs_nonneg (normalizedCanonicalFixedProfile t v)]
  have hInt :
      normalizedProjectiveProfileL1 t
        ≤
      4 * (|A1| + |A2|)
        * (∫ v : ℝ, |normalizedCanonicalFixedProfile t v|) := by
    unfold normalizedProjectiveProfileL1
    have hright :
        Integrable
          (fun v : ℝ =>
            4 * (|A1| + |A2|)
              * |normalizedCanonicalFixedProfile t v|) :=
      (normalizedCanonicalFixedProfile_abs_integrable t).const_mul
        (4 * (|A1| + |A2|))
    calc
      (∫ v : ℝ, |normalizedProjectivePhysicalProfile t v|)
        ≤
      ∫ v : ℝ,
        4 * (|A1| + |A2|)
          * |normalizedCanonicalFixedProfile t v| := by
            apply integral_mono
              (normalizedProjectivePhysicalProfile_integrable t).abs
              hright
              hP
      _ =
      4 * (|A1| + |A2|)
        * (∫ v : ℝ, |normalizedCanonicalFixedProfile t v|) := by
          rw [integral_const_mul]
  have hsum : |A1| + |A2| ≤ 2 * M / t := by
    linarith
  have hcoef : 0 ≤ 4 * (|A1| + |A2|) := by positivity
  calc
    normalizedProjectiveProfileL1 t
      ≤
    4 * (|A1| + |A2|)
      * (∫ v : ℝ, |normalizedCanonicalFixedProfile t v|) := hInt
    _ ≤
    4 * (|A1| + |A2|) * M :=
      mul_le_mul_of_nonneg_left hG hcoef
    _ ≤
    4 * (2 * M / t) * M := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by norm_num))
        hM
    _ =
    8 * M ^ 2 / t := by
      field_simp [ne_of_gt ht0]
      ring
    _ =
    8 * normalizedCanonicalProfileMassUpper ^ 2 / t := rfl

theorem normalizedProjectiveProfileFirstMoment_le_inv_t
    {t : ℝ} (ht : 18 ≤ t) :
    normalizedProjectiveProfileFirstMoment t
      ≤
    (9 * Real.pi / 4)
      * (8 * normalizedCanonicalProfileMassUpper ^ 2 / t) := by
  have hPabs :
      Integrable (fun v : ℝ => |normalizedProjectivePhysicalProfile t v|) :=
    (normalizedProjectivePhysicalProfile_integrable t).abs
  have hM1 := normalizedProjectiveProfile_firstMoment_integrable t
  have hdom :
      Integrable
        (fun v : ℝ =>
          (9 * Real.pi / 4)
            * |normalizedProjectivePhysicalProfile t v|) :=
    hPabs.const_mul _
  have hpoint : ∀ v : ℝ,
      |normalizedProjectivePhysicalProfile t v| * |v|
        ≤
      (9 * Real.pi / 4)
        * |normalizedProjectivePhysicalProfile t v| := by
    intro v
    by_cases hz : normalizedProjectivePhysicalProfile t v = 0
    · simp [hz]
    · have hs := normalizedProjectivePhysicalProfile_support_upper hz
      nlinarith [abs_nonneg (normalizedProjectivePhysicalProfile t v)]
  have hi :
      normalizedProjectiveProfileFirstMoment t
        ≤
      (9 * Real.pi / 4)
        * normalizedProjectiveProfileL1 t := by
    unfold normalizedProjectiveProfileFirstMoment
      normalizedProjectiveProfileL1
    calc
      (∫ v : ℝ,
        |normalizedProjectivePhysicalProfile t v| * |v|)
        ≤
      ∫ v : ℝ,
        (9 * Real.pi / 4)
          * |normalizedProjectivePhysicalProfile t v| :=
            integral_mono hM1 hdom hpoint
      _ =
      (9 * Real.pi / 4)
        * ∫ v : ℝ, |normalizedProjectivePhysicalProfile t v| := by
          rw [integral_const_mul]
  exact hi.trans
    (mul_le_mul_of_nonneg_left
      (normalizedProjectiveProfileL1_le_inv_t ht)
      (by positivity))

theorem normalizedProjectiveProfileSecondMoment_le_inv_t
    {t : ℝ} (ht : 18 ≤ t) :
    normalizedProjectiveProfileSecondMoment t
      ≤
    (9 * Real.pi / 4) ^ 2
      * (8 * normalizedCanonicalProfileMassUpper ^ 2 / t) := by
  have hPabs :
      Integrable (fun v : ℝ => |normalizedProjectivePhysicalProfile t v|) :=
    (normalizedProjectivePhysicalProfile_integrable t).abs
  have hM2 := normalizedProjectiveProfile_secondMoment_integrable t
  have hdom :
      Integrable
        (fun v : ℝ =>
          (9 * Real.pi / 4) ^ 2
            * |normalizedProjectivePhysicalProfile t v|) :=
    hPabs.const_mul _
  have hpoint : ∀ v : ℝ,
      |normalizedProjectivePhysicalProfile t v| * |v| ^ 2
        ≤
      (9 * Real.pi / 4) ^ 2
        * |normalizedProjectivePhysicalProfile t v| := by
    intro v
    by_cases hz : normalizedProjectivePhysicalProfile t v = 0
    · simp [hz]
    · have hs := normalizedProjectivePhysicalProfile_support_upper hz
      have hv0 : 0 ≤ |v| := abs_nonneg v
      have hR : 0 ≤ 9 * Real.pi / 4 := by positivity
      have hs2 : |v| ^ 2 ≤ (9 * Real.pi / 4) ^ 2 := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hs2
        (abs_nonneg (normalizedProjectivePhysicalProfile t v))
  have hi :
      normalizedProjectiveProfileSecondMoment t
        ≤
      (9 * Real.pi / 4) ^ 2
        * normalizedProjectiveProfileL1 t := by
    unfold normalizedProjectiveProfileSecondMoment
      normalizedProjectiveProfileL1
    calc
      (∫ v : ℝ,
        |normalizedProjectivePhysicalProfile t v| * |v| ^ 2)
        ≤
      ∫ v : ℝ,
        (9 * Real.pi / 4) ^ 2
          * |normalizedProjectivePhysicalProfile t v| :=
            integral_mono hM2 hdom hpoint
      _ =
      (9 * Real.pi / 4) ^ 2
        * ∫ v : ℝ, |normalizedProjectivePhysicalProfile t v| := by
          rw [integral_const_mul]
  exact hi.trans
    (mul_le_mul_of_nonneg_left
      (normalizedProjectiveProfileL1_le_inv_t ht)
      (by positivity))

end Synthesis
