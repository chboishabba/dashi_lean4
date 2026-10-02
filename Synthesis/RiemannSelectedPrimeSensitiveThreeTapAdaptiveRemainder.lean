import Synthesis.RiemannSelectedPrimeSensitiveThreeTapNormalizedProjective

/-!
# Adaptive M6/M8 and eighth-order local remainder for the transformed profile

This file gives an unconditional same-object envelope for the actual normalized
transformed signed projective profile P_eps.

If S is its proved support radius, then
  M6_abs <= S^6 M0_abs
  M8_abs <= S^8 M0_abs.

On the adaptive local domain |q| <= 1/S the existing certified scalar Taylor
bound therefore yields a literal eighth-order cosine remainder controlled by
M8_abs.  No commutation of projectivization and translation is used.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

def QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMoment
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (k : ℕ) : ℝ :=
  compactProfileAbsMoment
    (W.threeTapNormalizedSignedProjectiveProfile eps) k

def QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMass
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapNormalizedProjectiveAbsMoment eps 0

def QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMomentSix
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapNormalizedProjectiveAbsMoment eps 6

def QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMomentEight
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapNormalizedProjectiveAbsMoment eps 8

theorem QuarticFourSignedPolePair.threeTapNormalizedProjective_continuous
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    Continuous (W.threeTapNormalizedSignedProjectiveProfile eps) := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
    QuarticFourSignedPolePair.threeTapNormalizedHalf
    QuarticFourSignedPolePair.threeTapNormalizedTwo
  fun_prop

theorem QuarticFourSignedPolePair.threeTapNormalizedProjective_compact
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    HasCompactSupport (W.threeTapNormalizedSignedProjectiveProfile eps) := by
  have hhalfBase :
      HasCompactSupport
        (quarticFourWindowProfile W.R (1/2) W.muHalf) :=
    quarticFourWindowProfile_compact W.Rpos
  have htwoBase :
      HasCompactSupport
        (quarticFourWindowProfile W.R (2/3) W.muTwo) :=
    quarticFourWindowProfile_compact W.Rpos
  have hhalfTap :
      HasCompactSupport (W.threeTapNormalizedHalf eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedHalf
    exact detectorThreeTap_compact hhalfBase eps _
  have htwoTap :
      HasCompactSupport (W.threeTapNormalizedTwo eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedTwo
    exact detectorThreeTap_compact htwoBase eps _
  have hhalfP :
      HasCompactSupport (W.threeTapNormalizedProjectiveHalf eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
    exact genericProjectivePhysicalProfile_compact hhalfTap 1
  have htwoP :
      HasCompactSupport (W.threeTapNormalizedProjectiveTwo eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
    exact genericProjectivePhysicalProfile_compact htwoTap 1
  unfold QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile
  exact hhalfP.mul_left.add htwoP.mul_left

theorem QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMoment_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (k : ℕ) :
    0 <= W.threeTapNormalizedProjectiveAbsMoment eps k := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMoment
    compactProfileAbsMoment
  positivity

private theorem absMomentSix_le_support
    {P : ℝ → ℝ} {S : ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (hS : 0 <= S)
    (hsupp : ∀ u, P u ≠ 0 → |u| <= S) :
    compactProfileAbsMoment P 6
      <= S^6 * compactProfileAbsMoment P 0 := by
  have h6 := compactProfile_absMoment_integrable hP hPc 6
  have h0 := compactProfile_absMoment_integrable hP hPc 0
  unfold compactProfileAbsMoment
  calc
    (∫ u : ℝ, |P u| * |u|^6)
      <= ∫ u : ℝ, S^6 * (|P u| * |u|^0) := by
        apply integral_mono h6 (h0.const_mul (S^6))
        intro u
        by_cases hz : P u = 0
        · simp [hz]
        · have hu := hsupp u hz
          have hpow : |u|^6 <= S^6 := by
            gcongr
          simp only [pow_zero, mul_one]
          nlinarith [abs_nonneg (P u)]
    _ = S^6 * (∫ u : ℝ, |P u| * |u|^0) := by
      rw [integral_const_mul]
    _ = _ := by rfl

private theorem absMomentEight_le_support
    {P : ℝ → ℝ} {S : ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (hS : 0 <= S)
    (hsupp : ∀ u, P u ≠ 0 → |u| <= S) :
    compactProfileAbsMoment P 8
      <= S^8 * compactProfileAbsMoment P 0 := by
  have h8 := compactProfile_absMoment_integrable hP hPc 8
  have h0 := compactProfile_absMoment_integrable hP hPc 0
  unfold compactProfileAbsMoment
  calc
    (∫ u : ℝ, |P u| * |u|^8)
      <= ∫ u : ℝ, S^8 * (|P u| * |u|^0) := by
        apply integral_mono h8 (h0.const_mul (S^8))
        intro u
        by_cases hz : P u = 0
        · simp [hz]
        · have hu := hsupp u hz
          have hpow : |u|^8 <= S^8 := by
            gcongr
          simp only [pow_zero, mul_one]
          nlinarith [abs_nonneg (P u)]
    _ = S^8 * (∫ u : ℝ, |P u| * |u|^0) := by
      rw [integral_const_mul]
    _ = _ := by rfl

theorem QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMomentSix_le
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedProjectiveAbsMomentSix eps
      <=
    W.threeTapNormalizedSupportRadius^6
      * W.threeTapNormalizedProjectiveAbsMass eps := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMomentSix
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMass
  apply absMomentSix_le_support
    W.threeTapNormalizedProjective_continuous
    W.threeTapNormalizedProjective_compact
    W.threeTapNormalizedSupportRadius_pos.le
  intro u hu
  exact (W.threeTapNormalizedSignedProjective_support hu).le

theorem QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMomentEight_le
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedProjectiveAbsMomentEight eps
      <=
    W.threeTapNormalizedSupportRadius^8
      * W.threeTapNormalizedProjectiveAbsMass eps := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMomentEight
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMass
  apply absMomentEight_le_support
    W.threeTapNormalizedProjective_continuous
    W.threeTapNormalizedProjective_compact
    W.threeTapNormalizedSupportRadius_pos.le
  intro u hu
  exact (W.threeTapNormalizedSignedProjective_support hu).le

def QuarticFourSignedPolePair.threeTapNormalizedCosineSixthRemainder
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps q : ℝ) : ℝ :=
  ∫ v : ℝ,
    W.threeTapNormalizedSignedProjectiveProfile eps v
      *
    (Real.cos (q*v)
      - (1 - (q*v)^2/2 + (q*v)^4/24 - (q*v)^6/720))

/-- Literal transformed eighth-order local remainder on the adaptive radius. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedCosineSixthRemainder_abs_le
    {t eps q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= W.threeTapAdaptiveLocalRadius) :
    |W.threeTapNormalizedCosineSixthRemainder eps q|
      <=
    (1/35840 : ℝ) * |q|^8
      * W.threeTapNormalizedProjectiveAbsMomentEight eps := by
  let P := W.threeTapNormalizedSignedProjectiveProfile eps
  have hP : Continuous P := W.threeTapNormalizedProjective_continuous
  have hPc : HasCompactSupport P := W.threeTapNormalizedProjective_compact
  have hi :
      Integrable
        (fun v : ℝ =>
          P v *
            (Real.cos (q*v)
              - (1 - (q*v)^2/2 + (q*v)^4/24 - (q*v)^6/720))) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hPc.mul_right
  have hmaj :
      Integrable
        (fun v : ℝ =>
          (1/35840 : ℝ) * |q|^8 * (|P v| * |v|^8)) :=
    (compactProfile_absMoment_integrable hP hPc 8).const_mul
      ((1/35840 : ℝ) * |q|^8)
  unfold QuarticFourSignedPolePair.threeTapNormalizedCosineSixthRemainder
  calc
    |∫ v : ℝ,
      P v *
        (Real.cos (q*v)
          - (1 - (q*v)^2/2 + (q*v)^4/24 - (q*v)^6/720))|
      <=
    ∫ v : ℝ,
      |P v *
        (Real.cos (q*v)
          - (1 - (q*v)^2/2 + (q*v)^4/24 - (q*v)^6/720))| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ v : ℝ,
      (1/35840 : ℝ) * |q|^8 * (|P v| * |v|^8) := by
      apply integral_mono hi.abs hmaj
      intro v
      by_cases hz : P v = 0
      · simp [hz]
      · have hqv :=
          W.abs_q_mul_v_le_one_of_threeTapAdaptive hq hz
        have hc := real_cos_sub_sixth_abs_le_eighth hqv
        rw [abs_mul]
        have hp : |q*v|^8 = |q|^8 * |v|^8 := by
          rw [abs_mul, mul_pow]
        rw [hp] at hc
        nlinarith [abs_nonneg (P v), abs_nonneg v]
    _ =
    (1/35840 : ℝ) * |q|^8
      * compactProfileAbsMoment P 8 := by
      rw [integral_const_mul]
      ring
    _ = _ := by rfl

/-- Closed support-only envelope for the transformed eighth-order remainder. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedCosineSixthRemainder_abs_le_support
    {t eps q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| <= W.threeTapAdaptiveLocalRadius) :
    |W.threeTapNormalizedCosineSixthRemainder eps q|
      <=
    (1/35840 : ℝ) * |q|^8
      * (W.threeTapNormalizedSupportRadius^8
        * W.threeTapNormalizedProjectiveAbsMass eps) := by
  calc
    |W.threeTapNormalizedCosineSixthRemainder eps q|
      <=
    (1/35840 : ℝ) * |q|^8
      * W.threeTapNormalizedProjectiveAbsMomentEight eps :=
        W.threeTapNormalizedCosineSixthRemainder_abs_le hq
    _ <= _ := by
      gcongr
      exact W.threeTapNormalizedProjectiveAbsMomentEight_le

end Synthesis
