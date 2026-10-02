import Synthesis.RiemannSelectedPrimeSensitiveSymmetricShiftMoments
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds

/-!
# Three-tap transformed local-budget primitives

This module moves the local Taylor data onto the same transformed normalized
signed profile used by the physical three-tap detector.

The fixed physical shift log 2 becomes B(t)=(t/16)log 2.  The transformed
support radius is therefore allowed to grow with |B(t)|; the old canonical
radius 1/(pi+1) is not reused.

The file pays exact support, sixth moment and eighth moment objects.  The final
absolute eighth-and-higher terminal inequality remains an analytic estimate.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

def QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  detectorThreeTap
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t)
    eps (threeTapNormalizedShift t (Real.log 2))

def QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  (Real.pi + 1)
    + |threeTapNormalizedShift t (Real.log 2)|

def QuarticFourSignedPolePair.threeTapAdaptiveLocalRadius
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  1 / W.threeTapNormalizedSupportRadius

theorem QuarticFourSignedPolePair.threeTapNormalizedSupportRadius_pos
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 < W.threeTapNormalizedSupportRadius := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
  have hp : 0 < Real.pi + 1 := by positivity
  have ha : 0 <= |threeTapNormalizedShift t (Real.log 2)| := abs_nonneg _
  linarith

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalRadius_pos
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 < W.threeTapAdaptiveLocalRadius := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalRadius
  positivity

theorem detectorThreeTap_support_abs_le_add
    {g : ℝ → ℝ} {S eps L u : ℝ}
    (hS0 : 0 ≤ S)
    (hS : ∀ v : ℝ, g v ≠ 0 → |v| ≤ S)
    (hu : detectorThreeTap g eps L u ≠ 0) :
    |u| ≤ S + |L| := by
  by_contra hnot
  have hfar : S + |L| < |u| := lt_of_not_ge hnot
  have hz (v : ℝ) (hv : S < |v|) : g v = 0 := by
    by_contra hne
    exact (not_lt_of_ge (hS v hne)) hv
  have hminusTri : |u| ≤ |u-L| + |L| := by
    calc
      |u| = |(u-L)+L| := by congr 1 <;> ring
      _ ≤ |u-L| + |L| := abs_add _ _
  have hplusTri : |u| ≤ |u+L| + |L| := by
    calc
      |u| = |(u+L)-L| := by congr 1 <;> ring
      _ ≤ |u+L| + |L| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add (u+L) (-L)
  have hminus : S < |u-L| := by linarith
  have hplus : S < |u+L| := by linarith
  have hu0 : S < |u| := by
    have ha := abs_nonneg L
    linarith
  have h0 := hz u hu0
  have hm := hz (u-L) hminus
  have hp := hz (u+L) hplus
  apply hu
  simp [detectorThreeTap, h0, hm, hp]

theorem QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile_support
    {t eps u : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hu : W.threeTapNormalizedCombinedProfile eps u ≠ 0) :
    |u| ≤ W.threeTapNormalizedSupportRadius := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile
    QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
  apply detectorThreeTap_support_abs_le_add
    (S := Real.pi + 1)
  · positivity
  · intro v hv
    exact W.combinedProfile_support_abs_le_pi_add_one v hv
  · exact hu

theorem QuarticFourSignedPolePair.abs_q_mul_u_le_one_of_threeTapAdaptive
    {t eps q u : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : |q| ≤ W.threeTapAdaptiveLocalRadius)
    (hu : W.threeTapNormalizedCombinedProfile eps u ≠ 0) :
    |q*u| ≤ 1 := by
  have hus := W.threeTapNormalizedCombinedProfile_support hu
  rw [abs_mul]
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalRadius at hq
  have hS := W.threeTapNormalizedSupportRadius_pos
  have hqS :
      |q| * W.threeTapNormalizedSupportRadius ≤ 1 := by
    calc
      |q| * W.threeTapNormalizedSupportRadius
        ≤ (1 / W.threeTapNormalizedSupportRadius)
            * W.threeTapNormalizedSupportRadius :=
          mul_le_mul_of_nonneg_right hq hS.le
      _ = 1 := by field_simp [hS.ne']
  exact (mul_le_mul_of_nonneg_left hus (abs_nonneg q)).trans hqS

def QuarticFourSignedPolePair.threeTapSignedProfileMomentZero
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  rawMoment (W.threeTapNormalizedCombinedProfile eps) 0

def QuarticFourSignedPolePair.threeTapSignedProfileMomentTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  rawMoment (W.threeTapNormalizedCombinedProfile eps) 2

def QuarticFourSignedPolePair.threeTapSignedProfileMomentFour
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  rawMoment (W.threeTapNormalizedCombinedProfile eps) 4

theorem QuarticFourSignedPolePair.baseRawMomentZero_eq_zero
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    rawMoment
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) 0 = 0 := by
  unfold rawMoment
  simp only [pow_zero, one_mul]
  change profileZerothMoment
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t) = 0
  exact quarticFourSignedPoleCombinedProfile_zeroth_zero W.Rpos

theorem QuarticFourSignedPolePair.baseRawMomentTwo_eq_zero
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    rawMoment
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) 2 = 0 := by
  unfold rawMoment
  change profileSecondMoment
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t) = 0
  exact quarticFourSignedPoleCombinedProfile_second_zero
    W.Rpos W.J2Half W.J2Two

theorem QuarticFourSignedPolePair.baseRawMomentFour_eq
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    rawMoment
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) 4
      = -4 * W.targetStrength := by
  unfold rawMoment
  change profileFourthMoment
    (quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t)
      = -4 * W.targetStrength
  rw [quarticFourSignedPoleCombinedProfile_fourth W.Rpos]
  unfold QuarticFourSignedPolePair.targetStrength
  ring

theorem QuarticFourSignedPolePair.threeTapSignedProfileMomentZero_eq_zero
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedProfileMomentZero eps = 0 := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  unfold QuarticFourSignedPolePair.threeTapSignedProfileMomentZero
    QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile
  rw [threeTapRawMoment_zero_exact hP hPc,
      W.baseRawMomentZero_eq_zero]
  ring

theorem QuarticFourSignedPolePair.threeTapSignedProfileMomentTwo_eq_zero
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedProfileMomentTwo eps = 0 := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  unfold QuarticFourSignedPolePair.threeTapSignedProfileMomentTwo
    QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile
  rw [threeTapRawMoment_two_exact hP hPc,
      W.baseRawMomentZero_eq_zero,
      W.baseRawMomentTwo_eq_zero]
  ring

theorem QuarticFourSignedPolePair.threeTapSignedProfileMomentFour_eq
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedProfileMomentFour eps
      = -4 * (1 + 2*eps) * W.targetStrength := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  unfold QuarticFourSignedPolePair.threeTapSignedProfileMomentFour
    QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile
  rw [threeTapRawMoment_four_exact hP hPc,
      W.baseRawMomentZero_eq_zero,
      W.baseRawMomentTwo_eq_zero,
      W.baseRawMomentFour_eq]
  ring

/-- The transformed normalized profile retains the quartic near-line
cancellation unless eps=-1/2. -/
theorem QuarticFourSignedPolePair.threeTap_quartic_coefficient_neg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (heps : -(1/2 : ℝ) < eps) :
    W.threeTapSignedProfileMomentFour eps < 0 := by
  rw [W.threeTapSignedProfileMomentFour_eq]
  have hfac : 0 < 1 + 2*eps := by linarith
  have hS := W.signedTargetStrength
  nlinarith

def QuarticFourSignedPolePair.threeTapSignedProfileMomentSix
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  rawMoment (W.threeTapNormalizedCombinedProfile eps) 6

def QuarticFourSignedPolePair.threeTapSignedProfileMomentEight
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  rawMoment (W.threeTapNormalizedCombinedProfile eps) 8

def QuarticFourSignedPolePair.threeTapSignedProfileAbsMomentEight
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  compactProfileAbsMoment
    (W.threeTapNormalizedCombinedProfile eps) 8

theorem QuarticFourSignedPolePair.threeTapSignedProfileAbsMomentEight_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 ≤ W.threeTapSignedProfileAbsMomentEight eps := by
  unfold QuarticFourSignedPolePair.threeTapSignedProfileAbsMomentEight
    compactProfileAbsMoment
  positivity

theorem QuarticFourSignedPolePair.rawMomentSix_eq_signedProfileMomentSix
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    rawMoment
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) 6
      = W.signedProfileMomentSix := by
  unfold rawMoment QuarticFourSignedPolePair.signedProfileMomentSix
  apply integral_congr_ae
  filter_upwards with u
  ring

theorem QuarticFourSignedPolePair.threeTapSignedProfileMomentSix_exact
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedProfileMomentSix eps
      =
    W.signedProfileMomentSix
      + eps *
        ∫ u : ℝ,
          (2*u^6
            + 30*(threeTapNormalizedShift t (Real.log 2))^2*u^4
            + 30*(threeTapNormalizedShift t (Real.log 2))^4*u^2
            + 2*(threeTapNormalizedShift t (Real.log 2))^6)
          *
          quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t u := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  unfold QuarticFourSignedPolePair.threeTapSignedProfileMomentSix
    QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile
  rw [threeTapRawMoment_six_exact hP hPc,
      W.rawMomentSix_eq_signedProfileMomentSix]
  rfl

theorem QuarticFourSignedPolePair.threeTapSignedProfileMomentEight_exact
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedProfileMomentEight eps
      =
    rawMoment
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) 8
      + eps *
        ∫ u : ℝ,
          (2*u^8
            + 56*(threeTapNormalizedShift t (Real.log 2))^2*u^6
            + 140*(threeTapNormalizedShift t (Real.log 2))^4*u^4
            + 56*(threeTapNormalizedShift t (Real.log 2))^6*u^2
            + 2*(threeTapNormalizedShift t (Real.log 2))^8)
          *
          quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t u := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  unfold QuarticFourSignedPolePair.threeTapSignedProfileMomentEight
    QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile
  exact threeTapRawMoment_eight_exact hP hPc eps
    (threeTapNormalizedShift t (Real.log 2))

/-! ## Canonical local radius is genuinely invalid on shifted support -/

theorem QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile_at_shift
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedCombinedProfile eps
        (threeTapNormalizedShift t (Real.log 2))
      =
    eps *
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t 0 := by
  let B := threeTapNormalizedShift t (Real.log 2)
  have hBout :
      Real.pi + 1 < B :=
    threeTapNormalizedShift_logTwo_gt_pi_add_one ht
  have hBpos : 0 < B := lt_trans (by positivity : 0 < Real.pi + 1) hBout
  have hzB :
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t B = 0 := by
    by_contra hne
    have hs := W.combinedProfile_support_abs_le_pi_add_one B hne
    rw [abs_of_pos hBpos] at hs
    linarith
  have hz2B :
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t (B+B) = 0 := by
    by_contra hne
    have hs := W.combinedProfile_support_abs_le_pi_add_one (B+B) hne
    rw [abs_of_pos (by positivity : 0 < B+B)] at hs
    linarith
  unfold QuarticFourSignedPolePair.threeTapNormalizedCombinedProfile
    detectorThreeTap
  dsimp [B] at hzB hz2B ⊢
  rw [hzB, hz2B]
  ring

theorem QuarticFourSignedPolePair.canonical_q_times_threeTapShift_gt_one
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    1 <
      quarticSignedPoleCanonicalLocalRadius
        * threeTapNormalizedShift t (Real.log 2) := by
  have hB :=
    threeTapNormalizedShift_logTwo_gt_pi_add_one ht
  unfold quarticSignedPoleCanonicalLocalRadius
  have hp : 0 < Real.pi + 1 := by positivity
  exact (one_lt_div hp).2 hB

/-- For a nonzero transformed shifted-copy amplitude at B(t), the canonical
Taylor prerequisite |q*u|<=1 fails at q=eta0 on an actual support point. -/
theorem QuarticFourSignedPolePair.canonicalLocalTaylorCondition_fails_threeTap
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (heps : eps ≠ 0)
    (hcentre :
      quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t 0 ≠ 0) :
    W.threeTapNormalizedCombinedProfile eps
        (threeTapNormalizedShift t (Real.log 2)) ≠ 0
    ∧
    1 <
      |quarticSignedPoleCanonicalLocalRadius
        * threeTapNormalizedShift t (Real.log 2)| := by
  constructor
  · rw [W.threeTapNormalizedCombinedProfile_at_shift ht]
    exact mul_ne_zero heps hcentre
  · have hprod := W.canonical_q_times_threeTapShift_gt_one ht
    rw [abs_of_pos (lt_trans (by norm_num : (0:ℝ) < 1) hprod)]
    exact hprod

/-- The adaptive normalized split has a bounded physical half-width rather
than the original O(t) half-width.  This identity is the recut geometry. -/
theorem QuarticFourSignedPolePair.threeTapAdaptivePhysicalHalfWidth_eq
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    (t/16) * W.threeTapAdaptiveLocalRadius
      =
    (t/16) /
      ((Real.pi + 1)
        + |threeTapNormalizedShift t (Real.log 2)|) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalRadius
    QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
  ring

end Synthesis
