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

end Synthesis
