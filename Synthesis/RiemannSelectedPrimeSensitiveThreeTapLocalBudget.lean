import Synthesis.RiemannSelectedPrimeSensitiveSymmetricShiftMoments
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleLocalRemainderBounds

/-!
# Three-tap transformed projective local-budget frontier

Projectivization is detector-dependent: translating the source taper changes
the on-line response column, so in general

  projectiveProfile (T_eps g) != T_eps (projectiveProfile g).

Accordingly this file defines the transformed local-moment object directly
from the ACTUAL translated detector in each endpoint channel.  The generic
symmetric-shift moment algebra remains useful for linear subexpressions, but is
not used to identify these projective moments without a theorem.

The fixed physical shift log 2 becomes B(t)=(t/16)log 2 in the normalized
source coordinate.  At t>=200 B(t)>pi+1, proving that the old canonical
|q u|<=1 Taylor domain cannot simply be reused.

The transformed absolute M6/M8 estimate and a recut local/far compiler remain
the analytic frontier.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

/-- Same-object transformed physical projective profile, endpoint lambda=1/2. -/
def QuarticFourSignedPolePair.threeTapProjectiveProfileHalf
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  genericProjectivePhysicalProfile (W.threeTapHalf eps) (t/16)

/-- Same-object transformed physical projective profile, endpoint lambda=2/3. -/
def QuarticFourSignedPolePair.threeTapProjectiveProfileTwo
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  genericProjectivePhysicalProfile (W.threeTapTwo eps) (t/16)

/-- The exact pole-weighted transformed projective profile. -/
def QuarticFourSignedPolePair.threeTapSignedProjectiveProfile
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ → ℝ :=
  fun u =>
    W.poleTwo * W.threeTapProjectiveProfileHalf eps u
      + (-W.poleHalf) * W.threeTapProjectiveProfileTwo eps u

theorem QuarticFourSignedPolePair.threeTapProjectiveProfileHalf_continuous
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    Continuous (W.threeTapProjectiveProfileHalf eps) := by
  unfold QuarticFourSignedPolePair.threeTapProjectiveProfileHalf
  exact genericProjectivePhysicalProfile_continuous
    (detectorThreeTap_contDiff
      (quarticFourPhysicalDetector_contDiff W.Rpos)
      eps (Real.log 2)).continuous
    (t/16)

theorem QuarticFourSignedPolePair.threeTapProjectiveProfileTwo_continuous
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    Continuous (W.threeTapProjectiveProfileTwo eps) := by
  unfold QuarticFourSignedPolePair.threeTapProjectiveProfileTwo
  exact genericProjectivePhysicalProfile_continuous
    (detectorThreeTap_contDiff
      (quarticFourPhysicalDetector_contDiff W.Rpos)
      eps (Real.log 2)).continuous
    (t/16)

theorem QuarticFourSignedPolePair.threeTapProjectiveProfileHalf_compact
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasCompactSupport (W.threeTapProjectiveProfileHalf eps) := by
  unfold QuarticFourSignedPolePair.threeTapProjectiveProfileHalf
  exact genericProjectivePhysicalProfile_compact
    (detectorThreeTap_compact
      (quarticFourPhysicalDetector_compact
        W.Rpos (by linarith : 0 < t))
      eps (Real.log 2))
    (t/16)

theorem QuarticFourSignedPolePair.threeTapProjectiveProfileTwo_compact
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasCompactSupport (W.threeTapProjectiveProfileTwo eps) := by
  unfold QuarticFourSignedPolePair.threeTapProjectiveProfileTwo
  exact genericProjectivePhysicalProfile_compact
    (detectorThreeTap_compact
      (quarticFourPhysicalDetector_compact
        W.Rpos (by linarith : 0 < t))
      eps (Real.log 2))
    (t/16)

theorem QuarticFourSignedPolePair.threeTapSignedProjectiveProfile_continuous
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    Continuous (W.threeTapSignedProjectiveProfile eps) := by
  unfold QuarticFourSignedPolePair.threeTapSignedProjectiveProfile
  fun_prop

theorem QuarticFourSignedPolePair.threeTapSignedProjectiveProfile_compact
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    HasCompactSupport (W.threeTapSignedProjectiveProfile eps) := by
  unfold QuarticFourSignedPolePair.threeTapSignedProjectiveProfile
  exact
    (W.threeTapProjectiveProfileHalf_compact ht).mul_left.add
      (W.threeTapProjectiveProfileTwo_compact ht).mul_left

/-- Source-native absolute moments for the transformed projective object. -/
def QuarticFourSignedPolePair.threeTapProjectiveAbsMoment
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (k : ℕ) : ℝ :=
  compactProfileAbsMoment (W.threeTapSignedProjectiveProfile eps) k

def QuarticFourSignedPolePair.threeTapProjectiveAbsMomentSix
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapProjectiveAbsMoment eps 6

def QuarticFourSignedPolePair.threeTapProjectiveAbsMomentEight
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapProjectiveAbsMoment eps 8

theorem QuarticFourSignedPolePair.threeTapProjectiveAbsMoment_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (k : ℕ) :
    0 <= W.threeTapProjectiveAbsMoment eps k := by
  unfold QuarticFourSignedPolePair.threeTapProjectiveAbsMoment
    compactProfileAbsMoment
  positivity

/-! ## Normalized source-shift firewall -/

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

/-- A literal shifted source copy is centered outside the canonical normalized
Taylor radius.  Therefore a new local/far split is required before the old
post-sixth terminal compiler can consume the transformed detector. -/
theorem QuarticFourSignedPolePair.threeTap_requires_adaptive_local_recut
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    quarticSignedPoleCanonicalLocalRadius
      * threeTapNormalizedShift t (Real.log 2) > 1 := by
  exact W.canonical_q_times_threeTapShift_gt_one ht

/-- The adaptive physical half-width associated to the expanded source support. -/
theorem QuarticFourSignedPolePair.threeTapAdaptivePhysicalHalfWidth_eq
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    (t/16) * W.threeTapAdaptiveLocalRadius
      =
    (t/16) /
      ((Real.pi + 1)
        + |threeTapNormalizedShift t (Real.log 2)|) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalRadius
    QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
  ring

/-- Explicit firewall: this equality is NOT asserted.  It names the exact
object-identification debt that a future moment-transport theorem would have to
pay before generic shift formulas can be reused after projectivization. -/
def QuarticFourSignedPolePair.ThreeTapProjectiveShiftCommutes
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : Prop :=
  W.threeTapSignedProjectiveProfile eps
    =
  detectorThreeTap
    (fun u =>
      W.poleTwo *
        genericProjectivePhysicalProfile
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          (t/16) u
      + (-W.poleHalf) *
        genericProjectivePhysicalProfile
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          (t/16) u)
    eps (Real.log 2)

end Synthesis
