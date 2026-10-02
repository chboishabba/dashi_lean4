import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2Phase
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapNormalizedProjective

/-!
# Normalize the transformed J2 coefficient sign problem

The physical detector is a rescale of the normalized detector with shift
B=rL.  Since projective J2 scales as r^-4, the epsilon-linear and
epsilon-quadratic coefficients scale by exactly the same positive factor.

Thus their signs are decided at normalized sampling radius 1 with the sole
height dependence entering through B=(t/16)log2.
-/

noncomputable section
namespace Synthesis

open scoped Real

theorem projectiveBracketSecondMomentThreeTap_coeffs_rescale
    {G : ℝ → ℝ} {r : ℝ}
    (hG : Continuous G)
    (hGc : HasCompactSupport G)
    (hr : 0 < r)
    (L : ℝ) :
    projectiveBracketSecondMomentThreeTapLinearCoeff
        (projectiveRescaleProfile G r) L r
      =
    (1/r^4) *
      projectiveBracketSecondMomentThreeTapLinearCoeff G (r*L) 1
    ∧
    projectiveBracketSecondMomentThreeTapQuadraticCoeff
        (projectiveRescaleProfile G r) L r
      =
    (1/r^4) *
      projectiveBracketSecondMomentThreeTapQuadraticCoeff G (r*L) 1 := by
  let gp := projectiveRescaleProfile G r
  have hgp : Continuous gp :=
    projectiveRescaleProfile_continuous hG r
  have hgpc : HasCompactSupport gp :=
    projectiveRescaleProfile_compact hGc hr.ne'
  have hdet (eps : ℝ) :
      projectiveBracketSecondMoment
          (detectorThreeTap gp eps L) r
        =
      (1/r^4) *
        projectiveBracketSecondMoment
          (detectorThreeTap G eps (r*L)) 1 := by
    have hweld :
        detectorThreeTap gp eps L
          =
        projectiveRescaleProfile
          (detectorThreeTap G eps (r*L)) r := by
      simpa [gp] using
        detectorThreeTap_projectiveRescaleProfile G r eps L
    rw [hweld]
    apply projectiveBracketSecondMoment_rescale
    · unfold detectorThreeTap
      fun_prop
    · exact detectorThreeTap_compact hGc eps (r*L)
    · exact hr
  have hp1 := hdet 1
  have hpm1 := hdet (-1)
  rw [projectiveBracketSecondMoment_detectorThreeTap_quadratic
        hgp hgpc,
      projectiveBracketSecondMoment_detectorThreeTap_quadratic
        hG hGc] at hp1
  rw [projectiveBracketSecondMoment_detectorThreeTap_quadratic
        hgp hgpc,
      projectiveBracketSecondMoment_detectorThreeTap_quadratic
        hG hGc] at hpm1
  have hbase :=
    projectiveBracketSecondMoment_rescale hG hGc hr
  constructor <;> nlinarith

def QuarticFourSignedPolePair.threeTapNormalizedJ2LinearCoeff
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let B := threeTapNormalizedShift t (Real.log 2)
  W.poleTwo *
      projectiveBracketSecondMomentThreeTapLinearCoeff
        (quarticFourWindowProfile W.R (1/2) W.muHalf) B 1
    -
  W.poleHalf *
      projectiveBracketSecondMomentThreeTapLinearCoeff
        (quarticFourWindowProfile W.R (2/3) W.muTwo) B 1

def QuarticFourSignedPolePair.threeTapNormalizedJ2QuadraticCoeff
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let B := threeTapNormalizedShift t (Real.log 2)
  W.poleTwo *
      projectiveBracketSecondMomentThreeTapQuadraticCoeff
        (quarticFourWindowProfile W.R (1/2) W.muHalf) B 1
    -
  W.poleHalf *
      projectiveBracketSecondMomentThreeTapQuadraticCoeff
        (quarticFourWindowProfile W.R (2/3) W.muTwo) B 1

theorem QuarticFourSignedPolePair.threeTapSelectedJ2LinearCoeff_rescale
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSelectedJ2LinearCoeff
      =
    (1/(t/16)^4) * W.threeTapNormalizedJ2LinearCoeff := by
  have hr : 0 < t/16 := by linarith
  have hhalf :=
    projectiveBracketSecondMomentThreeTap_coeffs_rescale
      (quarticFourWindowProfile_continuous W.Rpos)
      (quarticFourWindowProfile_compact W.Rpos)
      hr (Real.log 2)
  have htwo :=
    projectiveBracketSecondMomentThreeTap_coeffs_rescale
      (quarticFourWindowProfile_continuous W.Rpos)
      (quarticFourWindowProfile_compact W.Rpos)
      hr (Real.log 2)
  unfold QuarticFourSignedPolePair.threeTapSelectedJ2LinearCoeff
    QuarticFourSignedPolePair.threeTapNormalizedJ2LinearCoeff
    quarticFourPhysicalDetector
    threeTapNormalizedShift
  rw [hhalf.1, htwo.1]
  ring

theorem QuarticFourSignedPolePair.threeTapSelectedJ2QuadraticCoeff_rescale
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSelectedJ2QuadraticCoeff
      =
    (1/(t/16)^4) * W.threeTapNormalizedJ2QuadraticCoeff := by
  have hr : 0 < t/16 := by linarith
  have hhalf :=
    projectiveBracketSecondMomentThreeTap_coeffs_rescale
      (quarticFourWindowProfile_continuous W.Rpos)
      (quarticFourWindowProfile_compact W.Rpos)
      hr (Real.log 2)
  have htwo :=
    projectiveBracketSecondMomentThreeTap_coeffs_rescale
      (quarticFourWindowProfile_continuous W.Rpos)
      (quarticFourWindowProfile_compact W.Rpos)
      hr (Real.log 2)
  unfold QuarticFourSignedPolePair.threeTapSelectedJ2QuadraticCoeff
    QuarticFourSignedPolePair.threeTapNormalizedJ2QuadraticCoeff
    quarticFourPhysicalDetector
    threeTapNormalizedShift
  rw [hhalf.2, htwo.2]
  ring

/-- Exact normalized near-line decision equation.  The positive physical
r^-4 factor has been removed. -/
theorem QuarticFourSignedPolePair.threeTapSignedJ2_eq_normalized_polynomial
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedJ2 eps
      =
    (1/(t/16)^4)
      *
    (eps * W.threeTapNormalizedJ2LinearCoeff
      + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff) := by
  rw [W.threeTapSignedJ2_quadratic ht,
      W.threeTapSelectedJ2LinearCoeff_rescale ht,
      W.threeTapSelectedJ2QuadraticCoeff_rescale ht]
  ring

theorem QuarticFourSignedPolePair.threeTapSignedJ2_zero_iff_normalized
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedJ2 eps = 0
      ↔
    eps * W.threeTapNormalizedJ2LinearCoeff
      + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff = 0 := by
  rw [W.threeTapSignedJ2_eq_normalized_polynomial ht]
  have hr : 0 < t/16 := by linarith
  have hfac : (1/(t/16)^4 : ℝ) ≠ 0 := by positivity
  exact mul_eq_zero.trans (by simp [hfac])

end Synthesis
