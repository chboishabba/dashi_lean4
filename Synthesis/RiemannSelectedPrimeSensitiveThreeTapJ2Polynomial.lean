import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveRemainder

/-!
# Exact epsilon-polynomial for the transformed J2 coordinate

The near-line fork is controlled by the transformed signed projective second
moment J2_eps.  This file computes it exactly as a degree-two polynomial in
the tap strength.  The degree-two term is real: both the source column and the
on-line response column move.

The baseline coefficient is proved zero from the selected witness's original
J2 cancellations.  Thus the first open sign question is the explicit linear /
quadratic coefficient combination, not whether projectivization commutes with
translation.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

theorem projectiveSqEvenResp_detectorThreeTap_eq
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (eps L s : ℝ) :
    projectiveSqEvenResp (detectorThreeTap g eps L) s
      =
    projectiveSqEvenResp g s
      + eps * projectiveSqEvenResp (threeTapShiftPair g L) s := by
  have hshiftc := threeTapShiftPair_continuous hg L
  have hshiftk := threeTapShiftPair_compact hgc L
  have h0 :
      Integrable (fun u : ℝ => g u * u^2 * Real.cos (s*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hgc.mul_right).mul_right)
  have h1 :
      Integrable
        (fun u : ℝ =>
          threeTapShiftPair g L u * u^2 * Real.cos (s*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hshiftk.mul_right).mul_right)
  unfold projectiveSqEvenResp
  rw [show
      (fun u : ℝ =>
        detectorThreeTap g eps L u * u^2 * Real.cos (s*u))
      =
      fun u =>
        g u * u^2 * Real.cos (s*u)
          + eps *
            (threeTapShiftPair g L u * u^2 * Real.cos (s*u)) by
      funext u
      rw [detectorThreeTap_eq_base_add_shiftPair]
      ring]
  rw [integral_add h0 (h1.const_mul eps), integral_const_mul]

def projectiveBracketSecondMomentThreeTapLinearCoeff
    (g : ℝ → ℝ) (L r : ℝ) : ℝ :=
  let S := threeTapShiftPair g L
  Zeta23Bridge.LiteralWeilParityBalance.evenResp S 0 r
      * projectiveSqEvenResp g (2*r)
    +
  Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 r
      * projectiveSqEvenResp S (2*r)
    -
  Zeta23Bridge.LiteralWeilParityBalance.evenResp S 0 (2*r)
      * projectiveSqEvenResp g r
    -
  Zeta23Bridge.LiteralWeilParityBalance.evenResp g 0 (2*r)
      * projectiveSqEvenResp S r

def projectiveBracketSecondMomentThreeTapQuadraticCoeff
    (g : ℝ → ℝ) (L r : ℝ) : ℝ :=
  let S := threeTapShiftPair g L
  Zeta23Bridge.LiteralWeilParityBalance.evenResp S 0 r
      * projectiveSqEvenResp S (2*r)
    -
  Zeta23Bridge.LiteralWeilParityBalance.evenResp S 0 (2*r)
      * projectiveSqEvenResp S r

theorem projectiveBracketSecondMoment_detectorThreeTap_quadratic
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (eps L r : ℝ) :
    projectiveBracketSecondMoment (detectorThreeTap g eps L) r
      =
    projectiveBracketSecondMoment g r
      + eps * projectiveBracketSecondMomentThreeTapLinearCoeff g L r
      + eps^2 * projectiveBracketSecondMomentThreeTapQuadraticCoeff g L r := by
  have hgt : Continuous (detectorThreeTap g eps L) := by
    exact (detectorThreeTap_contDiff
      (by simpa using hg.contDiff) eps L).continuous
  have hgk : HasCompactSupport (detectorThreeTap g eps L) :=
    detectorThreeTap_compact hgc eps L
  rw [projectiveBracketSecondMoment_eq_response_det hgt hgk r,
      projectiveBracketSecondMoment_eq_response_det hg hgc r,
      evenResp_detectorThreeTap_eq hg hgc,
      evenResp_detectorThreeTap_eq hg hgc,
      projectiveSqEvenResp_detectorThreeTap_eq hg hgc,
      projectiveSqEvenResp_detectorThreeTap_eq hg hgc]
  unfold projectiveBracketSecondMomentThreeTapLinearCoeff
    projectiveBracketSecondMomentThreeTapQuadraticCoeff
  dsimp
  ring

/-- Pole-weighted selected J2 written directly as the two endpoint projective
second moments. -/
def QuarticFourSignedPolePair.threeTapSelectedJ2
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.poleTwo *
      projectiveBracketSecondMoment (W.threeTapHalf eps) (t/16)
    -
  W.poleHalf *
      projectiveBracketSecondMoment (W.threeTapTwo eps) (t/16)

theorem QuarticFourSignedPolePair.threeTapSignedJ2_eq_selectedJ2
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedJ2 eps = W.threeTapSelectedJ2 eps := by
  let P1 := W.threeTapProjectiveProfileHalf eps
  let P2 := W.threeTapProjectiveProfileTwo eps
  have h1 :
      Integrable (fun u : ℝ => P1 u * u^2) :=
    Continuous.integrable_of_hasCompactSupport
      (by dsimp [P1]; fun_prop)
      (W.threeTapProjectiveProfileHalf_compact ht).mul_right
  have h2 :
      Integrable (fun u : ℝ => P2 u * u^2) :=
    Continuous.integrable_of_hasCompactSupport
      (by dsimp [P2]; fun_prop)
      (W.threeTapProjectiveProfileTwo_compact ht).mul_right
  unfold QuarticFourSignedPolePair.threeTapSignedJ2
    QuarticFourSignedPolePair.threeTapSelectedJ2
    QuarticFourSignedPolePair.threeTapSignedProjectiveProfile
  rw [show
      (fun u : ℝ =>
        (W.poleTwo * W.threeTapProjectiveProfileHalf eps u
          + (-W.poleHalf) * W.threeTapProjectiveProfileTwo eps u) * u^2)
      =
      fun u =>
        W.poleTwo * (W.threeTapProjectiveProfileHalf eps u * u^2)
          + (-W.poleHalf) *
            (W.threeTapProjectiveProfileTwo eps u * u^2) by
      funext u
      ring,
      integral_add (h1.const_mul _) (h2.const_mul _),
      integral_const_mul, integral_const_mul]
  unfold QuarticFourSignedPolePair.threeTapProjectiveProfileHalf
    QuarticFourSignedPolePair.threeTapProjectiveProfileTwo
  rw [genericProjectivePhysicalProfile_secondMoment,
      genericProjectivePhysicalProfile_secondMoment]
  ring

def QuarticFourSignedPolePair.threeTapSelectedJ2LinearCoeff
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.poleTwo *
      projectiveBracketSecondMomentThreeTapLinearCoeff
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
        (Real.log 2) (t/16)
    -
  W.poleHalf *
      projectiveBracketSecondMomentThreeTapLinearCoeff
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
        (Real.log 2) (t/16)

def QuarticFourSignedPolePair.threeTapSelectedJ2QuadraticCoeff
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.poleTwo *
      projectiveBracketSecondMomentThreeTapQuadraticCoeff
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
        (Real.log 2) (t/16)
    -
  W.poleHalf *
      projectiveBracketSecondMomentThreeTapQuadraticCoeff
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
        (Real.log 2) (t/16)

theorem QuarticFourSignedPolePair.threeTapSelectedJ2_zeroStrength
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSelectedJ2 0 = 0 := by
  have hr : 0 < t/16 := by linarith
  unfold QuarticFourSignedPolePair.threeTapSelectedJ2
    QuarticFourSignedPolePair.threeTapHalf
    QuarticFourSignedPolePair.threeTapTwo
    detectorThreeTap
  simp only [zero_mul, add_zero]
  unfold quarticFourPhysicalDetector
  rw [projectiveBracketSecondMoment_rescale
        (quarticFourWindowProfile_continuous W.Rpos)
        (quarticFourWindowProfile_compact W.Rpos) hr,
      projectiveBracketSecondMoment_rescale
        (quarticFourWindowProfile_continuous W.Rpos)
        (quarticFourWindowProfile_compact W.Rpos) hr,
      W.J2Half, W.J2Two]
  ring

/-- Exact near-line decision polynomial.  The constant coefficient vanishes. -/
theorem QuarticFourSignedPolePair.threeTapSignedJ2_quadratic
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedJ2 eps
      =
    eps * W.threeTapSelectedJ2LinearCoeff
      + eps^2 * W.threeTapSelectedJ2QuadraticCoeff := by
  rw [W.threeTapSignedJ2_eq_selectedJ2 ht]
  unfold QuarticFourSignedPolePair.threeTapSelectedJ2
    QuarticFourSignedPolePair.threeTapSelectedJ2LinearCoeff
    QuarticFourSignedPolePair.threeTapSelectedJ2QuadraticCoeff
    QuarticFourSignedPolePair.threeTapHalf
    QuarticFourSignedPolePair.threeTapTwo
  rw [projectiveBracketSecondMoment_detectorThreeTap_quadratic
        (quarticFourPhysicalDetector_contDiff W.Rpos).continuous
        (quarticFourPhysicalDetector_compact W.Rpos (by linarith : 0 < t)),
      projectiveBracketSecondMoment_detectorThreeTap_quadratic
        (quarticFourPhysicalDetector_contDiff W.Rpos).continuous
        (quarticFourPhysicalDetector_compact W.Rpos (by linarith : 0 < t))]
  have h0 := W.threeTapSelectedJ2_zeroStrength ht
  unfold QuarticFourSignedPolePair.threeTapSelectedJ2
    QuarticFourSignedPolePair.threeTapHalf
    QuarticFourSignedPolePair.threeTapTwo
    detectorThreeTap at h0
  simp only [zero_mul, add_zero] at h0
  ring_nf at h0 ⊢
  linarith

/-- The transformed target remains quartic at the line exactly when this
explicit epsilon-polynomial vanishes. -/
theorem QuarticFourSignedPolePair.threeTap_quartic_line_condition
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapSignedJ2 eps = 0
      ↔
    eps * W.threeTapSelectedJ2LinearCoeff
      + eps^2 * W.threeTapSelectedJ2QuadraticCoeff = 0 := by
  rw [W.threeTapSignedJ2_quadratic ht]

end Synthesis
