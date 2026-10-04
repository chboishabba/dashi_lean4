import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveMixed
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2Normalized

/-!
# Exact adaptive degree-six jet for the transformed projective profile

The old selected witness had M0=M2=0, so its local degree-six reference
collapsed to quartic + signed sixth harmonic.  After the three-tap
deformation M2 need not vanish.

This file keeps the transformed local jet honest:

  integral P_eps(v) T6(alpha v,q v)
    = c2 M2_eps + c4 M4_eps + c6 M6_eps,

with M0_eps=0 proved from projectivization itself.

Together with the adaptive mixed eighth-order remainder, this is the correct
local compiler core in both the quadratic and exceptional quartic branches.
-/

noncomputable section
namespace Synthesis

open MeasureTheory
open scoped Real

def QuarticFourSignedPolePair.threeTapNormalizedSignedMoment
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (k : ℕ) : ℝ :=
  ∫ v : ℝ,
    W.threeTapNormalizedSignedProjectiveProfile eps v * v^k

def QuarticFourSignedPolePair.threeTapNormalizedM2
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapNormalizedSignedMoment eps 2

def QuarticFourSignedPolePair.threeTapNormalizedM4
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapNormalizedSignedMoment eps 4

def QuarticFourSignedPolePair.threeTapNormalizedM6
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapNormalizedSignedMoment eps 6

theorem QuarticFourSignedPolePair.threeTapNormalizedM0_zero
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedSignedMoment eps 0 = 0 := by
  let g1 := W.threeTapNormalizedHalf eps
  let g2 := W.threeTapNormalizedTwo eps
  have hg1 : Continuous g1 := by
    unfold g1 QuarticFourSignedPolePair.threeTapNormalizedHalf detectorThreeTap
    fun_prop
  have hg2 : Continuous g2 := by
    unfold g2 QuarticFourSignedPolePair.threeTapNormalizedTwo detectorThreeTap
    fun_prop
  have hk1 : HasCompactSupport g1 := by
    unfold g1 QuarticFourSignedPolePair.threeTapNormalizedHalf
    exact detectorThreeTap_compact
      (quarticFourWindowProfile_compact W.Rpos) eps _
  have hk2 : HasCompactSupport g2 := by
    unfold g2 QuarticFourSignedPolePair.threeTapNormalizedTwo
    exact detectorThreeTap_compact
      (quarticFourWindowProfile_compact W.Rpos) eps _
  have h1 := genericProjectivePhysicalProfile_integral_zero hg1 hk1 1
  have h2 := genericProjectivePhysicalProfile_integral_zero hg2 hk2 1
  unfold QuarticFourSignedPolePair.threeTapNormalizedSignedMoment
    QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
  simp only [pow_zero, mul_one]
  have hi1 :
      Integrable
        (W.threeTapNormalizedProjectiveHalf eps) :=
    W.threeTapNormalizedProjective_continuous
      |>.integrable_of_hasCompactSupport
        W.threeTapNormalizedProjective_compact
  -- linearity is discharged directly on the two endpoint integrals.
  rw [show
      (fun v : ℝ =>
        W.poleTwo * W.threeTapNormalizedProjectiveHalf eps v
          + (-W.poleHalf) * W.threeTapNormalizedProjectiveTwo eps v)
      =
      fun v =>
        W.poleTwo * W.threeTapNormalizedProjectiveHalf eps v
          + (-W.poleHalf) * W.threeTapNormalizedProjectiveTwo eps v by rfl]
  have hp1 :
      Integrable (W.threeTapNormalizedProjectiveHalf eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
    exact
      (genericProjectivePhysicalProfile_continuous hg1 1)
        .integrable_of_hasCompactSupport
          (genericProjectivePhysicalProfile_compact hk1 1)
  have hp2 :
      Integrable (W.threeTapNormalizedProjectiveTwo eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
    exact
      (genericProjectivePhysicalProfile_continuous hg2 1)
        .integrable_of_hasCompactSupport
          (genericProjectivePhysicalProfile_compact hk2 1)
  rw [integral_add (hp1.const_mul _) (hp2.const_mul _),
      integral_const_mul, integral_const_mul]
  unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf at h1
  unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo at h2
  rw [h1,h2]
  ring

def mixedDegreeSixC2 (alpha q : ℝ) : ℝ :=
  (alpha^2 - q^2)/2

def mixedDegreeSixC4 (alpha q : ℝ) : ℝ :=
  (alpha^4 + q^4 - 6*alpha^2*q^2)/24

def mixedDegreeSixC6 (alpha q : ℝ) : ℝ :=
  quarticSignedPoleSixthPhaseReal alpha q / 720

theorem QuarticFourSignedPolePair.threeTapMixedDegreeSix_referenceIntegral
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    (∫ v : ℝ,
      W.threeTapNormalizedSignedProjectiveProfile eps v
        * quarticSignedPoleMixedDegreeSixTaylor (alpha*v) (q*v))
      =
    mixedDegreeSixC2 alpha q * W.threeTapNormalizedM2 eps
      + mixedDegreeSixC4 alpha q * W.threeTapNormalizedM4 eps
      + mixedDegreeSixC6 alpha q * W.threeTapNormalizedM6 eps := by
  let P := W.threeTapNormalizedSignedProjectiveProfile eps
  have hP : Continuous P := W.threeTapNormalizedProjective_continuous
  have hPc : HasCompactSupport P := W.threeTapNormalizedProjective_compact
  have h0 : Integrable P :=
    hP.integrable_of_hasCompactSupport hPc
  have h2 : Integrable (fun v : ℝ => P v * v^2) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hPc.mul_right
  have h4 : Integrable (fun v : ℝ => P v * v^4) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hPc.mul_right
  have h6 : Integrable (fun v : ℝ => P v * v^6) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hPc.mul_right
  rw [show
      (fun v : ℝ =>
        P v * quarticSignedPoleMixedDegreeSixTaylor (alpha*v) (q*v))
      =
      fun v =>
        P v
          + mixedDegreeSixC2 alpha q * (P v * v^2)
          + mixedDegreeSixC4 alpha q * (P v * v^4)
          + mixedDegreeSixC6 alpha q * (P v * v^6) by
      funext v
      unfold quarticSignedPoleMixedDegreeSixTaylor
        quarticSignedPoleSixthPhaseReal
        mixedDegreeSixC2 mixedDegreeSixC4 mixedDegreeSixC6
      ring]
  rw [integral_add
        (h0.add (h2.const_mul _)).add (h4.const_mul _)
        (h6.const_mul _),
      integral_add (h0.add (h2.const_mul _)) (h4.const_mul _),
      integral_add h0 (h2.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [show (∫ v : ℝ, P v) = 0 by
      simpa [P, QuarticFourSignedPolePair.threeTapNormalizedSignedMoment]
        using W.threeTapNormalizedM0_zero (eps:=eps)]
  unfold QuarticFourSignedPolePair.threeTapNormalizedM2
    QuarticFourSignedPolePair.threeTapNormalizedM4
    QuarticFourSignedPolePair.threeTapNormalizedM6
    QuarticFourSignedPolePair.threeTapNormalizedSignedMoment
  dsimp [P]
  ring

def QuarticFourSignedPolePair.threeTapNormalizedPairKernel
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha q : ℝ) : ℝ :=
  ∫ v : ℝ,
    W.threeTapNormalizedSignedProjectiveProfile eps v
      * Real.cosh (alpha*v) * Real.cos (q*v)

def QuarticFourSignedPolePair.threeTapNormalizedDegreeSixJet
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha q : ℝ) : ℝ :=
  mixedDegreeSixC2 alpha q * W.threeTapNormalizedM2 eps
    + mixedDegreeSixC4 alpha q * W.threeTapNormalizedM4 eps
    + mixedDegreeSixC6 alpha q * W.threeTapNormalizedM6 eps

theorem QuarticFourSignedPolePair.threeTapNormalizedPairKernel_eq_jet_add_remainder
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedPairKernel eps alpha q
      =
    W.threeTapNormalizedDegreeSixJet eps alpha q
      + W.threeTapNormalizedMixedSixthRemainder eps alpha q := by
  let P := W.threeTapNormalizedSignedProjectiveProfile eps
  have hP : Continuous P := W.threeTapNormalizedProjective_continuous
  have hPc : HasCompactSupport P := W.threeTapNormalizedProjective_compact
  have hexact :
      Integrable (fun v : ℝ =>
        P v * Real.cosh (alpha*v) * Real.cos (q*v)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have href :
      Integrable (fun v : ℝ =>
        P v * quarticSignedPoleMixedDegreeSixTaylor (alpha*v) (q*v)) :=
    Continuous.integrable_of_hasCompactSupport
      (by
        unfold quarticSignedPoleMixedDegreeSixTaylor
          quarticSignedPoleSixthPhaseReal
        fun_prop)
      hPc.mul_right
  unfold QuarticFourSignedPolePair.threeTapNormalizedPairKernel
    QuarticFourSignedPolePair.threeTapNormalizedMixedSixthRemainder
    compactMixedSixthRemainder
    QuarticFourSignedPolePair.threeTapNormalizedDegreeSixJet
  rw [← W.threeTapMixedDegreeSix_referenceIntegral (eps:=eps)
      (alpha:=alpha) (q:=q)]
  rw [← integral_add href (hexact.sub href)]
  apply integral_congr_ae
  filter_upwards with v
  ring

theorem QuarticFourSignedPolePair.threeTapNormalizedPairKernel_sub_jet_abs_le
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (ha : |alpha| <= W.threeTapAdaptiveLocalRadius)
    (hq : |q| <= W.threeTapAdaptiveLocalRadius) :
    |W.threeTapNormalizedPairKernel eps alpha q
      - W.threeTapNormalizedDegreeSixJet eps alpha q|
      <=
    quarticSignedPoleMixedEighthEnvelope alpha q
      * W.threeTapNormalizedProjectiveAbsMomentEight eps := by
  rw [W.threeTapNormalizedPairKernel_eq_jet_add_remainder]
  ring_nf
  exact W.threeTapNormalizedMixedSixthRemainder_abs_le ha hq

end Synthesis
