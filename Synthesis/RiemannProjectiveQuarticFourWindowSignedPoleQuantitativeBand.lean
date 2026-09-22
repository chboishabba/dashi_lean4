import Synthesis.RiemannCompactCoshQuantitativeQuarticBand
import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleCutset

/-!
# Explicit quantitative band for the signed four-window pole-cancelled observable

The original `QuarticFourSignedPolePair` stores an existential punctured
radius `eps`.  For the Clay-facing route that is stronger bookkeeping than
needed and weaker numerically than desired: the consumer only needs a concrete
radius which can be compared with the normalized critical-strip width `8/t`.

For the combined signed profile P we already know

  M0(P) = 0,
  M2(P) = 0,
  M4(P) = -4 * signedTargetStrength.

The generic compact-cosh fourth-order compiler therefore gives the explicit
radius

  min 1 ((4 * signedTargetStrength) /
    (2 * (compactCoshFourthLipschitzConstant P + 1))).

This file installs that radius on the exact signed-pole witness and rebuilds the
target-pair lower bound and contradiction compiler using it directly.  Thus the
old existential `W.eps` is no longer on the preferred terminal path.

No theorem here proves the remaining scalar inequality `8/t < radius`; that
is the quantitative uniformity theorem which must be supplied by actual
analysis.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23

def QuarticFourSignedPolePair.quantitativeTargetRadius
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  quantitativeFourthOrderRadius
    (4 * W.signedTargetStrength)
    (compactCoshFourthLipschitzConstant
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t))

theorem QuarticFourSignedPolePair.quantitativeTargetRadius_pos
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 < W.quantitativeTargetRadius := by
  unfold QuarticFourSignedPolePair.quantitativeTargetRadius
  exact quantitativeFourthOrderRadius_pos
    (by nlinarith [W.signedTargetStrength])
    (compactCoshFourthLipschitzConstant_nonneg _)

/--
The signed combined height defect is positive on the explicit quantitative
fourth-order band.  This is the constructive replacement for
`W.combinedTargetBand`.
-/
theorem QuarticFourSignedPolePair.quantitativeCombinedTargetBand
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (a : ℝ)
    (ha0 : 0 < |a|)
    (ha :
      |a| < W.quantitativeTargetRadius) :
    0 <
      quarticFourSignedPoleCombinedHeightDefect
        W.R W.muHalf W.muTwo t a := by
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  let m : ℝ := 4 * W.signedTargetStrength
  have hm : 0 < m := by
    dsimp [m]
    nlinarith [W.signedTargetStrength]
  have hP : Continuous P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hM0 : profileZerothMoment P = 0 := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_zeroth_zero W.Rpos
  have hM2 : profileSecondMoment P = 0 := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_second_zero
      W.Rpos W.J2Half W.J2Two
  have hM4 : profileFourthMoment P <= -m := by
    dsimp [P, m]
    rw [quarticFourSignedPoleCombinedProfile_fourth W.Rpos]
  have hcosh :=
    compactCosh_neg_of_quartic_margin
      hP hPc hm hM0 hM2 hM4 a ha0
  have hRadius :
      |a| <
        quantitativeFourthOrderRadius m
          (compactCoshFourthLipschitzConstant P) := by
    simpa [QuarticFourSignedPolePair.quantitativeTargetRadius, m, P]
      using ha
  have hneg := hcosh hRadius
  rw [quarticFourSignedPoleCombinedHeightDefect_eq_cosh W.Rpos]
  dsimp [P] at hneg
  nlinarith

theorem QuarticFourSignedPolePair.physicalCombinedHeightDefect_nonneg_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros) :
    0 <= W.physicalCombinedHeightDefect (heightOf rho) := by
  by_cases ha : heightOf rho = 0
  · rw [ha]
    unfold QuarticFourSignedPolePair.physicalCombinedHeightDefect
    simp [heightDefect_self]
  · have hr : 0 < t/16 := by positivity
    have hstrip := zetaZero_height_abs_le_half rho
    have hnorm0 : 0 < |heightOf rho/(t/16)| := by
      rw [abs_pos]
      exact div_ne_zero ha hr.ne'
    have hnorm :
        |heightOf rho/(t/16)| <= 8/t := by
      rw [abs_div, abs_of_pos hr]
      rw [div_le_div_iff₀ hr ht]
      nlinarith
    have hband :=
      W.quantitativeCombinedTargetBand
        (heightOf rho/(t/16)) hnorm0
        (hnorm.trans_lt hhigh)
    rw [W.physicalCombinedHeightDefect_scaled ht]
    have hfac : 0 < 1/(t/16)^2 := by positivity
    exact (mul_pos hfac hband).le

theorem QuarticFourSignedPolePair.physicalCombinedHeightDefect_pos_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 < W.physicalCombinedHeightDefect (heightOf rho) := by
  have hr : 0 < t/16 := by positivity
  have hstrip := zetaZero_height_abs_le_half rho
  have hnorm0 : 0 < |heightOf rho/(t/16)| := by
    rw [abs_pos]
    exact div_ne_zero hoff hr.ne'
  have hnorm :
      |heightOf rho/(t/16)| <= 8/t := by
    rw [abs_div, abs_of_pos hr]
    rw [div_le_div_iff₀ hr ht]
    nlinarith
  have hband :=
    W.quantitativeCombinedTargetBand
      (heightOf rho/(t/16)) hnorm0
      (hnorm.trans_lt hhigh)
  rw [W.physicalCombinedHeightDefect_scaled ht]
  have hfac : 0 < 1/(t/16)^2 := by positivity
  exact mul_pos hfac hband

theorem QuarticFourSignedPolePair.combinedZeroHeightDefect_nonneg_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros) :
    0 <= W.combinedZeroHeightDefect rho := by
  unfold QuarticFourSignedPolePair.combinedZeroHeightDefect
  exact mul_nonneg (by positivity)
    (W.physicalCombinedHeightDefect_nonneg_quantitative
      ht hhigh rho)

theorem QuarticFourSignedPolePair.combinedZeroHeightDefect_pos_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0) :
    0 < W.combinedZeroHeightDefect rho := by
  unfold QuarticFourSignedPolePair.combinedZeroHeightDefect
  exact mul_pos (by positivity)
    (W.physicalCombinedHeightDefect_pos_quantitative
      ht hhigh rho hoff)

/--
Quantitative target-pair lower bound with no dependence on the existential
`W.eps` field.
-/
theorem QuarticFourSignedPolePair.two_target_le_combinedCluster_quantitative
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    2 * W.combinedZeroHeightDefect rho
      <= W.combinedCluster := by
  have hs := W.combinedSource_summable ht
  have hsplit :=
    hs.sum_add_tsum_compl
      (s:=canonicalTargetPairFinset rho him)
  rw [W.combinedCluster_eq_tsum ht]
  rw [← hsplit, W.targetPair_sum_eq_two him hoff]
  exact le_add_of_nonneg_right
    (tsum_nonneg fun z =>
      W.combinedZeroHeightDefect_nonneg_quantitative
        ht hhigh ((z : SameOrd t) : Zeros))

/--
Preferred contradiction compiler: the only band input is now the explicit
scalar inequality against `quantitativeTargetRadius`.
-/
theorem false_of_quarticFourSignedPole_external_strict_quantitative
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.quantitativeTargetRadius)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      W.poleTwo *
        (offOrdProjectiveDefect
            (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
            t (t/16)
          +
         gammaProjectiveDefect
            (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
            t (t/16))
        +
      (-W.poleHalf) *
        (offOrdProjectiveDefect
            (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
            t (t/16)
          +
         gammaProjectiveDefect
            (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
            t (t/16))
      <
      2 * W.combinedZeroHeightDefect rho) :
    False := by
  have hlo :=
    W.two_target_le_combinedCluster_quantitative
      (by linarith : 0 < t) hhigh him hoff
  rw [W.combinedCluster_eq_offGamma ht] at hlo
  linarith

end Synthesis
