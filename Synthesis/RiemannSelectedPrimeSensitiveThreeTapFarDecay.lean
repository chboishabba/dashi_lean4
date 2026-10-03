import Synthesis.RiemannSelectedPrimeSensitiveThreeTapFiniteAsymptotic
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapPairSignedCut
import Zeta23Bridge.OscillatoryKernelDecay

/-!
# Reciprocal-square decay of the actual transformed pair kernel

The half-height adverse tail is not merely an abstract summable remainder.
The actual normalized pair kernel is a cosine transform of a compact C2
profile.  Twice integrating by parts therefore gives q^-2 decay.

After restoring the projective scaling, the two powers of t/16 cancel:

  mult/(t/16)^2 * K(alpha)/q^2
    = mult*K(alpha)/(gamma-t)^2.

Thus the genuinely distributional tail problem is reduced to a weighted
inverse-square zero-count sum, rather than an arbitrary reflection-pair tsum.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators
open Zeta23Bridge.OscillatoryKernelDecay

/-- The actual normalized signed projective profile is C2. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile_contDiff_two
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    ContDiff ℝ 2 (W.threeTapNormalizedSignedProjectiveProfile eps) := by
  have hHalfBase :
      ContDiff ℝ 2 (quarticFourWindowProfile W.R (1/2) W.muHalf) :=
    quarticFourWindowProfile_contDiff W.Rpos
  have hTwoBase :
      ContDiff ℝ 2 (quarticFourWindowProfile W.R (2/3) W.muTwo) :=
    quarticFourWindowProfile_contDiff W.Rpos
  have hHalfTap :
      ContDiff ℝ 2 (W.threeTapNormalizedHalf eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedHalf
    exact detectorThreeTap_contDiff hHalfBase eps
      (threeTapNormalizedShift t (Real.log 2))
  have hTwoTap :
      ContDiff ℝ 2 (W.threeTapNormalizedTwo eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedTwo
    exact detectorThreeTap_contDiff hTwoBase eps
      (threeTapNormalizedShift t (Real.log 2))
  have hHalfProj :
      ContDiff ℝ 2 (W.threeTapNormalizedProjectiveHalf eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveHalf
      genericProjectivePhysicalProfile twoRadiusBracket
    fun_prop
  have hTwoProj :
      ContDiff ℝ 2 (W.threeTapNormalizedProjectiveTwo eps) := by
    unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveTwo
      genericProjectivePhysicalProfile twoRadiusBracket
    fun_prop
  unfold QuarticFourSignedPolePair.threeTapNormalizedSignedProjectiveProfile
  exact (contDiff_const.mul hHalfProj).add (contDiff_const.mul hTwoProj)

/-- Oscillatory profile for one normalized horizontal displacement alpha. -/
def QuarticFourSignedPolePair.threeTapPairOscillatoryProfile
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha : ℝ) : ℝ → ℝ :=
  fun v => W.threeTapNormalizedSignedProjectiveProfile eps v
    * Real.cosh (alpha*v)

theorem QuarticFourSignedPolePair.threeTapPairOscillatoryProfile_contDiff_two
    {t eps alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    ContDiff ℝ 2 (W.threeTapPairOscillatoryProfile eps alpha) := by
  unfold QuarticFourSignedPolePair.threeTapPairOscillatoryProfile
  exact (W.threeTapNormalizedSignedProjectiveProfile_contDiff_two (eps:=eps)).mul
    (by fun_prop)

theorem QuarticFourSignedPolePair.threeTapPairOscillatoryProfile_compact
    {t eps alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    HasCompactSupport (W.threeTapPairOscillatoryProfile eps alpha) := by
  unfold QuarticFourSignedPolePair.threeTapPairOscillatoryProfile
  exact (W.threeTapNormalizedProjective_compact (eps:=eps)).mul_right

/-- L1 curvature controlling two integrations by parts. -/
def QuarticFourSignedPolePair.threeTapPairOscillatoryCurvature
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps alpha : ℝ) : ℝ :=
  ∫ v : ℝ,
    |deriv (deriv (W.threeTapPairOscillatoryProfile eps alpha)) v|

theorem QuarticFourSignedPolePair.threeTapPairOscillatoryCurvature_nonneg
    {t eps alpha : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapPairOscillatoryCurvature eps alpha := by
  unfold QuarticFourSignedPolePair.threeTapPairOscillatoryCurvature
  exact integral_nonneg fun v => abs_nonneg _

/-- The normalized pair kernel has the standard q^-2 Fourier decay. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedPairKernel_abs_le_invSq
    {t eps alpha q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hq : q ≠ 0) :
    |W.threeTapNormalizedPairKernel eps alpha q|
      <= W.threeTapPairOscillatoryCurvature eps alpha / q^2 := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedPairKernel
    QuarticFourSignedPolePair.threeTapPairOscillatoryProfile
  exact abs_integral_mul_cos_le
    (W.threeTapPairOscillatoryProfile_contDiff_two (eps:=eps) (alpha:=alpha))
    (W.threeTapPairOscillatoryProfile_compact (eps:=eps) (alpha:=alpha))
    hq

/-- Physical-coordinate form of the per-zero decay.  The projective scaling
cancels exactly against q=((gamma-t)/(t/16)). -/
theorem QuarticFourSignedPolePair.threeTapAdaptivePairTerm_abs_le_inverseSquare
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hord : ((rho : ℂ).im - t) ≠ 0) :
    |W.threeTapAdaptivePairTerm eps rho|
      <=
    ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * W.threeTapPairOscillatoryCurvature eps
          (heightOf rho / (t/16))
      / (((rho : ℂ).im - t)^2) := by
  have hr : 0 < t/16 := by linarith
  have hr0 : t/16 ≠ 0 := ne_of_gt hr
  have hq : ((rho : ℂ).im - t)/(t/16) ≠ 0 := div_ne_zero hord hr0
  have hk := W.threeTapNormalizedPairKernel_abs_le_invSq
    (eps:=eps)
    (alpha:=heightOf rho/(t/16))
    (q:=((rho : ℂ).im-t)/(t/16)) hq
  have hmNat :
      (1 : ℕ) <= (Zeta23.zetaZeroConfig).mult (rho : ℂ) :=
    (Zeta23.zetaZeroConfig).one_le_mult (rho : ℂ) rho.2
  have hm : 0 <= ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
    positivity
  unfold QuarticFourSignedPolePair.threeTapAdaptivePairTerm
  have hcoef : 0 <= ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2 := by
    positivity
  rw [abs_mul, abs_of_nonneg hcoef]
  calc
    ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
        * |W.threeTapNormalizedPairKernel eps
            (heightOf rho/(t/16))
            (((rho : ℂ).im-t)/(t/16))|
      <= ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
        * (W.threeTapPairOscillatoryCurvature eps
            (heightOf rho/(t/16))
          / ((((rho : ℂ).im-t)/(t/16))^2)) :=
        mul_le_mul_of_nonneg_left hk hcoef
    _ = ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * W.threeTapPairOscillatoryCurvature eps
            (heightOf rho/(t/16))
        / (((rho : ℂ).im-t)^2) := by
      field_simp [hr0, hord]
      ring

/-- The favorable/adverse split never exceeds the absolute pair size, so the
same inverse-square majorant applies to the actual adverse contribution. -/
theorem QuarticFourSignedPolePair.threeTapPairAdversePart_le_inverseSquare
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hord : ((rho : ℂ).im - t) ≠ 0) :
    W.threeTapPairAdversePart eps rho
      <=
    ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * W.threeTapPairOscillatoryCurvature eps
          (heightOf rho / (t/16))
      / (((rho : ℂ).im - t)^2) := by
  have habs := W.threeTapAdaptivePairTerm_abs_le_inverseSquare ht rho hord (eps:=eps)
  have hpart : W.threeTapPairAdversePart eps rho
      <= |W.threeTapAdaptivePairTerm eps rho| := by
    unfold QuarticFourSignedPolePair.threeTapPairAdversePart
    by_cases h : 0 <= W.threeTapAdaptivePairTerm eps rho
    · rw [abs_of_nonneg h]
      ring_nf
      exact le_rfl
    · have h' := le_of_not_ge h
      rw [abs_of_nonpos h']
      ring_nf
      exact neg_nonneg.mpr h'
  exact hpart.trans habs

end Synthesis
