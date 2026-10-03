import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseFinalCut
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Canonical asymptotic budget for the one-scale adverse cut

The final one-scale scalar is already reduced to an RvM-compatible cutoff R.
This file exposes the actual t-scaling of its finite-core terms.

The key observation is that the canonical horizontal radius A=8/t shrinks at
exactly the rate needed to cancel the O(t) growth of the translated normalized
support.  For t>=200,

  A * supportRadius < 1.

Hence every canonical cosh weight is bounded by cosh(1), uniformly in t.  The
finite RvM budget can therefore be bounded using only the ordinary normalized
profile masses M0 and M1, with the physical scales

  phi       : O(t^-2) M0,
  Lip(phi)  : O(t^-3) M1,
  mu window : O(R t^-2 log t) M0.

At the canonical corridor R=t/2 this becomes

  mu window : O((log t)/t) M0,
  endpoint  : O((log t)/t^2) M0,
  Abel tail : O((log t)/t^2) M1.

No asymptotic bound on M0/M1 or on the compensation is asserted here.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval

/-- Exact product of the canonical horizontal radius with the transformed
normalized support. -/
theorem QuarticFourSignedPolePair.threeTapCanonicalAlpha_mul_support_eq
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    threeTapCanonicalAlphaRadius t * W.threeTapNormalizedSupportRadius
      =
    (8/t) * (Real.pi + 1)
      + (1/2 : ℝ) * Real.log 2 := by
  have hshift : 0 < threeTapNormalizedShift t (Real.log 2) := by
    unfold threeTapNormalizedShift
    positivity
  unfold threeTapCanonicalAlphaRadius
    QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
    threeTapNormalizedShift
  rw [abs_of_pos hshift]
  field_simp [ne_of_gt ht]
  ring

/-- Uniform canonical support control: despite the translated support growing
linearly in t, the canonical alpha weight times that support stays below one. -/
theorem QuarticFourSignedPolePair.threeTapCanonicalAlpha_mul_support_lt_one
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    threeTapCanonicalAlphaRadius t * W.threeTapNormalizedSupportRadius < 1 := by
  have ht0 : 0 < t := by linarith
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  rw [W.threeTapCanonicalAlpha_mul_support_eq ht0]
  have hfirst : (8/t) * (Real.pi + 1) < (1/5 : ℝ) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ ht0]
    have ht200 : 200 <= t := ht
    nlinarith
  have hsecond : (1/2 : ℝ) * Real.log 2 < 1/2 := by
    nlinarith
  linarith

/-- On the actual transformed support, the canonical cosh factor is bounded by
`cosh 1`, uniformly for every t>=200. -/
theorem QuarticFourSignedPolePair.threeTapCanonicalCosh_le_cosh_one
    {t eps v : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hv : W.threeTapNormalizedSignedProjectiveProfile eps v ≠ 0) :
    Real.cosh (threeTapCanonicalAlphaRadius t * |v|) <= Real.cosh 1 := by
  have hA : 0 <= threeTapCanonicalAlphaRadius t :=
    threeTapCanonicalAlphaRadius_nonneg (by linarith)
  have hs := W.threeTapNormalizedSignedProjective_support hv
  have hAS :
      threeTapCanonicalAlphaRadius t * |v|
        <= threeTapCanonicalAlphaRadius t * W.threeTapNormalizedSupportRadius :=
    mul_le_mul_of_nonneg_left hs.le hA
  have hone :
      threeTapCanonicalAlphaRadius t * |v| <= 1 :=
    hAS.trans (W.threeTapCanonicalAlpha_mul_support_lt_one ht).le
  rw [Real.cosh_le_cosh]
  rw [abs_of_nonneg (mul_nonneg hA (abs_nonneg v)), abs_of_nonneg (by norm_num : (0:ℝ) <= 1)]
  exact hone

/-- Canonical adverse sup mass is controlled by the ordinary normalized M0
mass with a t-independent cosh(1) factor. -/
theorem QuarticFourSignedPolePair.threeTapKernelAdverseCanonicalSupMass_le
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapKernelAdverseAlphaSupMass eps (threeTapCanonicalAlphaRadius t)
      <=
    Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps := by
  let P := W.threeTapNormalizedSignedProjectiveProfile eps
  have hleft : Integrable
      (fun v : ℝ =>
        Real.cosh (threeTapCanonicalAlphaRadius t * |v|) * |P v|) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((W.threeTapNormalizedProjective_compact (eps:=eps)).abs.mul_left)
  have hright : Integrable (fun v : ℝ => Real.cosh 1 * |P v|) := by
    exact (W.threeTapNormalizedProjective_continuous (eps:=eps)).abs
      |>.integrable_of_hasCompactSupport
        (W.threeTapNormalizedProjective_compact (eps:=eps)).abs
      |>.const_mul _
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseAlphaSupMass
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMass
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMoment
    compactProfileAbsMoment
  rw [show (∫ v : ℝ, Real.cosh 1 * |P v| * |v|^0)
      = ∫ v : ℝ, Real.cosh 1 * |P v| by
        apply integral_congr_ae
        filter_upwards with v
        simp]
  rw [integral_const_mul]
  apply integral_mono hleft hright
  intro v
  by_cases hv : P v = 0
  · simp [hv]
  · exact mul_le_mul_of_nonneg_right
      (W.threeTapCanonicalCosh_le_cosh_one ht hv)
      (abs_nonneg (P v))

/-- Canonical adverse Lipschitz mass is controlled by the ordinary normalized
first absolute moment with the same t-independent cosh(1) factor. -/
theorem QuarticFourSignedPolePair.threeTapKernelAdverseCanonicalLipschitzMass_le
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapKernelAdverseAlphaLipschitzMass eps (threeTapCanonicalAlphaRadius t)
      <=
    Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMoment eps 1 := by
  let P := W.threeTapNormalizedSignedProjectiveProfile eps
  have hleft : Integrable
      (fun v : ℝ =>
        Real.cosh (threeTapCanonicalAlphaRadius t * |v|) * |P v| * |v|) := by
    exact W.threeTapKernelAdverseAlphaLipschitzMass_integrable
      (eps:=eps) (A:=threeTapCanonicalAlphaRadius t)
  have hright : Integrable (fun v : ℝ => Real.cosh 1 * (|P v| * |v|)) := by
    exact (compactProfile_absMoment_integrable
      (W.threeTapNormalizedProjective_continuous (eps:=eps))
      (W.threeTapNormalizedProjective_compact (eps:=eps)) 1).const_mul _
  unfold QuarticFourSignedPolePair.threeTapKernelAdverseAlphaLipschitzMass
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMoment
    compactProfileAbsMoment
  rw [integral_const_mul]
  apply integral_mono hleft hright
  intro v
  by_cases hv : P v = 0
  · simp [hv]
  · have hc := W.threeTapCanonicalCosh_le_cosh_one ht hv
    have huv : 0 <= |P v| * |v| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      Real.cosh (threeTapCanonicalAlphaRadius t * |v|) * |P v| * |v|
        = Real.cosh (threeTapCanonicalAlphaRadius t * |v|) * (|P v| * |v|) := by ring
      _ <= Real.cosh 1 * (|P v| * |v|) :=
        mul_le_mul_of_nonneg_right hc huv

/-- Source-visible t^-2 bound for the physical adverse test. -/
theorem QuarticFourSignedPolePair.threeTapAdverseCanonicalPhysicalTest_le
    {t eps x : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdversePhysicalOrdinateTest eps (threeTapCanonicalAlphaRadius t) x
      <=
    (256/t^2) * (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps) := by
  have ht0 : 0 < t := by linarith
  have hsup := W.threeTapAdversePhysicalOrdinateTest_le_supMass ht0
    (eps:=eps) (A:=threeTapCanonicalAlphaRadius t) (x:=x)
  have hmass := W.threeTapKernelAdverseCanonicalSupMass_le ht
  have hcoef : 0 <= (1/(t/16)^2 : ℝ) := by positivity
  calc
    W.threeTapAdversePhysicalOrdinateTest eps (threeTapCanonicalAlphaRadius t) x
      <= (1/(t/16)^2) *
        W.threeTapKernelAdverseAlphaSupMass eps (threeTapCanonicalAlphaRadius t) := hsup
    _ <= (1/(t/16)^2) *
        (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps) :=
      mul_le_mul_of_nonneg_left hmass hcoef
    _ = (256/t^2) *
        (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps) := by
      field_simp [ne_of_gt ht0]
      ring

/-- Source-visible t^-3 bound for the physical Lipschitz mass. -/
theorem QuarticFourSignedPolePair.threeTapAdverseCanonicalPhysicalLipschitzMass_le
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdversePhysicalLipschitzMass eps (threeTapCanonicalAlphaRadius t)
      <=
    (4096/t^3) *
      (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMoment eps 1) := by
  have ht0 : 0 < t := by linarith
  unfold QuarticFourSignedPolePair.threeTapAdversePhysicalLipschitzMass
  have hmass := W.threeTapKernelAdverseCanonicalLipschitzMass_le ht
  have hden : 0 <= (t/16)^3 := by positivity
  have hdiv := div_le_div_of_nonneg_right hmass hden
  calc
    W.threeTapKernelAdverseAlphaLipschitzMass eps (threeTapCanonicalAlphaRadius t) / (t/16)^3
      <= (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMoment eps 1) / (t/16)^3 := hdiv
    _ = (4096/t^3) *
        (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMoment eps 1) := by
      field_simp [ne_of_gt ht0]
      ring

/-- Coarser finite-core budget displaying only its source-visible t,R scales. -/
def QuarticFourSignedPolePair.threeTapAdverseNearScaleBudget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps R C Cmu : ℝ) : ℝ :=
  let E := C * (Real.log ((t-R)+3) + Real.log ((t+R)+4))
  let M0 := Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps
  let M1 := Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMoment eps 1
  (2*R) * ((256/t^2) * M0) * (Cmu * Real.log ((t+R)+3))
    + E * ((256/t^2) * M0)
    + (2*R) * E * ((4096/t^3) * M1)

/-- The fully explicit near budget is bounded by the scale-table budget. -/
theorem QuarticFourSignedPolePair.threeTapAdverseNearExplicitBudget_le_scaleBudget
    {t eps R C Cmu : ℝ}
    (ht : 200 <= t)
    (hR : 0 <= R)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu)
    (hleft : 5 <= t-R)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdverseNearExplicitBudget eps
        (threeTapCanonicalAlphaRadius t) R C Cmu
      <= W.threeTapAdverseNearScaleBudget eps R C Cmu := by
  have ht0 : 0 < t := by linarith
  let E := C * (Real.log ((t-R)+3) + Real.log ((t+R)+4))
  let M0 := Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps
  let M1 := Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMoment eps 1
  have hE : 0 <= E := by
    dsimp [E]
    have hL : 0 <= Real.log ((t-R)+3) := Real.log_nonneg (by linarith)
    have hU : 0 <= Real.log ((t+R)+4) := Real.log_nonneg (by linarith)
    exact mul_nonneg hC (add_nonneg hL hU)
  have hU : 0 <= Cmu * Real.log ((t+R)+3) := by
    exact mul_nonneg hCmu (Real.log_nonneg (by linarith))
  have hM0 : 0 <= M0 := by
    dsimp [M0]
    exact mul_nonneg (Real.cosh_pos _).le
      (W.threeTapNormalizedProjectiveAbsMoment_nonneg (eps:=eps) 0)
  have hM1 : 0 <= M1 := by
    dsimp [M1]
    exact mul_nonneg (Real.cosh_pos _).le
      (W.threeTapNormalizedProjectiveAbsMoment_nonneg (eps:=eps) 1)
  have htest := W.threeTapAdverseCanonicalPhysicalTest_le ht
    (eps:=eps) (x:=t+R)
  have hlip := W.threeTapAdverseCanonicalPhysicalLipschitzMass_le ht
    (eps:=eps)
  have hmass := W.threeTapKernelAdverseCanonicalSupMass_le ht (eps:=eps)
  unfold QuarticFourSignedPolePair.threeTapAdverseNearExplicitBudget
    QuarticFourSignedPolePair.threeTapAdverseNearScaleBudget
  dsimp [E,M0,M1]
  have hcoef : 0 <= (1/(t/16)^2 : ℝ) := by positivity
  have hmuScale :
      (1/(t/16)^2) *
          W.threeTapKernelAdverseAlphaSupMass eps (threeTapCanonicalAlphaRadius t)
        <=
      (256/t^2) *
          (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps) := by
    calc
      (1/(t/16)^2) *
          W.threeTapKernelAdverseAlphaSupMass eps (threeTapCanonicalAlphaRadius t)
        <= (1/(t/16)^2) *
          (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps) :=
        mul_le_mul_of_nonneg_left hmass hcoef
      _ = _ := by
        field_simp [ne_of_gt ht0]
        ring
  gcongr

/-- The simple corridor R=t/2 is RvM-compatible throughout the current high-t
range. -/
theorem QuarticFourSignedPolePair.threeTapHalfHeightCutoff_compatible
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.ThreeTapRvMCompatibleCutoff (t/2) := by
  constructor
  · linarith
  · linarith

/-- Specialized scale budget at the canonical corridor R=t/2.  This is the
budget table used for the asymptotic sign comparison. -/
def QuarticFourSignedPolePair.threeTapAdverseHalfHeightScaleBudget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps C Cmu : ℝ) : ℝ :=
  W.threeTapAdverseNearScaleBudget eps (t/2) C Cmu

end Synthesis
