import Synthesis.RiemannQuantitativeTaperMixingBound
import Synthesis.RiemannQuantitativeSymmetricBumpMass
import Zeta23Bridge.LiteralWeilEvenChannelTaper

/-!
# Quantitative canonical two-window taper

Rebuild the canonical pole-killing taper using the same fixed affine bump in both
windows.  This preserves the historical sign geometry while exposing explicit
L1 derivative scaling.

For t >= 18:

  R  = pi/(4t),
  r  = t/16,
  c1 = 2pi/t,
  c2 = pi/t,

  g1 = symmetric bump at c1,
  g2 = symmetric bump at c2,

  lambda = -Pole(g2,t,r) / Pole(g1,t,r),
  g = g2 + lambda g1.

The theorem owns:
  Pole(g,t,r)=0,
  0 < lambda <= quantitativeMixUpper,
and explicit M0/M1/M2 upper bounds for g.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOddChannelTaper
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

def quantitativeOuterPole (t : ℝ) : ℝ :=
  poleEvenResp (quantitativeOuterBump t) t (quantitativeSampleRadius t)

def quantitativeInnerPole (t : ℝ) : ℝ :=
  poleEvenResp (quantitativeInnerBump t) t (quantitativeSampleRadius t)

def quantitativeLambda (t : ℝ) : ℝ :=
  - quantitativeInnerPole t / quantitativeOuterPole t

def quantitativeCanonicalTaper (t : ℝ) : ℝ → ℝ :=
  fun u =>
    quantitativeInnerBump t u
      + quantitativeLambda t * quantitativeOuterBump t u

def quantitativeTaperMass0Upper (t : ℝ) : ℝ :=
  2 * quantitativeTaperR t * unitBumpMass0 * (1 + quantitativeMixUpper)

def quantitativeTaperMass1Upper : ℝ :=
  2 * unitBumpMass1 * (1 + quantitativeMixUpper)

def quantitativeTaperMass2Upper (t : ℝ) : ℝ :=
  2 * (quantitativeTaperR t)⁻¹ * unitBumpMass2 * (1 + quantitativeMixUpper)

def quantitativePoleWeight (t s u : ℝ) : ℝ :=
  Real.cosh (u / 2) * Real.cos (t*u) * Real.cos (s*u)

theorem quantitativeTaperR_pos {t : ℝ} (ht : 0 < t) :
    0 < quantitativeTaperR t := by
  unfold quantitativeTaperR
  positivity

theorem quantitativeOuterBump_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (quantitativeOuterBump t) := by
  unfold quantitativeOuterBump quantitativeSymBump
  exact (symmetrize_contDiff
    (scaledUnitBump_contDiff (quantitativeTaperR_pos ht).ne'
      (quantitativeTaperOuterCenter t))).continuous

theorem quantitativeInnerBump_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (quantitativeInnerBump t) := by
  unfold quantitativeInnerBump quantitativeSymBump
  exact (symmetrize_contDiff
    (scaledUnitBump_contDiff (quantitativeTaperR_pos ht).ne'
      (quantitativeTaperInnerCenter t))).continuous

theorem quantitativeOuterBump_compact {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (quantitativeOuterBump t) := by
  unfold quantitativeOuterBump
  exact quantitativeSymBump_hasCompactSupport (quantitativeTaperR_pos ht)

theorem quantitativeInnerBump_compact {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (quantitativeInnerBump t) := by
  unfold quantitativeInnerBump
  exact quantitativeSymBump_hasCompactSupport (quantitativeTaperR_pos ht)

theorem outerUnitPoleIntegral_pos {t : ℝ} (ht : 18 <= t) :
    0 < ∫ u : ℝ,
      scaledUnitBump (quantitativeTaperOuterCenter t) (quantitativeTaperR t) u
        * quantitativePoleWeight t (quantitativeSampleRadius t) u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  apply scaledUnitBump_positive_integral (quantitativeTaperR_pos ht0)
  · unfold quantitativePoleWeight
    fun_prop
  · intro u hu
    have hhalf := outerPoleWeight_ge_half ht0 hu
    unfold quantitativePoleWeight
    linarith

theorem innerUnitPoleIntegral_neg {t : ℝ} (ht : 18 <= t) :
    (∫ u : ℝ,
      scaledUnitBump (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
        * quantitativePoleWeight t (quantitativeSampleRadius t) u) < 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hpos :
      0 < ∫ u : ℝ,
        scaledUnitBump (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
          * (- quantitativePoleWeight t (quantitativeSampleRadius t) u) := by
    apply scaledUnitBump_positive_integral (quantitativeTaperR_pos ht0)
    · unfold quantitativePoleWeight
      fun_prop
    · intro u hu
      unfold quantitativePoleWeight quantitativeSampleRadius
      unfold quantitativeTaperInnerCenter quantitativeTaperR at hu
      rw [abs_lt] at hu
      have hlow : 3 * Real.pi / (4*t) < u := by
        field_simp at hu ⊢
        nlinarith [Real.pi_pos]
      have hhigh : u < 5 * Real.pi / (4*t) := by
        field_simp at hu ⊢
        nlinarith [Real.pi_pos]
      have htuLow : 3 * Real.pi / 4 < t*u := by
        have h := mul_lt_mul_of_pos_left hlow ht0
        field_simp at h
        exact h
      have htuHigh : t*u < 5 * Real.pi / 4 := by
        have h := mul_lt_mul_of_pos_left hhigh ht0
        field_simp at h
        exact h
      have hct : Real.cos (t*u) < 0 := by
        have hs : 0 < Real.cos (t*u - Real.pi) := by
          apply Real.cos_pos_of_mem_Ioo
          constructor <;> linarith
        rw [Real.cos_sub_pi] at hs
        linarith
      have hsample :
          0 < Real.cos ((t/16)*u) := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · have hu0 : 0 < u := lt_trans (by positivity) hlow
          nlinarith
        · nlinarith [htuHigh, Real.pi_pos]
      have hch : 0 < Real.cosh (u/2) := Real.cosh_pos _
      positivity
  have hrw :
      (fun u : ℝ =>
        scaledUnitBump (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
          * (-quantitativePoleWeight t (quantitativeSampleRadius t) u))
      =
      fun u : ℝ => -
        (scaledUnitBump (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
          * quantitativePoleWeight t (quantitativeSampleRadius t) u) := by
    funext u
    ring
  rw [hrw, integral_neg] at hpos
  linarith

theorem quantitativeOuterPole_eq_two_integral {t : ℝ} (ht : 0 < t) :
    quantitativeOuterPole t
      =
    2 * ∫ u : ℝ,
      scaledUnitBump (quantitativeTaperOuterCenter t) (quantitativeTaperR t) u
        * quantitativePoleWeight t (quantitativeSampleRadius t) u := by
  unfold quantitativeOuterPole quantitativeOuterBump
  rw [poleEvenResp]
  exact integral_symmetrize
    (scaledUnitBump_continuous (quantitativeTaperR_pos ht).ne'
      (quantitativeTaperOuterCenter t))
    (scaledUnitBump_hasCompactSupport (quantitativeTaperR_pos ht))
    (by unfold quantitativePoleWeight; fun_prop)
    (by
      intro u
      unfold quantitativePoleWeight
      simp [Real.cosh_neg, Real.cos_neg])

theorem quantitativeInnerPole_eq_two_integral {t : ℝ} (ht : 0 < t) :
    quantitativeInnerPole t
      =
    2 * ∫ u : ℝ,
      scaledUnitBump (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
        * quantitativePoleWeight t (quantitativeSampleRadius t) u := by
  unfold quantitativeInnerPole quantitativeInnerBump
  rw [poleEvenResp]
  exact integral_symmetrize
    (scaledUnitBump_continuous (quantitativeTaperR_pos ht).ne'
      (quantitativeTaperInnerCenter t))
    (scaledUnitBump_hasCompactSupport (quantitativeTaperR_pos ht))
    (by unfold quantitativePoleWeight; fun_prop)
    (by
      intro u
      unfold quantitativePoleWeight
      simp [Real.cosh_neg, Real.cos_neg])

theorem quantitativeOuterPole_pos {t : ℝ} (ht : 18 <= t) :
    0 < quantitativeOuterPole t := by
  rw [quantitativeOuterPole_eq_two_integral (lt_of_lt_of_le (by norm_num) ht)]
  linarith [outerUnitPoleIntegral_pos ht]

theorem quantitativeInnerPole_neg {t : ℝ} (ht : 18 <= t) :
    quantitativeInnerPole t < 0 := by
  rw [quantitativeInnerPole_eq_two_integral (lt_of_lt_of_le (by norm_num) ht)]
  linarith [innerUnitPoleIntegral_neg ht]

theorem quantitativeOuterPole_lower {t : ℝ} (ht : 18 <= t) :
    quantitativeTaperR t * unitBumpMass0
      <= quantitativeOuterPole t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [quantitativeOuterPole_eq_two_integral ht0]
  let phi := scaledUnitBump
    (quantitativeTaperOuterCenter t) (quantitativeTaperR t)
  have hphi : Continuous phi :=
    scaledUnitBump_continuous (quantitativeTaperR_pos ht0).ne' _
  have hphic : HasCompactSupport phi :=
    scaledUnitBump_hasCompactSupport (quantitativeTaperR_pos ht0)
  have hiPhi : Integrable phi :=
    hphi.integrable_of_hasCompactSupport hphic
  have hiWeighted : Integrable
      (fun u : ℝ => phi u *
        quantitativePoleWeight t (quantitativeSampleRadius t) u) :=
    Zeta23Bridge.LiteralWeilParityBalance.taper_integrable
      hphi hphic (by unfold quantitativePoleWeight; fun_prop)
  have hpoint : ∀ u : ℝ,
      (1/2 : ℝ) * phi u
        <= phi u * quantitativePoleWeight t (quantitativeSampleRadius t) u := by
    intro u
    by_cases hu : phi u = 0
    · simp [hu]
    · have hwin := scaledUnitBump_support (quantitativeTaperR_pos ht0) hu
      have hw := outerPoleWeight_ge_half ht0 hwin
      exact mul_le_mul_of_nonneg_left hw
        (scaledUnitBump_nonneg _ _ _)
  have hint := integral_mono
    (hiPhi.const_mul (1/2 : ℝ)) hiWeighted hpoint
  rw [integral_const_mul] at hint
  have hmass :
      (∫ u : ℝ, phi u)
        = quantitativeTaperR t * unitBumpMass0 := by
    have habs :
        (fun u : ℝ => |phi u|) = phi := by
      funext u
      rw [abs_of_nonneg (scaledUnitBump_nonneg _ _ _)]
    have hm := taperMass_scaledUnitBump
      (c := quantitativeTaperOuterCenter t)
      (quantitativeTaperR_pos ht0)
    unfold taperMass at hm
    rw [habs] at hm
    exact hm
  rw [hmass] at hint
  nlinarith

theorem quantitativeInnerPole_abs_upper {t : ℝ} (ht : 18 <= t) :
    -quantitativeInnerPole t
      <= 2 * Real.cosh (5 * Real.pi / 144)
        * quantitativeTaperR t * unitBumpMass0 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [quantitativeInnerPole_eq_two_integral ht0]
  let phi := scaledUnitBump
    (quantitativeTaperInnerCenter t) (quantitativeTaperR t)
  have hphi : Continuous phi :=
    scaledUnitBump_continuous (quantitativeTaperR_pos ht0).ne' _
  have hphic : HasCompactSupport phi :=
    scaledUnitBump_hasCompactSupport (quantitativeTaperR_pos ht0)
  have hiPhi : Integrable phi :=
    hphi.integrable_of_hasCompactSupport hphic
  have hiNegWeighted : Integrable
      (fun u : ℝ => -(phi u *
        quantitativePoleWeight t (quantitativeSampleRadius t) u)) :=
    (Zeta23Bridge.LiteralWeilParityBalance.taper_integrable
      hphi hphic (by unfold quantitativePoleWeight; fun_prop)).neg
  have hpoint : ∀ u : ℝ,
      -(phi u * quantitativePoleWeight t (quantitativeSampleRadius t) u)
        <= Real.cosh (5 * Real.pi / 144) * phi u := by
    intro u
    by_cases hu : phi u = 0
    · simp [hu]
    · have hwin := scaledUnitBump_support (quantitativeTaperR_pos ht0) hu
      have habs := innerPoleWeight_abs_le ht hwin
      have hphi0 := scaledUnitBump_nonneg
        (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
      have hnegLeAbs :
          -quantitativePoleWeight t (quantitativeSampleRadius t) u
            <= |quantitativePoleWeight t (quantitativeSampleRadius t) u| :=
        neg_le_abs _
      nlinarith
  have hint := integral_mono hiNegWeighted
    ((hiPhi.const_mul (Real.cosh (5*Real.pi/144)))) hpoint
  rw [integral_neg, integral_const_mul] at hint
  have hmass :
      (∫ u : ℝ, phi u)
        = quantitativeTaperR t * unitBumpMass0 := by
    have habs :
        (fun u : ℝ => |phi u|) = phi := by
      funext u
      rw [abs_of_nonneg (scaledUnitBump_nonneg _ _ _)]
    have hm := taperMass_scaledUnitBump
      (c := quantitativeTaperInnerCenter t)
      (quantitativeTaperR_pos ht0)
    unfold taperMass at hm
    rw [habs] at hm
    exact hm
  rw [hmass] at hint
  nlinarith

theorem quantitativeLambda_pos {t : ℝ} (ht : 18 <= t) :
    0 < quantitativeLambda t := by
  unfold quantitativeLambda
  exact div_pos (by linarith [quantitativeInnerPole_neg ht])
    (quantitativeOuterPole_pos ht)

theorem quantitativeLambda_le {t : ℝ} (ht : 18 <= t) :
    quantitativeLambda t <= quantitativeMixUpper := by
  unfold quantitativeLambda
  exact quantitativeMixingRatio_le ht
    (quantitativeOuterPole_lower ht)
    (quantitativeInnerPole_abs_upper ht)
    (quantitativeOuterPole_pos ht)
    (quantitativeInnerPole_neg ht)

theorem quantitativeCanonicalTaper_pole_zero
    {t : ℝ} (ht : 18 <= t) :
    poleEvenResp (quantitativeCanonicalTaper t) t
      (quantitativeSampleRadius t) = 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold quantitativeCanonicalTaper
  rw [poleEvenResp_add_smul
    (quantitativeInnerBump_continuous ht0)
    (quantitativeInnerBump_compact ht0)
    (quantitativeOuterBump_continuous ht0)
    (quantitativeOuterBump_compact ht0)]
  unfold quantitativeLambda quantitativeOuterPole quantitativeInnerPole
  field_simp [ne_of_gt (quantitativeOuterPole_pos ht)]
  ring

theorem taperMass_add_smul_le
    {f g : ℝ → ℝ} {lam : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hlam : 0 <= lam) :
    taperMass (fun u => f u + lam * g u)
      <= taperMass f + lam * taperMass g := by
  have hfi : Integrable (fun u : ℝ => |f u|) :=
    hf.abs.integrable_of_hasCompactSupport hfc.abs
  have hgi : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  have hrhs : Integrable (fun u : ℝ => |f u| + lam * |g u|) :=
    hfi.add (hgi.const_mul lam)
  have hlhs : Integrable (fun u : ℝ => |f u + lam * g u|) :=
    (hf.add (continuous_const.mul hg)).abs.integrable_of_hasCompactSupport
      (hfc.add hgc.mul_left).abs
  have hpt : ∀ u,
      |f u + lam * g u| <= |f u| + lam * |g u| := by
    intro u
    have h := abs_add (f u) (lam * g u)
    rw [abs_mul, abs_of_nonneg hlam] at h
    exact h
  have h := integral_mono hlhs hrhs hpt
  unfold taperMass
  rw [integral_add hfi (hgi.const_mul lam), integral_const_mul]
  exact h

theorem quantitativeCanonicalTaper_mass0_le
    {t : ℝ} (ht : 18 <= t) :
    taperMass (quantitativeCanonicalTaper t)
      <= quantitativeTaperMass0Upper t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold quantitativeCanonicalTaper quantitativeTaperMass0Upper
  have h :=
    taperMass_add_smul_le
      (quantitativeInnerBump_continuous ht0)
      (quantitativeInnerBump_compact ht0)
      (quantitativeOuterBump_continuous ht0)
      (quantitativeOuterBump_compact ht0)
      (quantitativeLambda_pos ht).le
  have hi := taperMass_quantitativeSymBump_le
    (c := quantitativeTaperInnerCenter t) (quantitativeTaperR_pos ht0)
  have ho := taperMass_quantitativeSymBump_le
    (c := quantitativeTaperOuterCenter t) (quantitativeTaperR_pos ht0)
  have hlam := quantitativeLambda_le ht
  nlinarith [mul_nonneg hlam (unitBumpMass0_nonneg)]


theorem quantitativeOuterBump_contDiff {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 2 (quantitativeOuterBump t) := by
  unfold quantitativeOuterBump quantitativeSymBump
  exact symmetrize_contDiff
    (scaledUnitBump_contDiff (quantitativeTaperR_pos ht).ne'
      (quantitativeTaperOuterCenter t))

theorem quantitativeInnerBump_contDiff {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 2 (quantitativeInnerBump t) := by
  unfold quantitativeInnerBump quantitativeSymBump
  exact symmetrize_contDiff
    (scaledUnitBump_contDiff (quantitativeTaperR_pos ht).ne'
      (quantitativeTaperInnerCenter t))

theorem quantitativeCanonicalTaper_contDiff
    {t : ℝ} (ht : 18 <= t) :
    ContDiff ℝ 2 (quantitativeCanonicalTaper t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold quantitativeCanonicalTaper
  exact (quantitativeInnerBump_contDiff ht0).add
    (contDiff_const.mul (quantitativeOuterBump_contDiff ht0))

theorem deriv_quantitativeCanonicalTaper
    {t : ℝ} (ht : 18 <= t) :
    deriv (quantitativeCanonicalTaper t)
      =
    fun u =>
      deriv (quantitativeInnerBump t) u
        + quantitativeLambda t * deriv (quantitativeOuterBump t) u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hi : Differentiable ℝ (quantitativeInnerBump t) :=
    (quantitativeInnerBump_contDiff ht0).differentiable (by norm_num)
  have ho : Differentiable ℝ (quantitativeOuterBump t) :=
    (quantitativeOuterBump_contDiff ht0).differentiable (by norm_num)
  funext u
  have hs :=
    (hi u).hasDerivAt.add
      ((ho u).hasDerivAt.const_mul (quantitativeLambda t))
  rw [hs.deriv]
  unfold quantitativeCanonicalTaper
  ring

theorem deriv2_quantitativeCanonicalTaper
    {t : ℝ} (ht : 18 <= t) :
    deriv (deriv (quantitativeCanonicalTaper t))
      =
    fun u =>
      deriv (deriv (quantitativeInnerBump t)) u
        + quantitativeLambda t *
          deriv (deriv (quantitativeOuterBump t)) u := by
  rw [deriv_quantitativeCanonicalTaper ht]
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hi : Differentiable ℝ (deriv (quantitativeInnerBump t)) :=
    (quantitativeInnerBump_contDiff ht0).differentiable_deriv_two
  have ho : Differentiable ℝ (deriv (quantitativeOuterBump t)) :=
    (quantitativeOuterBump_contDiff ht0).differentiable_deriv_two
  funext u
  have hs :=
    (hi u).hasDerivAt.add
      ((ho u).hasDerivAt.const_mul (quantitativeLambda t))
  rw [hs.deriv]
  ring

theorem quantitativeCanonicalTaper_compact
    {t : ℝ} (ht : 18 <= t) :
    HasCompactSupport (quantitativeCanonicalTaper t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold quantitativeCanonicalTaper
  exact (quantitativeInnerBump_compact ht0).add
    (quantitativeOuterBump_compact ht0).mul_left

theorem quantitativeCanonicalTaper_mass1_le
    {t : ℝ} (ht : 18 <= t) :
    taperMass (deriv (quantitativeCanonicalTaper t))
      <= quantitativeTaperMass1Upper := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [deriv_quantitativeCanonicalTaper ht]
  unfold quantitativeTaperMass1Upper
  have hiC := (quantitativeInnerBump_contDiff ht0).deriv'.continuous
  have hoC := (quantitativeOuterBump_contDiff ht0).deriv'.continuous
  have hiK := (quantitativeInnerBump_compact ht0).deriv
  have hoK := (quantitativeOuterBump_compact ht0).deriv
  have h :=
    taperMass_add_smul_le
      hiC hiK hoC hoK (quantitativeLambda_pos ht).le
  have hi := taperMass_deriv_quantitativeSymBump_le
    (c := quantitativeTaperInnerCenter t) (quantitativeTaperR_pos ht0)
  have ho := taperMass_deriv_quantitativeSymBump_le
    (c := quantitativeTaperOuterCenter t) (quantitativeTaperR_pos ht0)
  have hlam := quantitativeLambda_le ht
  have hM := unitBumpMass1_nonneg
  nlinarith [mul_nonneg hlam hM]

theorem quantitativeCanonicalTaper_mass2_le
    {t : ℝ} (ht : 18 <= t) :
    taperMass (deriv (deriv (quantitativeCanonicalTaper t)))
      <= quantitativeTaperMass2Upper t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [deriv2_quantitativeCanonicalTaper ht]
  unfold quantitativeTaperMass2Upper
  have hiC :=
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.continuous_deriv2
      (quantitativeInnerBump_contDiff ht0)
  have hoC :=
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.continuous_deriv2
      (quantitativeOuterBump_contDiff ht0)
  have hiK := (quantitativeInnerBump_compact ht0).deriv.deriv
  have hoK := (quantitativeOuterBump_compact ht0).deriv.deriv
  have h :=
    taperMass_add_smul_le
      hiC hiK hoC hoK (quantitativeLambda_pos ht).le
  have hi := taperMass_deriv2_quantitativeSymBump_le
    (c := quantitativeTaperInnerCenter t) (quantitativeTaperR_pos ht0)
  have ho := taperMass_deriv2_quantitativeSymBump_le
    (c := quantitativeTaperOuterCenter t) (quantitativeTaperR_pos ht0)
  have hlam := quantitativeLambda_le ht
  have hM := unitBumpMass2_nonneg
  have hRinv : 0 <= (quantitativeTaperR t)⁻¹ :=
    (inv_pos.mpr (quantitativeTaperR_pos ht0)).le
  nlinarith [mul_nonneg hlam (mul_nonneg hRinv hM)]


end Synthesis
