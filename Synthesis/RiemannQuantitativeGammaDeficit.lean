import Synthesis.RiemannGammaCenteredKernelCompactBridge
import Synthesis.RiemannGammaCanonicalIntegratedDeficit
import Synthesis.RiemannQuantitativeCanonicalTaper
import Zeta23Bridge.LiteralWeilGammaConeBound

/-!
# Literal quantitative Gamma deficit on the canonical pole-killing taper

This file instantiates the literal time-domain Gamma kernel on the existing
quantitative two-window taper.

For t >= 18 and r=t/16:

* P_in  = quantitativeInnerPole t < 0,
* P_out = quantitativeOuterPole t > 0,
* lambda = -P_in/P_out,
* P_in + lambda P_out = 0.

The literal centered Gamma masses of the two symmetric bumps are the actual
Gamma responses of their centered tapers. The archimedean-kernel bridge
identifies them with the same positive-side pole densities multiplied by the
Gamma/pole ratio R_t(u).

Endpoint ratio monotonicity therefore gives

  R_5 P_in <= G_in,
  R_7 P_out <= G_out,

and pole cancellation yields the literal Gamma-cone deficit

  Q_Gamma <= -2 (-P_in) canonicalGammaRatioGap(t).
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilGammaConeBound

theorem quantitativeSymBump_even (c R u : ℝ) :
    quantitativeSymBump c R (-u) = quantitativeSymBump c R u := by
  unfold quantitativeSymBump
  unfold Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
  simp [add_comm]

theorem quantitativeInnerBump_even (t u : ℝ) :
    quantitativeInnerBump t (-u) = quantitativeInnerBump t u := by
  unfold quantitativeInnerBump
  exact quantitativeSymBump_even _ _ _

theorem quantitativeOuterBump_even (t u : ℝ) :
    quantitativeOuterBump t (-u) = quantitativeOuterBump t u := by
  unfold quantitativeOuterBump
  exact quantitativeSymBump_even _ _ _

theorem quantitativeCanonicalTaper_even
    {t : ℝ} (u : ℝ) :
    quantitativeCanonicalTaper t (-u)
      = quantitativeCanonicalTaper t u := by
  unfold quantitativeCanonicalTaper
  rw [quantitativeInnerBump_even, quantitativeOuterBump_even]

def quantitativeGammaWeight (t u : ℝ) : ℝ :=
  centeredRadiusWeight t u * Real.cos (t*u) * gammaArchKernel |u|

def quantitativeInnerGamma (t : ℝ) : ℝ :=
  2 * ∫ u : ℝ,
    scaledUnitBump
      (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
      * quantitativeGammaWeight t u

def quantitativeOuterGamma (t : ℝ) : ℝ :=
  2 * ∫ u : ℝ,
    scaledUnitBump
      (quantitativeTaperOuterCenter t) (quantitativeTaperR t) u
      * quantitativeGammaWeight t u

theorem quantitativeGammaWeight_even (t u : ℝ) :
    quantitativeGammaWeight t (-u) = quantitativeGammaWeight t u := by
  unfold quantitativeGammaWeight centeredRadiusWeight
  simp [Real.cos_neg, abs_neg]

theorem gammaResp_centered_inner_eq_quantitativeInnerGamma
    {t : ℝ} (ht : 18 <= t) :
    gammaResp
      (gammaCenteredTaper
        (quantitativeInnerBump t) (quantitativeSampleRadius t))
      t 0
      = quantitativeInnerGamma t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hkernel :=
    gammaResp_centered_archKernel_exact_compact
      (quantitativeInnerBump_contDiff ht0)
      (quantitativeInnerBump_compact ht0)
      (quantitativeInnerBump_even t)
      (quantitativeSampleRadius t) t
  rw [hkernel]
  unfold quantitativeInnerGamma quantitativeGammaWeight
  have hs :=
    integral_symmetrize
      (scaledUnitBump_continuous
        (quantitativeTaperR_pos ht0).ne'
        (quantitativeTaperInnerCenter t))
      (scaledUnitBump_hasCompactSupport
        (quantitativeTaperR_pos ht0))
      (by
        unfold centeredRadiusWeight
        fun_prop)
      (by
        intro u
        simp [Real.cos_neg, abs_neg])
  unfold quantitativeInnerBump quantitativeSymBump
  unfold Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
  unfold gammaCenteredTaper centeredRadiusWeight
  rw [show
      (fun u : ℝ =>
        -( (scaledUnitBump
              (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
            + scaledUnitBump
              (quantitativeTaperInnerCenter t) (quantitativeTaperR t) (-u))
          * (Real.cos (quantitativeSampleRadius t*u)-1)
          * Real.cos (t*u) * gammaArchKernel |u|))
      =
      fun u =>
        (scaledUnitBump
              (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
            + scaledUnitBump
              (quantitativeTaperInnerCenter t) (quantitativeTaperR t) (-u))
          * ((1-Real.cos (quantitativeSampleRadius t*u))
            * Real.cos (t*u) * gammaArchKernel |u|) by
      funext u; ring]
  simpa [quantitativeSampleRadius, mul_assoc] using hs.symm

theorem gammaResp_centered_outer_eq_quantitativeOuterGamma
    {t : ℝ} (ht : 18 <= t) :
    gammaResp
      (gammaCenteredTaper
        (quantitativeOuterBump t) (quantitativeSampleRadius t))
      t 0
      = quantitativeOuterGamma t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hkernel :=
    gammaResp_centered_archKernel_exact_compact
      (quantitativeOuterBump_contDiff ht0)
      (quantitativeOuterBump_compact ht0)
      (quantitativeOuterBump_even t)
      (quantitativeSampleRadius t) t
  rw [hkernel]
  unfold quantitativeOuterGamma quantitativeGammaWeight
  have hs :=
    integral_symmetrize
      (scaledUnitBump_continuous
        (quantitativeTaperR_pos ht0).ne'
        (quantitativeTaperOuterCenter t))
      (scaledUnitBump_hasCompactSupport
        (quantitativeTaperR_pos ht0))
      (by
        unfold centeredRadiusWeight
        fun_prop)
      (by
        intro u
        simp [Real.cos_neg, abs_neg])
  unfold quantitativeOuterBump quantitativeSymBump
  unfold Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
  unfold gammaCenteredTaper centeredRadiusWeight
  rw [show
      (fun u : ℝ =>
        -( (scaledUnitBump
              (quantitativeTaperOuterCenter t) (quantitativeTaperR t) u
            + scaledUnitBump
              (quantitativeTaperOuterCenter t) (quantitativeTaperR t) (-u))
          * (Real.cos (quantitativeSampleRadius t*u)-1)
          * Real.cos (t*u) * gammaArchKernel |u|))
      =
      fun u =>
        (scaledUnitBump
              (quantitativeTaperOuterCenter t) (quantitativeTaperR t) u
            + scaledUnitBump
              (quantitativeTaperOuterCenter t) (quantitativeTaperR t) (-u))
          * ((1-Real.cos (quantitativeSampleRadius t*u))
            * Real.cos (t*u) * gammaArchKernel |u|) by
      funext u; ring]
  simpa [quantitativeSampleRadius, mul_assoc] using hs.symm

theorem quantitativeGammaWeight_eq_ratio_mul_poleWeight
    {t u : ℝ}
    (hu : 0 < u)
    (hangle0 : 0 <= (t/16)*u)
    (hanglePi2 : (t/16)*u < Real.pi/2) :
    quantitativeGammaWeight t u
      =
    gammaToPoleRatio t u
      * quantitativePoleWeight t (quantitativeSampleRadius t) u := by
  unfold quantitativeGammaWeight quantitativePoleWeight
  unfold gammaToPoleRatio poleRadiusWeight quantitativeSampleRadius
  have hc : 0 < Real.cos ((t/16)*u) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hch : Real.cosh (u/2) ≠ 0 := (Real.cosh_pos _).ne'
  rw [abs_of_pos hu]
  field_simp [hc.ne', hch]
  ring

theorem innerPoleWeight_nonpos_on_closed_window
    {t u : ℝ} (ht : 18 <= t)
    (hlo : 3*Real.pi/(4*t) <= u)
    (hhi : u <= 5*Real.pi/(4*t)) :
    quantitativePoleWeight t (quantitativeSampleRadius t) u <= 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold quantitativePoleWeight quantitativeSampleRadius
  have htuL : 3*Real.pi/4 <= t*u := by
    have h := mul_le_mul_of_nonneg_left hlo ht0.le
    field_simp [ne_of_gt ht0] at h
    nlinarith [Real.pi_pos]
  have htuH : t*u <= 5*Real.pi/4 := by
    have h := mul_le_mul_of_nonneg_left hhi ht0.le
    field_simp [ne_of_gt ht0] at h
    nlinarith [Real.pi_pos]
  have hc : Real.cos (t*u) <= 0 := by
    have hs : 0 <= Real.cos (t*u-Real.pi) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos]
    rw [Real.cos_sub_pi] at hs
    linarith
  have hsample : 0 <= Real.cos ((t/16)*u) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have hu0 : 0 <= u := le_trans (by positivity) hlo
      nlinarith
    · nlinarith [htuH, Real.pi_pos]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (Real.cosh_pos (u/2)).le hc)
    hsample

theorem outerPoleWeight_nonneg_on_closed_window
    {t u : ℝ} (ht : 18 <= t)
    (hlo : 7*Real.pi/(4*t) <= u)
    (hhi : u <= 9*Real.pi/(4*t)) :
    0 <= quantitativePoleWeight t (quantitativeSampleRadius t) u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold quantitativePoleWeight quantitativeSampleRadius
  have htuL : 7*Real.pi/4 <= t*u := by
    have h := mul_le_mul_of_nonneg_left hlo ht0.le
    field_simp [ne_of_gt ht0] at h
    nlinarith [Real.pi_pos]
  have htuH : t*u <= 9*Real.pi/4 := by
    have h := mul_le_mul_of_nonneg_left hhi ht0.le
    field_simp [ne_of_gt ht0] at h
    nlinarith [Real.pi_pos]
  have hc : 0 <= Real.cos (t*u) := by
    have hs : 0 <= Real.cos (t*u-2*Real.pi) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos]
    simpa [Real.cos_sub_int_mul_two_pi] using hs
  have hsample : 0 <= Real.cos ((t/16)*u) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have hu0 : 0 <= u := le_trans (by positivity) hlo
      nlinarith
    · nlinarith [htuH, Real.pi_pos]
  exact mul_nonneg
    (mul_nonneg (Real.cosh_pos (u/2)).le hc)
    hsample

theorem quantitativeInnerGamma_endpoint_lower
    {t : ℝ} (ht : 18 <= t) :
    canonicalInnerRatioEndpoint t * quantitativeInnerPole t
      <= quantitativeInnerGamma t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [quantitativeInnerPole_eq_two_integral ht0]
  unfold quantitativeInnerGamma
  let phi : ℝ → ℝ :=
    scaledUnitBump
      (quantitativeTaperInnerCenter t) (quantitativeTaperR t)
  have hpole :
      Integrable
        (fun u => phi u
          * quantitativePoleWeight t (quantitativeSampleRadius t) u) :=
    taper_integrable
      (scaledUnitBump_continuous (quantitativeTaperR_pos ht0).ne' _)
      (scaledUnitBump_hasCompactSupport (quantitativeTaperR_pos ht0))
      (by unfold quantitativePoleWeight; fun_prop)
  have hgamma :
      Integrable
        (fun u => phi u * quantitativeGammaWeight t u) := by
    have hc : Continuous (fun u => phi u * quantitativeGammaWeight t u) := by
      unfold phi quantitativeGammaWeight centeredRadiusWeight
      fun_prop
    exact hc.integrable_of_hasCompactSupport
      (scaledUnitBump_hasCompactSupport (quantitativeTaperR_pos ht0)).mul_left
  have hpoint : ∀ u,
      canonicalInnerRatioEndpoint t *
        (phi u * quantitativePoleWeight t (quantitativeSampleRadius t) u)
      <= phi u * quantitativeGammaWeight t u := by
    intro u
    by_cases hbu : phi u = 0
    · simp [hbu]
    · have hs := scaledUnitBump_support
          (quantitativeTaperR_pos ht0) hbu
      unfold phi quantitativeTaperInnerCenter quantitativeTaperR at hs
      rw [abs_lt] at hs
      have hlo : 3*Real.pi/(4*t) < u := by
        field_simp [ne_of_gt ht0] at hs ⊢
        nlinarith [Real.pi_pos]
      have hhi : u < 5*Real.pi/(4*t) := by
        field_simp [ne_of_gt ht0] at hs ⊢
        nlinarith [Real.pi_pos]
      have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hlo.le
      have hang0 : 0 <= (t/16)*u := by positivity
      have hang : (t/16)*u < Real.pi/2 := by
        have htu := mul_lt_mul_of_pos_left hhi ht0
        field_simp [ne_of_gt ht0] at htu
        nlinarith [Real.pi_pos]
      rw [quantitativeGammaWeight_eq_ratio_mul_poleWeight
        hu0 hang0 hang]
      have hratio :=
        inner_ratio_le_five_endpoint ht hlo.le hhi.le
      have hp :=
        innerPoleWeight_nonpos_on_closed_window ht hlo.le hhi.le
      have hb := scaledUnitBump_nonneg
        (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u
      have hmul :
          gammaToPoleRatio t u
            * quantitativePoleWeight t (quantitativeSampleRadius t) u
          >=
          canonicalInnerRatioEndpoint t
            * quantitativePoleWeight t (quantitativeSampleRadius t) u :=
        mul_le_mul_of_nonpos_right hratio hp
      nlinarith
  have hi :=
    integral_mono
      (hpole.const_mul (canonicalInnerRatioEndpoint t))
      hgamma hpoint
  rw [integral_const_mul] at hi
  nlinarith

theorem quantitativeOuterGamma_endpoint_lower
    {t : ℝ} (ht : 18 <= t) :
    canonicalOuterRatioEndpoint t * quantitativeOuterPole t
      <= quantitativeOuterGamma t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  rw [quantitativeOuterPole_eq_two_integral ht0]
  unfold quantitativeOuterGamma
  let phi : ℝ → ℝ :=
    scaledUnitBump
      (quantitativeTaperOuterCenter t) (quantitativeTaperR t)
  have hpole :
      Integrable
        (fun u => phi u
          * quantitativePoleWeight t (quantitativeSampleRadius t) u) :=
    taper_integrable
      (scaledUnitBump_continuous (quantitativeTaperR_pos ht0).ne' _)
      (scaledUnitBump_hasCompactSupport (quantitativeTaperR_pos ht0))
      (by unfold quantitativePoleWeight; fun_prop)
  have hgamma :
      Integrable
        (fun u => phi u * quantitativeGammaWeight t u) := by
    have hc : Continuous (fun u => phi u * quantitativeGammaWeight t u) := by
      unfold phi quantitativeGammaWeight centeredRadiusWeight
      fun_prop
    exact hc.integrable_of_hasCompactSupport
      (scaledUnitBump_hasCompactSupport (quantitativeTaperR_pos ht0)).mul_left
  have hpoint : ∀ u,
      canonicalOuterRatioEndpoint t *
        (phi u * quantitativePoleWeight t (quantitativeSampleRadius t) u)
      <= phi u * quantitativeGammaWeight t u := by
    intro u
    by_cases hbu : phi u = 0
    · simp [hbu]
    · have hs := scaledUnitBump_support
          (quantitativeTaperR_pos ht0) hbu
      unfold phi quantitativeTaperOuterCenter quantitativeTaperR at hs
      rw [abs_lt] at hs
      have hlo : 7*Real.pi/(4*t) < u := by
        field_simp [ne_of_gt ht0] at hs ⊢
        nlinarith [Real.pi_pos]
      have hhi : u < 9*Real.pi/(4*t) := by
        field_simp [ne_of_gt ht0] at hs ⊢
        nlinarith [Real.pi_pos]
      have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hlo.le
      have hang0 : 0 <= (t/16)*u := by positivity
      have hang : (t/16)*u < Real.pi/2 := by
        have htu := mul_lt_mul_of_pos_left hhi ht0
        field_simp [ne_of_gt ht0] at htu
        nlinarith [Real.pi_pos]
      rw [quantitativeGammaWeight_eq_ratio_mul_poleWeight
        hu0 hang0 hang]
      have hratio :=
        seven_endpoint_le_outer_ratio ht hlo.le hhi.le
      have hp :=
        outerPoleWeight_nonneg_on_closed_window ht hlo.le hhi.le
      have hb := scaledUnitBump_nonneg
        (quantitativeTaperOuterCenter t) (quantitativeTaperR t) u
      have hmul :
          canonicalOuterRatioEndpoint t
            * quantitativePoleWeight t (quantitativeSampleRadius t) u
          <=
          gammaToPoleRatio t u
            * quantitativePoleWeight t (quantitativeSampleRadius t) u :=
        mul_le_mul_of_nonneg_right hratio hp
      nlinarith
  have hi :=
    integral_mono
      (hpole.const_mul (canonicalOuterRatioEndpoint t))
      hgamma hpoint
  rw [integral_const_mul] at hi
  nlinarith

theorem gammaResp_centered_canonical_eq_inner_outer
    {t : ℝ} (ht : 18 <= t) :
    gammaResp
      (gammaCenteredTaper
        (quantitativeCanonicalTaper t) (quantitativeSampleRadius t))
      t 0
      =
    quantitativeInnerGamma t
      + quantitativeLambda t * quantitativeOuterGamma t := by
  have hC2 := quantitativeCanonicalTaper_contDiff ht
  have hcompact := quantitativeCanonicalTaper_compact ht
  have hkernel :=
    gammaResp_centered_archKernel_exact_compact
      hC2 hcompact (quantitativeCanonicalTaper_even (t:=t))
      (quantitativeSampleRadius t) t
  rw [hkernel]
  have hi :=
    gammaResp_centered_inner_eq_quantitativeInnerGamma ht
  have ho :=
    gammaResp_centered_outer_eq_quantitativeOuterGamma ht
  rw [← hi, ← ho]
  have hki :=
    gammaResp_centered_archKernel_exact_compact
      (quantitativeInnerBump_contDiff
        (lt_of_lt_of_le (by norm_num) ht))
      (quantitativeInnerBump_compact
        (lt_of_lt_of_le (by norm_num) ht))
      (quantitativeInnerBump_even t)
      (quantitativeSampleRadius t) t
  have hko :=
    gammaResp_centered_archKernel_exact_compact
      (quantitativeOuterBump_contDiff
        (lt_of_lt_of_le (by norm_num) ht))
      (quantitativeOuterBump_compact
        (lt_of_lt_of_le (by norm_num) ht))
      (quantitativeOuterBump_even t)
      (quantitativeSampleRadius t) t
  rw [hki, hko]
  unfold quantitativeCanonicalTaper gammaCenteredTaper
  have hiInt : Integrable
      (fun u =>
        quantitativeInnerBump t u
          * (Real.cos (quantitativeSampleRadius t*u)-1)
          * Real.cos (t*u) * gammaArchKernel |u|) := by
    exact
      (gammaCenteredTaper_contDiff
        (quantitativeInnerBump_contDiff
          (lt_of_lt_of_le (by norm_num) ht))
        (quantitativeSampleRadius t)).continuous.integrable_of_hasCompactSupport
        (gammaCenteredTaper_hasCompactSupport
          (quantitativeInnerBump_compact
            (lt_of_lt_of_le (by norm_num) ht))
          (quantitativeSampleRadius t))
      |>.mul (by fun_prop)
  have hoInt : Integrable
      (fun u =>
        quantitativeOuterBump t u
          * (Real.cos (quantitativeSampleRadius t*u)-1)
          * Real.cos (t*u) * gammaArchKernel |u|) := by
    exact
      (gammaCenteredTaper_contDiff
        (quantitativeOuterBump_contDiff
          (lt_of_lt_of_le (by norm_num) ht))
        (quantitativeSampleRadius t)).continuous.integrable_of_hasCompactSupport
        (gammaCenteredTaper_hasCompactSupport
          (quantitativeOuterBump_compact
            (lt_of_lt_of_le (by norm_num) ht))
          (quantitativeSampleRadius t))
      |>.mul (by fun_prop)
  rw [show
      (fun u : ℝ =>
        (quantitativeInnerBump t u
          + quantitativeLambda t * quantitativeOuterBump t u)
          * (Real.cos (quantitativeSampleRadius t*u)-1)
          * Real.cos (t*u) * gammaArchKernel |u|)
      =
      fun u =>
        quantitativeInnerBump t u
          * (Real.cos (quantitativeSampleRadius t*u)-1)
          * Real.cos (t*u) * gammaArchKernel |u|
        + quantitativeLambda t *
          (quantitativeOuterBump t u
            * (Real.cos (quantitativeSampleRadius t*u)-1)
            * Real.cos (t*u) * gammaArchKernel |u|) by
      funext u; ring]
  rw [integral_add hiInt (hoInt.const_mul _), integral_const_mul]
  ring

theorem quantitativeCanonicalGammaCone_deficit
    {t : ℝ} (ht : 18 <= t) :
    evenConeFunctional
      (gammaVec
        (sampleFam
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0))
      <=
    -2 * ((-quantitativeInnerPole t)
      * canonicalGammaRatioGap t) := by
  have hPin := quantitativeInnerPole_neg ht
  have hPout := quantitativeOuterPole_pos ht
  have hcancel :
      quantitativeInnerPole t
        + quantitativeLambda t * quantitativeOuterPole t = 0 := by
    unfold quantitativeLambda
    field_simp [ne_of_gt hPout]
    ring
  have hGin := quantitativeInnerGamma_endpoint_lower ht
  have hGout := quantitativeOuterGamma_endpoint_lower ht
  have hresp :=
    gammaResp_centered_canonical_eq_inner_outer ht
  have hC2 :=
    gammaCenteredTaper_contDiff
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeSampleRadius t)
  have hcompact :=
    gammaCenteredTaper_hasCompactSupport
      (quantitativeCanonicalTaper_compact ht)
      (quantitativeSampleRadius t)
  have heven : ∀ u,
      gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) (-u)
      =
      gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) u := by
    intro u
    unfold gammaCenteredTaper
    rw [quantitativeCanonicalTaper_even]
    simp [Real.cos_neg]
  have hcone :=
    gammaConeValue_exact
      hC2.continuous hcompact heven t 0
  rw [hcone]
  simp only [neg_zero]
  rw [hresp]
  exact canonicalIntegratedGammaConeUpper
    hPin hPout hcancel hGin hGout rfl

theorem quantitativeCanonicalGammaCone_neg
    {t : ℝ} (ht : 18 <= t) :
    evenConeFunctional
      (gammaVec
        (sampleFam
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          t 0))
      < 0 := by
  have h := quantitativeCanonicalGammaCone_deficit ht
  have hmass : 0 < -quantitativeInnerPole t := by
    linarith [quantitativeInnerPole_neg ht]
  have hgap := canonicalGammaRatioGap_pos ht
  nlinarith [mul_pos hmass hgap]

end Synthesis
