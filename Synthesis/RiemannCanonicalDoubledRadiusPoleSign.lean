import Synthesis.RiemannQuantitativeCanonicalRadiusZeroPolePositive
import Synthesis.RiemannCanonicalGateData
import Zeta23Bridge.LiteralWeilPoleProjectiveCancellation

/-!
# Sign of the canonical pole channel at the doubled projective radius

The canonical taper kills the pole response at

  r = t/16.

The projective pole defect therefore has sign determined by the doubled-radius
response P_t(2r).  This file proves the relevant direction.

On the positive-coordinate inner/outer windows write x=(t/16)u.  Passing from
r to 2r multiplies the selected-radius pole density by

  h(x) = cos(2x)/cos(x).

On 0<x<pi/2 this ratio is strictly decreasing.  The canonical inner window has

  3*pi/64 < x < 5*pi/64,

while the outer window has

  7*pi/64 < x < 9*pi/64.

Thus, with c=h(3*pi/32), the inner negative selected-radius density is
multiplied by at least c and the outer positive density by at most c.
Since the selected-radius inner+lambda*outer integral is exactly zero, the
doubled-radius sum is nonpositive.

Consequently

  P_t(2r) <= 0

and, because A_0(r)>0 on GateData,

  0 <= D_pole^proj.

So the canonical projective pole term is not a hidden negative margin that can
absorb a target-independent N-mu discrepancy.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilPoleProjectiveCancellation
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

def doubleSampleAttenuation (x : ℝ) : ℝ :=
  Real.cos (2*x) / Real.cos x

theorem doubleSampleAttenuation_eq
    {x : ℝ} (hc : Real.cos x ≠ 0) :
    doubleSampleAttenuation x
      = 2 * Real.cos x - 1 / Real.cos x := by
  unfold doubleSampleAttenuation
  rw [Real.cos_two_mul]
  field_simp [hc]
  ring

theorem doubleSampleAttenuation_strictAnti
    {x y : ℝ}
    (hx0 : 0 ≤ x)
    (hxy : x < y)
    (hy : y < Real.pi / 2) :
    doubleSampleAttenuation y < doubleSampleAttenuation x := by
  have hxpi : x < Real.pi / 2 := lt_trans hxy hy
  have hcx : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hcy : 0 < Real.cos y := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hcos : Real.cos y < Real.cos x := by
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      hx0 (by linarith [Real.pi_pos]) hxy
  have hinv : 1 / Real.cos x < 1 / Real.cos y := by
    exact (div_lt_div_iff₀ hcx hcy).2 (by simpa using hcos)
  rw [doubleSampleAttenuation_eq hcy.ne',
      doubleSampleAttenuation_eq hcx.ne']
  linarith

def doubledPoleRatioSeparator : ℝ :=
  doubleSampleAttenuation (3 * Real.pi / 32)

theorem inner_doubleSampleAttenuation_ge_separator
    {t u : ℝ} (ht : 0 < t)
    (hlo : 3 * Real.pi / (4*t) < u)
    (hhi : u < 5 * Real.pi / (4*t)) :
    doubledPoleRatioSeparator
      ≤ doubleSampleAttenuation ((t/16)*u) := by
  have hx0 : 0 ≤ (t/16)*u := by
    have hu0 : 0 < u := lt_trans (by positivity) hlo
    positivity
  have hxhi : (t/16)*u < 5 * Real.pi / 64 := by
    have h := mul_lt_mul_of_pos_left hhi (show 0 < t/16 by positivity)
    field_simp [ne_of_gt ht] at h
    nlinarith [Real.pi_pos]
  have hmid : (t/16)*u < 3 * Real.pi / 32 := by
    nlinarith [Real.pi_pos]
  have hmidpi : 3 * Real.pi / 32 < Real.pi/2 := by
    nlinarith [Real.pi_pos]
  exact (doubleSampleAttenuation_strictAnti hx0 hmid hmidpi).le

theorem outer_doubleSampleAttenuation_le_separator
    {t u : ℝ} (ht : 0 < t)
    (hlo : 7 * Real.pi / (4*t) < u)
    (hhi : u < 9 * Real.pi / (4*t)) :
    doubleSampleAttenuation ((t/16)*u)
      ≤ doubledPoleRatioSeparator := by
  have hmid0 : 0 ≤ 3 * Real.pi / 32 := by positivity
  have hxlo : 7 * Real.pi / 64 < (t/16)*u := by
    have h := mul_lt_mul_of_pos_left hlo (show 0 < t/16 by positivity)
    field_simp [ne_of_gt ht] at h
    nlinarith [Real.pi_pos]
  have hmid : 3 * Real.pi / 32 < (t/16)*u := by
    nlinarith [Real.pi_pos]
  have hxhi : (t/16)*u < 9 * Real.pi / 64 := by
    have h := mul_lt_mul_of_pos_left hhi (show 0 < t/16 by positivity)
    field_simp [ne_of_gt ht] at h
    nlinarith [Real.pi_pos]
  have hxpi : (t/16)*u < Real.pi/2 := by
    nlinarith [Real.pi_pos]
  exact (doubleSampleAttenuation_strictAnti hmid0 hmid hxpi).le

def quantitativeOuterSelectedPoleDensity (t u : ℝ) : ℝ :=
  quantitativeOuterPoleBaseWeight t u
    * Real.cos ((t/16)*u)

def quantitativeInnerSelectedPoleDensity (t u : ℝ) : ℝ :=
  quantitativeInnerPoleBaseWeight t u
    * Real.cos ((t/16)*u)

def quantitativeOuterDoubledPoleDensity (t u : ℝ) : ℝ :=
  quantitativeOuterPoleBaseWeight t u
    * Real.cos ((t/8)*u)

def quantitativeInnerDoubledPoleDensity (t u : ℝ) : ℝ :=
  quantitativeInnerPoleBaseWeight t u
    * Real.cos ((t/8)*u)

theorem outerSelectedPoleDensity_nonneg
    {t : ℝ} (ht : 18 ≤ t) :
    ∀ u, 0 ≤ quantitativeOuterSelectedPoleDensity t u := by
  intro u
  unfold quantitativeOuterSelectedPoleDensity
  by_cases hF : quantitativeOuterPoleBaseWeight t u = 0
  · simp [hF]
  · have hs := quantitativeOuterPoleBaseWeight_support ht u hF
    have ht0 : 0 < t := by linarith
    have hangle0 : 0 < (t/16)*u := by
      have hu0 : 0 < u := lt_trans (by positivity) hs.1
      positivity
    have hanglepi : (t/16)*u < Real.pi/2 := by
      have h := mul_lt_mul_of_pos_left hs.2 (show 0 < t/16 by positivity)
      field_simp [ne_of_gt ht0] at h
      nlinarith [Real.pi_pos]
    have hc : 0 < Real.cos ((t/16)*u) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith
    exact mul_nonneg
      (quantitativeOuterPoleBaseWeight_nonneg ht u)
      hc.le

theorem innerSelectedPoleDensity_nonpos
    {t : ℝ} (ht : 18 ≤ t) :
    ∀ u, quantitativeInnerSelectedPoleDensity t u ≤ 0 := by
  intro u
  unfold quantitativeInnerSelectedPoleDensity
  by_cases hF : quantitativeInnerPoleBaseWeight t u = 0
  · simp [hF]
  · have hs := quantitativeInnerPoleBaseWeight_support ht u hF
    have ht0 : 0 < t := by linarith
    have hangle0 : 0 < (t/16)*u := by
      have hu0 : 0 < u := lt_trans (by positivity) hs.1
      positivity
    have hanglepi : (t/16)*u < Real.pi/2 := by
      have h := mul_lt_mul_of_pos_left hs.2 (show 0 < t/16 by positivity)
      field_simp [ne_of_gt ht0] at h
      nlinarith [Real.pi_pos]
    have hc : 0 < Real.cos ((t/16)*u) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (quantitativeInnerPoleBaseWeight_nonpos ht u) hc.le

theorem doubledPoleDensity_eq_selected_mul_attenuation
    {F : ℝ → ℝ} {t u : ℝ}
    (ht : 0 < t)
    (hsupp : F u ≠ 0 ->
      0 < u ∧ u < 9 * Real.pi / (4*t)) :
    F u * Real.cos ((t/8)*u)
      =
    (F u * Real.cos ((t/16)*u))
      * doubleSampleAttenuation ((t/16)*u) := by
  by_cases hF : F u = 0
  · simp [hF]
  · have hu := hsupp hF
    have hx0 : 0 < (t/16)*u := by positivity
    have hxpi : (t/16)*u < Real.pi/2 := by
      have h := mul_lt_mul_of_pos_left hu.2 (show 0 < t/16 by positivity)
      field_simp [ne_of_gt ht] at h
      nlinarith [Real.pi_pos]
    have hc : Real.cos ((t/16)*u) ≠ 0 := by
      exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, hxpi⟩).ne'
    unfold doubleSampleAttenuation
    have h2 : (t/8)*u = 2 * ((t/16)*u) := by ring
    rw [h2]
    field_simp [hc]
    ring

theorem outerDoubledPoleIntegral_le_separator
    {t : ℝ} (ht : 18 ≤ t) :
    (∫ u : ℝ, quantitativeOuterDoubledPoleDensity t u)
      ≤
    doubledPoleRatioSeparator
      * ∫ u : ℝ, quantitativeOuterSelectedPoleDensity t u := by
  have ht0 : 0 < t := by linarith
  have hsel : Integrable (quantitativeOuterSelectedPoleDensity t) := by
    unfold quantitativeOuterSelectedPoleDensity
    exact (quantitativeOuterPoleBaseWeight_integrable ht).mul
      (by fun_prop)
  have hdbl : Integrable (quantitativeOuterDoubledPoleDensity t) := by
    unfold quantitativeOuterDoubledPoleDensity
    exact (quantitativeOuterPoleBaseWeight_integrable ht).mul
      (by fun_prop)
  have hrhs : Integrable
      (fun u => doubledPoleRatioSeparator
        * quantitativeOuterSelectedPoleDensity t u) :=
    hsel.const_mul _
  calc
    (∫ u : ℝ, quantitativeOuterDoubledPoleDensity t u)
      ≤
    ∫ u : ℝ,
      doubledPoleRatioSeparator
        * quantitativeOuterSelectedPoleDensity t u := by
      apply integral_mono hdbl hrhs
      intro u
      by_cases hF : quantitativeOuterPoleBaseWeight t u = 0
      · simp [quantitativeOuterDoubledPoleDensity,
          quantitativeOuterSelectedPoleDensity, hF]
      · have hs := quantitativeOuterPoleBaseWeight_support ht u hF
        have heq :=
          doubledPoleDensity_eq_selected_mul_attenuation
            (F := quantitativeOuterPoleBaseWeight t)
            ht0
            (fun h => ⟨lt_trans (by positivity) (quantitativeOuterPoleBaseWeight_support ht u h).1,
              (quantitativeOuterPoleBaseWeight_support ht u h).2⟩)
        rw [quantitativeOuterDoubledPoleDensity,
          quantitativeOuterSelectedPoleDensity, heq]
        exact mul_le_mul_of_nonneg_right
          (outer_doubleSampleAttenuation_le_separator ht0 hs.1 hs.2)
          (outerSelectedPoleDensity_nonneg ht u)
    _ =
    doubledPoleRatioSeparator
      * ∫ u : ℝ, quantitativeOuterSelectedPoleDensity t u := by
      rw [integral_const_mul]

theorem innerDoubledPoleIntegral_le_separator
    {t : ℝ} (ht : 18 ≤ t) :
    (∫ u : ℝ, quantitativeInnerDoubledPoleDensity t u)
      ≤
    doubledPoleRatioSeparator
      * ∫ u : ℝ, quantitativeInnerSelectedPoleDensity t u := by
  have ht0 : 0 < t := by linarith
  have hsel : Integrable (quantitativeInnerSelectedPoleDensity t) := by
    unfold quantitativeInnerSelectedPoleDensity
    exact (quantitativeInnerPoleBaseWeight_integrable ht).mul
      (by fun_prop)
  have hdbl : Integrable (quantitativeInnerDoubledPoleDensity t) := by
    unfold quantitativeInnerDoubledPoleDensity
    exact (quantitativeInnerPoleBaseWeight_integrable ht).mul
      (by fun_prop)
  have hrhs : Integrable
      (fun u => doubledPoleRatioSeparator
        * quantitativeInnerSelectedPoleDensity t u) :=
    hsel.const_mul _
  calc
    (∫ u : ℝ, quantitativeInnerDoubledPoleDensity t u)
      ≤
    ∫ u : ℝ,
      doubledPoleRatioSeparator
        * quantitativeInnerSelectedPoleDensity t u := by
      apply integral_mono hdbl hrhs
      intro u
      by_cases hF : quantitativeInnerPoleBaseWeight t u = 0
      · simp [quantitativeInnerDoubledPoleDensity,
          quantitativeInnerSelectedPoleDensity, hF]
      · have hs := quantitativeInnerPoleBaseWeight_support ht u hF
        have heq :=
          doubledPoleDensity_eq_selected_mul_attenuation
            (F := quantitativeInnerPoleBaseWeight t)
            ht0
            (fun h => ⟨lt_trans (by positivity) (quantitativeInnerPoleBaseWeight_support ht u h).1,
              lt_trans (quantitativeInnerPoleBaseWeight_support ht u h).2
                (by positivity : 5 * Real.pi / (4*t) < 9 * Real.pi / (4*t))⟩)
        rw [quantitativeInnerDoubledPoleDensity,
          quantitativeInnerSelectedPoleDensity, heq]
        have hratio :=
          inner_doubleSampleAttenuation_ge_separator
            ht0 hs.1 hs.2
        exact mul_le_mul_of_nonpos_left hratio
          (innerSelectedPoleDensity_nonpos ht u)
    _ =
    doubledPoleRatioSeparator
      * ∫ u : ℝ, quantitativeInnerSelectedPoleDensity t u := by
      rw [integral_const_mul]

theorem canonical_selectedPoleIntegral_cancels
    {t : ℝ} (ht : 18 ≤ t) :
    (∫ u : ℝ, quantitativeInnerSelectedPoleDensity t u)
      +
    quantitativeLambda t
      * ∫ u : ℝ, quantitativeOuterSelectedPoleDensity t u
      = 0 := by
  rw [show
      (∫ u : ℝ, quantitativeInnerSelectedPoleDensity t u)
        = quantitativeInnerPole t / 2 by
      unfold quantitativeInnerSelectedPoleDensity
      exact quantitativeInnerPole_weighted_eq_half ht,
    show
      (∫ u : ℝ, quantitativeOuterSelectedPoleDensity t u)
        = quantitativeOuterPole t / 2 by
      unfold quantitativeOuterSelectedPoleDensity
      exact quantitativeOuterPole_weighted_eq_half ht]
  unfold quantitativeLambda
  field_simp [ne_of_gt (quantitativeOuterPole_pos ht)]
  ring

theorem quantitativeInnerPole_doubled_eq_two_integral
    {t : ℝ} (ht : 18 ≤ t) :
    poleEvenResp (quantitativeInnerBump t) t
      (2 * quantitativeSampleRadius t)
      =
    2 * ∫ u : ℝ, quantitativeInnerDoubledPoleDensity t u := by
  have ht0 : 0 < t := by linarith
  unfold quantitativeInnerDoubledPoleDensity
    quantitativeInnerPoleBaseWeight
  unfold quantitativeInnerBump quantitativeSymBump
  rw [poleEvenResp]
  have hs :=
    integral_symmetrize
      (scaledUnitBump_continuous
        (quantitativeTaperR_pos ht0).ne'
        (quantitativeTaperInnerCenter t))
      (scaledUnitBump_hasCompactSupport
        (quantitativeTaperR_pos ht0))
      (by fun_prop :
        Continuous
          (fun u : ℝ =>
            Real.cosh (u/2) * Real.cos (t*u)
              * Real.cos ((t/8)*u)))
      (by
        intro u
        simp [Real.cosh_neg, Real.cos_neg])
  have hr : 2 * quantitativeSampleRadius t = t/8 := by
    unfold quantitativeSampleRadius
    ring
  rw [hr]
  simpa [mul_assoc] using hs

theorem quantitativeOuterPole_doubled_eq_two_integral
    {t : ℝ} (ht : 18 ≤ t) :
    poleEvenResp (quantitativeOuterBump t) t
      (2 * quantitativeSampleRadius t)
      =
    2 * ∫ u : ℝ, quantitativeOuterDoubledPoleDensity t u := by
  have ht0 : 0 < t := by linarith
  unfold quantitativeOuterDoubledPoleDensity
    quantitativeOuterPoleBaseWeight
  unfold quantitativeOuterBump quantitativeSymBump
  rw [poleEvenResp]
  have hs :=
    integral_symmetrize
      (scaledUnitBump_continuous
        (quantitativeTaperR_pos ht0).ne'
        (quantitativeTaperOuterCenter t))
      (scaledUnitBump_hasCompactSupport
        (quantitativeTaperR_pos ht0))
      (by fun_prop :
        Continuous
          (fun u : ℝ =>
            Real.cosh (u/2) * Real.cos (t*u)
              * Real.cos ((t/8)*u)))
      (by
        intro u
        simp [Real.cosh_neg, Real.cos_neg])
  have hr : 2 * quantitativeSampleRadius t = t/8 := by
    unfold quantitativeSampleRadius
    ring
  rw [hr]
  simpa [mul_assoc] using hs

theorem quantitativeCanonicalTaper_doubled_pole_nonpos
    {t : ℝ} (ht : 18 ≤ t) :
    poleEvenResp (quantitativeCanonicalTaper t) t
      (2 * quantitativeSampleRadius t) ≤ 0 := by
  have ht0 : 0 < t := by linarith
  have hlin :=
    poleEvenResp_add_smul
      (quantitativeInnerBump_continuous ht0)
      (quantitativeInnerBump_compact ht0)
      (quantitativeOuterBump_continuous ht0)
      (quantitativeOuterBump_compact ht0)
      (t := t) (s := 2 * quantitativeSampleRadius t)
      (lam := quantitativeLambda t)
  unfold quantitativeCanonicalTaper
  rw [hlin,
      quantitativeInnerPole_doubled_eq_two_integral ht,
      quantitativeOuterPole_doubled_eq_two_integral ht]
  have hi := innerDoubledPoleIntegral_le_separator ht
  have ho := outerDoubledPoleIntegral_le_separator ht
  have hlam : 0 ≤ quantitativeLambda t :=
    (quantitativeLambda_pos ht).le
  have hcancel := canonical_selectedPoleIntegral_cancels ht
  nlinarith [mul_le_mul_of_nonneg_left ho hlam]

theorem gate_onLineRadiusResp_pos
    {g : ℝ → ℝ} {t r Λ : ℝ}
    (hd : GateData g t r Λ) :
    0 < evenResp g 0 r := by
  let F : ℝ → ℝ := fun u => g u * Real.cos (r*u)
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hFcpt : HasCompactSupport F := by
    dsimp [F]
    exact hd.compactSupport.mul_right
  have hFint : Integrable F :=
    hFcont.integrable_of_hasCompactSupport hFcpt
  have hFnn : ∀ u, 0 ≤ F u := by
    intro u
    by_cases hg0 : g u = 0
    · simp [F, hg0]
    · have hc :
          0 < Real.cos (r*u) := by
        exact Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.cos_pos_of_radial
          hd.radiusPos (hd.radial u hg0)
      exact mul_nonneg (hd.nonneg u) hc.le
  obtain ⟨u0, v0, hu0, hv0, huv⟩ := hd.twoPoint
  have hFu0 : 0 < F u0 := by
    have hc :
        0 < Real.cos (r*u0) :=
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.cos_pos_of_radial
        hd.radiusPos (hd.radial u0 (ne_of_gt hu0))
    exact mul_pos hu0 hc
  have hopen : IsOpen {u : ℝ | 0 < F u} :=
    isOpen_lt continuous_const hFcont
  have hmeas :
      0 < volume {u : ℝ | 0 < F u} :=
    hopen.measure_pos volume ⟨u0, hFu0⟩
  have hsub :
      {u : ℝ | 0 < F u} ⊆ Function.support F := by
    intro u hu
    exact ne_of_gt hu
  have hpos : 0 < ∫ u : ℝ, F u := by
    rw [integral_pos_iff_support_of_nonneg hFnn hFint]
    exact lt_of_lt_of_le hmeas (measure_mono hsub)
  unfold evenResp
  simp only [zero_mul, Real.cosh_zero, one_mul]
  simpa [F] using hpos

theorem quantitativeCanonical_projectivePoleDefect_nonneg
    {t : ℝ} (ht : 18 ≤ t) :
    0 ≤
    poleProjectiveDefect
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t) := by
  have hd :=
    quantitativeCanonicalGateData ht
  have hp2 := quantitativeCanonicalTaper_doubled_pole_nonpos ht
  have hp1 := quantitativeCanonicalTaper_pole_zero ht
  have hA :
      0 <
      evenResp (quantitativeCanonicalTaper t) 0
        (quantitativeSampleRadius t) :=
    gate_onLineRadiusResp_pos hd
  rw [poleProjectiveDefect_eq
    hd.smooth.continuous hd.compactSupport hd.isEven
    t (quantitativeSampleRadius t), hp1]
  nlinarith

end Synthesis
