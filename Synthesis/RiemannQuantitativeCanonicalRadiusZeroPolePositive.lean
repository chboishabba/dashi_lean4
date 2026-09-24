import Synthesis.RiemannCanonicalCenteredClusterPoleReduction
import Synthesis.RiemannPoleWindowIntegralDeweighting

/-!
# Positive radius-zero pole for the quantitative canonical taper

The quantitative canonical taper is

  g_t = inner_t + lambda_t outer_t,

where lambda_t is chosen so that the pole response weighted by
cos((t/16)u) vanishes.

The already-proved pole-window de-weighting theorem says that this weighted
cancellation leaves a positive *unweighted* residue, because the positive outer
window is attenuated more strongly by the sample cosine than the negative inner
window.

This file specializes that abstract theorem to the literal quantitative bumps
and proves

  0 < poleEvenResp (quantitativeCanonicalTaper t) t 0

for every t>=18.

Combined with the canonical centered cluster/pole reduction, the remaining
high sign is therefore a comparison against a genuinely positive, same-object
pole quantity.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance

def quantitativeOuterPoleBaseWeight (t u : ℝ) : ℝ :=
  scaledUnitBump
      (quantitativeTaperOuterCenter t)
      (quantitativeTaperR t) u
    * (Real.cosh (u / 2) * Real.cos (t * u))

def quantitativeInnerPoleBaseWeight (t u : ℝ) : ℝ :=
  scaledUnitBump
      (quantitativeTaperInnerCenter t)
      (quantitativeTaperR t) u
    * (Real.cosh (u / 2) * Real.cos (t * u))

theorem quantitativeOuterPoleBaseWeight_integrable
    {t : ℝ} (ht : 18 <= t) :
    Integrable (quantitativeOuterPoleBaseWeight t) := by
  have ht0 : 0 < t := by linarith
  unfold quantitativeOuterPoleBaseWeight
  exact
    ((scaledUnitBump_continuous
      (quantitativeTaperR_pos ht0).ne' _).mul (by fun_prop))
      .integrable_of_hasCompactSupport
        (scaledUnitBump_hasCompactSupport
          (quantitativeTaperR_pos ht0)).mul_right

theorem quantitativeInnerPoleBaseWeight_integrable
    {t : ℝ} (ht : 18 <= t) :
    Integrable (quantitativeInnerPoleBaseWeight t) := by
  have ht0 : 0 < t := by linarith
  unfold quantitativeInnerPoleBaseWeight
  exact
    ((scaledUnitBump_continuous
      (quantitativeTaperR_pos ht0).ne' _).mul (by fun_prop))
      .integrable_of_hasCompactSupport
        (scaledUnitBump_hasCompactSupport
          (quantitativeTaperR_pos ht0)).mul_right

theorem quantitativeOuterPoleBaseWeight_nonneg
    {t : ℝ} (ht : 18 <= t) :
    ∀ u, 0 <= quantitativeOuterPoleBaseWeight t u := by
  intro u
  unfold quantitativeOuterPoleBaseWeight
  by_cases hb :
      scaledUnitBump
        (quantitativeTaperOuterCenter t)
        (quantitativeTaperR t) u = 0
  · simp [hb]
  · have ht0 : 0 < t := by linarith
    have hs :=
      scaledUnitBump_support (quantitativeTaperR_pos ht0) hb
    unfold quantitativeTaperOuterCenter quantitativeTaperR at hs
    rw [abs_lt] at hs
    have hlo : 7 * Real.pi / (4 * t) < u := by
      field_simp [ne_of_gt ht0] at hs ⊢
      nlinarith [Real.pi_pos]
    have hhi : u < 9 * Real.pi / (4 * t) := by
      field_simp [ne_of_gt ht0] at hs ⊢
      nlinarith [Real.pi_pos]
    have htuL : 7 * Real.pi / 4 < t * u := by
      have h := mul_lt_mul_of_pos_left hlo ht0
      field_simp [ne_of_gt ht0] at h
      exact h
    have htuH : t * u < 9 * Real.pi / 4 := by
      have h := mul_lt_mul_of_pos_left hhi ht0
      field_simp [ne_of_gt ht0] at h
      exact h
    have hcos : 0 < Real.cos (t * u) := by
      have hmem :
          -(Real.pi / 2) < t * u - 2 * Real.pi
            ∧ t * u - 2 * Real.pi < Real.pi / 2 := by
        constructor <;> linarith
      have hc := Real.cos_pos_of_mem_Ioo hmem
      simpa [Real.cos_sub_int_mul_two_pi] using hc
    positivity

theorem quantitativeInnerPoleBaseWeight_nonpos
    {t : ℝ} (ht : 18 <= t) :
    ∀ u, quantitativeInnerPoleBaseWeight t u <= 0 := by
  intro u
  unfold quantitativeInnerPoleBaseWeight
  by_cases hb :
      scaledUnitBump
        (quantitativeTaperInnerCenter t)
        (quantitativeTaperR t) u = 0
  · simp [hb]
  · have ht0 : 0 < t := by linarith
    have hs :=
      scaledUnitBump_support (quantitativeTaperR_pos ht0) hb
    unfold quantitativeTaperInnerCenter quantitativeTaperR at hs
    rw [abs_lt] at hs
    have hlo : 3 * Real.pi / (4 * t) < u := by
      field_simp [ne_of_gt ht0] at hs ⊢
      nlinarith [Real.pi_pos]
    have hhi : u < 5 * Real.pi / (4 * t) := by
      field_simp [ne_of_gt ht0] at hs ⊢
      nlinarith [Real.pi_pos]
    have htuL : 3 * Real.pi / 4 < t * u := by
      have h := mul_lt_mul_of_pos_left hlo ht0
      field_simp [ne_of_gt ht0] at h
      exact h
    have htuH : t * u < 5 * Real.pi / 4 := by
      have h := mul_lt_mul_of_pos_left hhi ht0
      field_simp [ne_of_gt ht0] at h
      exact h
    have hcos : Real.cos (t * u) < 0 := by
      have hmem :
          -(Real.pi / 2) < t * u - Real.pi
            ∧ t * u - Real.pi < Real.pi / 2 := by
        constructor <;> linarith
      have hc := Real.cos_pos_of_mem_Ioo hmem
      rw [Real.cos_sub_pi] at hc
      linarith
    have hbnn :=
      scaledUnitBump_nonneg
        (quantitativeTaperInnerCenter t)
        (quantitativeTaperR t) u
    have hch := Real.cosh_pos (u / 2)
    nlinarith [mul_pos hch (-hcos)]

theorem quantitativeOuterPoleBaseWeight_support
    {t : ℝ} (ht : 18 <= t) :
    ∀ u, quantitativeOuterPoleBaseWeight t u != 0 ->
      7 * Real.pi / (4 * t) < u
        ∧ u < 9 * Real.pi / (4 * t) := by
  intro u hu
  have hb :
      scaledUnitBump
        (quantitativeTaperOuterCenter t)
        (quantitativeTaperR t) u != 0 := by
    intro h
    apply hu
    simp [quantitativeOuterPoleBaseWeight, h]
  have ht0 : 0 < t := by linarith
  have hs :=
    scaledUnitBump_support (quantitativeTaperR_pos ht0) hb
  unfold quantitativeTaperOuterCenter quantitativeTaperR at hs
  rw [abs_lt] at hs
  constructor <;>
    field_simp [ne_of_gt ht0] at hs ⊢ <;>
    nlinarith [Real.pi_pos]

theorem quantitativeInnerPoleBaseWeight_support
    {t : ℝ} (ht : 18 <= t) :
    ∀ u, quantitativeInnerPoleBaseWeight t u != 0 ->
      3 * Real.pi / (4 * t) < u
        ∧ u < 5 * Real.pi / (4 * t) := by
  intro u hu
  have hb :
      scaledUnitBump
        (quantitativeTaperInnerCenter t)
        (quantitativeTaperR t) u != 0 := by
    intro h
    apply hu
    simp [quantitativeInnerPoleBaseWeight, h]
  have ht0 : 0 < t := by linarith
  have hs :=
    scaledUnitBump_support (quantitativeTaperR_pos ht0) hb
  unfold quantitativeTaperInnerCenter quantitativeTaperR at hs
  rw [abs_lt] at hs
  constructor <;>
    field_simp [ne_of_gt ht0] at hs ⊢ <;>
    nlinarith [Real.pi_pos]

theorem quantitativeOuterPoleBaseWeight_integral_pos
    {t : ℝ} (ht : 18 <= t) :
    0 < ∫ u : ℝ, quantitativeOuterPoleBaseWeight t u := by
  have ht0 : 0 < t := by linarith
  apply scaledUnitBump_positive_integral
    (quantitativeTaperR_pos ht0)
  · fun_prop
  · intro u hu
    unfold quantitativeTaperOuterCenter quantitativeTaperR at hu
    rw [abs_lt] at hu
    have hlo : 7 * Real.pi / (4 * t) < u := by
      field_simp [ne_of_gt ht0] at hu ⊢
      nlinarith [Real.pi_pos]
    have hhi : u < 9 * Real.pi / (4 * t) := by
      field_simp [ne_of_gt ht0] at hu ⊢
      nlinarith [Real.pi_pos]
    have htuL : 7 * Real.pi / 4 < t * u := by
      have h := mul_lt_mul_of_pos_left hlo ht0
      field_simp [ne_of_gt ht0] at h
      exact h
    have htuH : t * u < 9 * Real.pi / 4 := by
      have h := mul_lt_mul_of_pos_left hhi ht0
      field_simp [ne_of_gt ht0] at h
      exact h
    have hx :
        -(Real.pi / 2) < t * u - 2 * Real.pi
          ∧ t * u - 2 * Real.pi < Real.pi / 2 := by
      constructor <;> linarith
    have hc := Real.cos_pos_of_mem_Ioo hx
    have hc' : 0 < Real.cos (t * u) := by
      simpa [Real.cos_sub_int_mul_two_pi] using hc
    exact mul_pos (Real.cosh_pos _) hc'

theorem quantitativeInnerPoleBaseWeight_integral_neg
    {t : ℝ} (ht : 18 <= t) :
    (∫ u : ℝ, quantitativeInnerPoleBaseWeight t u) < 0 := by
  have ht0 : 0 < t := by linarith
  have hpos :
      0 < ∫ u : ℝ,
        scaledUnitBump
          (quantitativeTaperInnerCenter t)
          (quantitativeTaperR t) u
        * (-(Real.cosh (u/2) * Real.cos (t*u))) := by
    apply scaledUnitBump_positive_integral
      (quantitativeTaperR_pos ht0)
    · fun_prop
    · intro u hu
      have hs := scaledUnitBump_support
        (quantitativeTaperR_pos ht0) hu
      unfold quantitativeTaperInnerCenter quantitativeTaperR at hs
      rw [abs_lt] at hs
      have htuL : 3*Real.pi/4 < t*u := by
        field_simp [ne_of_gt ht0] at hs
        nlinarith [Real.pi_pos]
      have htuH : t*u < 5*Real.pi/4 := by
        field_simp [ne_of_gt ht0] at hs
        nlinarith [Real.pi_pos]
      have hx : -(Real.pi/2) < t*u-Real.pi
          ∧ t*u-Real.pi < Real.pi/2 := by
        constructor <;> linarith
      have hh := Real.cos_pos_of_mem_Ioo hx
      rw [Real.cos_sub_pi] at hh
      have hch := Real.cosh_pos (u/2)
      nlinarith [mul_pos hch (-Real.cos (t*u))]
  have heq :
      (fun u : ℝ =>
        scaledUnitBump
          (quantitativeTaperInnerCenter t)
          (quantitativeTaperR t) u
        * (-(Real.cosh (u/2) * Real.cos (t*u))))
      =
      fun u : ℝ => - quantitativeInnerPoleBaseWeight t u := by
    funext u
    unfold quantitativeInnerPoleBaseWeight
    ring
  rw [heq, integral_neg] at hpos
  linarith

theorem quantitativeOuterPole_weighted_eq_half
    {t : ℝ} (ht : 18 <= t) :
    (∫ u : ℝ,
      quantitativeOuterPoleBaseWeight t u
        * Real.cos ((t / 16) * u))
      =
    quantitativeOuterPole t / 2 := by
  have ht0 : 0 < t := by linarith
  rw [quantitativeOuterPole_eq_two_integral ht0]
  unfold quantitativeOuterPoleBaseWeight quantitativePoleWeight
    quantitativeSampleRadius
  ring_nf

theorem quantitativeInnerPole_weighted_eq_half
    {t : ℝ} (ht : 18 <= t) :
    (∫ u : ℝ,
      quantitativeInnerPoleBaseWeight t u
        * Real.cos ((t / 16) * u))
      =
    quantitativeInnerPole t / 2 := by
  have ht0 : 0 < t := by linarith
  rw [quantitativeInnerPole_eq_two_integral ht0]
  unfold quantitativeInnerPoleBaseWeight quantitativePoleWeight
    quantitativeSampleRadius
  ring_nf

theorem quantitativeInnerPole_radiusZero_eq_two_base
    {t : ℝ} (ht : 18 <= t) :
    poleEvenResp (quantitativeInnerBump t) t 0
      =
    2 * ∫ u : ℝ, quantitativeInnerPoleBaseWeight t u := by
  have ht0 : 0 < t := by linarith
  unfold quantitativeInnerBump quantitativeSymBump
  rw [poleEvenResp]
  simp only [Real.cos_zero, mul_one]
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
            Real.cosh (u / 2) * Real.cos (t * u)))
      (by
        intro u
        simp [Real.cosh_neg, Real.cos_neg])
  unfold Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
    quantitativeInnerPoleBaseWeight
  simpa [mul_assoc] using hs

theorem quantitativeOuterPole_radiusZero_eq_two_base
    {t : ℝ} (ht : 18 <= t) :
    poleEvenResp (quantitativeOuterBump t) t 0
      =
    2 * ∫ u : ℝ, quantitativeOuterPoleBaseWeight t u := by
  have ht0 : 0 < t := by linarith
  unfold quantitativeOuterBump quantitativeSymBump
  rw [poleEvenResp]
  simp only [Real.cos_zero, mul_one]
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
            Real.cosh (u / 2) * Real.cos (t * u)))
      (by
        intro u
        simp [Real.cosh_neg, Real.cos_neg])
  unfold Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
    quantitativeOuterPoleBaseWeight
  simpa [mul_assoc] using hs

theorem quantitativeCanonicalTaper_radiusZero_pole_pos
    {t : ℝ} (ht : 18 <= t) :
    0 < poleEvenResp (quantitativeCanonicalTaper t) t 0 := by
  have ht0 : 0 < t := by linarith
  let F1 := quantitativeOuterPoleBaseWeight t
  let F2 := quantitativeInnerPoleBaseWeight t
  have hF1 := quantitativeOuterPoleBaseWeight_integrable ht
  have hF2 := quantitativeInnerPoleBaseWeight_integrable ht
  have hA1 := quantitativeOuterPoleBaseWeight_integral_pos ht
  have hA2 := quantitativeInnerPoleBaseWeight_integral_neg ht
  have hP1 : 0 < ∫ u : ℝ, F1 u * Real.cos ((t/16)*u) := by
    dsimp [F1]
    rw [quantitativeOuterPole_weighted_eq_half ht]
    linarith [quantitativeOuterPole_pos ht]
  have hP2 : (∫ u : ℝ, F2 u * Real.cos ((t/16)*u)) < 0 := by
    dsimp [F2]
    rw [quantitativeInnerPole_weighted_eq_half ht]
    linarith [quantitativeInnerPole_neg ht]
  have hlam :
      quantitativeLambda t
        =
      -(∫ u : ℝ, F2 u * Real.cos ((t/16)*u))
        /
      (∫ u : ℝ, F1 u * Real.cos ((t/16)*u)) := by
    dsimp [F1, F2]
    rw [quantitativeOuterPole_weighted_eq_half ht,
        quantitativeInnerPole_weighted_eq_half ht]
    unfold quantitativeLambda
    field_simp [ne_of_gt (quantitativeOuterPole_pos ht)]
    ring
  have hres :=
    two_window_integral_cancellation_leaves_positive_residue
      ht0 hF1 hF2
      (quantitativeOuterPoleBaseWeight_nonneg ht)
      (quantitativeInnerPoleBaseWeight_nonpos ht)
      (quantitativeOuterPoleBaseWeight_support ht)
      (quantitativeInnerPoleBaseWeight_support ht)
      hA1 hA2 hP1 hP2 hlam
  have hlin :=
    poleEvenResp_add_smul
      (quantitativeInnerBump_continuous ht0)
      (quantitativeInnerBump_compact ht0)
      (quantitativeOuterBump_continuous ht0)
      (quantitativeOuterBump_compact ht0)
      (t := t) (s := 0) (lam := quantitativeLambda t)
  have hi := quantitativeInnerPole_radiusZero_eq_two_base ht
  have ho := quantitativeOuterPole_radiusZero_eq_two_base ht
  unfold quantitativeCanonicalTaper
  rw [hlin, hi, ho]
  dsimp [F1, F2] at hres
  nlinarith

end Synthesis
