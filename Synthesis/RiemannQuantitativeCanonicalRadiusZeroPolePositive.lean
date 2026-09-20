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
    have hs :=
      quantitativeOuterPoleBaseWeight_support ht
        (u := u) (by
          unfold quantitativeOuterPoleBaseWeight
          exact mul_ne_zero hu (by
            have hs0 := scaledUnitBump_support
              (quantitativeTaperR_pos ht0) hu
            unfold quantitativeTaperOuterCenter quantitativeTaperR at hs0
            rw [abs_lt] at hs0
            have hlo : 7 * Real.pi / (4 * t) < u := by
              field_simp [ne_of_gt ht0] at hs0 ⊢
              nlinarith [Real.pi_pos]
            have hhi : u < 9 * Real.pi / (4 * t) := by
              field_simp [ne_of_gt ht0] at hs0 ⊢
              nlinarith [Real.pi_pos]
            have htuL : 7 * Real.pi / 4 < t * u := by
              have h := mul_lt_mul_of_pos_left hlo ht0
              field_simp [ne_of_gt ht0] at h
              exact h
            have htuH : t * u < 9 * Real.pi / 4 := by
              have h := mul_lt_mul_of_pos_left hhi ht0
              field_simp [ne_of_gt ht0] at h
              exact h
            have hc : 0 < Real.cos (t*u) := by
              have hx : -(Real.pi/2) < t*u-2*Real.pi
                  ∧ t*u-2*Real.pi < Real.pi/2 := by
                constructor <;> linarith
              have hh := Real.cos_pos_of_mem_Ioo hx
              simpa [Real.cos_sub_int_mul_two_pi] using hh
            exact mul_ne_zero (Real.cosh_pos _).ne' hc.ne'))
    unfold quantitativeOuterPoleBaseWeight at hs
    have hbnn :=
      scaledUnitBump_nonneg
        (quantitativeTaperOuterCenter t)
        (quantitativeTaperR t) u
    have hcosh := Real.cosh_pos (u/2)
    have hcos : 0 < Real.cos (t*u) := by
      rcases hs with ⟨hlo,hhi⟩
      have htuL : 7*Real.pi/4 < t*u := by
        have h := mul_lt_mul_of_pos_left hlo ht0
        field_simp [ne_of_gt ht0] at h
        exact h
      have htuH : t*u < 9*Real.pi/4 := by
        have h := mul_lt_mul_of_pos_left hhi ht0
        field_simp [ne_of_gt ht0] at h
        exact h
      have hx : -(Real.pi/2) < t*u-2*Real.pi
          ∧ t*u-2*Real.pi < Real.pi/2 := by
        constructor <;> linarith
      have hh := Real.cos_pos_of_mem_Ioo hx
      simpa [Real.cos_sub_int_mul_two_pi] using hh
    positivity

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
  have hcanonical :
      poleEvenResp (quantitativeCanonicalTaper t) t 0
        =
      2 * ((∫ u : ℝ, F2 u)
        + quantitativeLambda t * ∫ u : ℝ, F1 u) := by
    have hi :=
      quantitativeInnerPole_eq_two_integral ht0
    have ho :=
      quantitativeOuterPole_eq_two_integral ht0
    unfold poleEvenResp quantitativeCanonicalTaper
    simp only [Real.cos_zero, mul_one]
    unfold F1 F2 quantitativeInnerPoleBaseWeight
      quantitativeOuterPoleBaseWeight
    have hIi :
      Integrable
        (fun u : ℝ =>
          quantitativeInnerBump t u
            * (Real.cosh (u/2) * Real.cos (t*u))) := by
      exact
        ((quantitativeInnerBump_continuous ht0).mul (by fun_prop))
          .integrable_of_hasCompactSupport
            (quantitativeInnerBump_compact ht0).mul_right
    have hIo :
      Integrable
        (fun u : ℝ =>
          quantitativeOuterBump t u
            * (Real.cosh (u/2) * Real.cos (t*u))) := by
      exact
        ((quantitativeOuterBump_continuous ht0).mul (by fun_prop))
          .integrable_of_hasCompactSupport
            (quantitativeOuterBump_compact ht0).mul_right
    rw [show
      (fun u : ℝ =>
        (quantitativeInnerBump t u
          + quantitativeLambda t * quantitativeOuterBump t u)
          * (Real.cosh (u / 2) * Real.cos (t * u)))
      =
      fun u : ℝ =>
        quantitativeInnerBump t u
          * (Real.cosh (u / 2) * Real.cos (t*u))
        + quantitativeLambda t *
          (quantitativeOuterBump t u
            * (Real.cosh (u / 2) * Real.cos (t*u))) by
        funext u
        ring]
    rw [integral_add hIi (hIo.const_mul _), integral_const_mul]
    -- unfold the symmetric bumps and reflect the even base weight
    unfold quantitativeInnerBump quantitativeOuterBump
      quantitativeSymBump
      Zeta23Bridge.LiteralWeilOddChannelTaper.symmetrize
    have hbaseEven :
        ∀ u : ℝ,
          Real.cosh ((-u)/2) * Real.cos (t*(-u))
            =
          Real.cosh (u/2) * Real.cos (t*u) := by
      intro u
      simp [Real.cosh_neg, Real.cos_neg]
    have hinnerSym :
      (∫ u : ℝ,
        (scaledUnitBump
            (quantitativeTaperInnerCenter t)
            (quantitativeTaperR t) u
          + scaledUnitBump
            (quantitativeTaperInnerCenter t)
            (quantitativeTaperR t) (-u))
        * (Real.cosh (u/2) * Real.cos (t*u)))
      =
      2 * ∫ u : ℝ,
        scaledUnitBump
          (quantitativeTaperInnerCenter t)
          (quantitativeTaperR t) u
        * (Real.cosh (u/2) * Real.cos (t*u)) := by
      exact integral_symmetrize
        (scaledUnitBump_continuous
          (quantitativeTaperR_pos ht0).ne' _)
        (scaledUnitBump_hasCompactSupport
          (quantitativeTaperR_pos ht0))
        (by fun_prop)
        hbaseEven
    have houterSym :
      (∫ u : ℝ,
        (scaledUnitBump
            (quantitativeTaperOuterCenter t)
            (quantitativeTaperR t) u
          + scaledUnitBump
            (quantitativeTaperOuterCenter t)
            (quantitativeTaperR t) (-u))
        * (Real.cosh (u/2) * Real.cos (t*u)))
      =
      2 * ∫ u : ℝ,
        scaledUnitBump
          (quantitativeTaperOuterCenter t)
          (quantitativeTaperR t) u
        * (Real.cosh (u/2) * Real.cos (t*u)) := by
      exact integral_symmetrize
        (scaledUnitBump_continuous
          (quantitativeTaperR_pos ht0).ne' _)
        (scaledUnitBump_hasCompactSupport
          (quantitativeTaperR_pos ht0))
        (by fun_prop)
        hbaseEven
    rw [hinnerSym, houterSym]
    ring
  rw [hcanonical]
  nlinarith

end Synthesis
