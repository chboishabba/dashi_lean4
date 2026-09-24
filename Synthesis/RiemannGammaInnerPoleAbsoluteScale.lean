import Synthesis.RiemannGammaMatchedQuantitativeGain
import Synthesis.RiemannQuantitativeCanonicalTaper
import Zeta23Bridge.PoleQuotientComplementMargin

/-!
# Absolute scale of the canonical inner pole mass

On the positive inner affine bump one has

  3*pi/4 < t*u < 5*pi/4.

Hence

  -cos(t*u) >= sqrt(2)/2.

The selected-radius sample phase also lies inside the quarter-period window, so

  cos((t/16)*u) >= sqrt(2)/2,

while cosh(u/2) >= 1.  Therefore the negative inner pole weight is at least
1/2 pointwise on the bump.

The literal symmetric pole response is twice the positive-coordinate integral.
Together with exact affine bump mass scaling this gives

  - quantitativeInnerPole(t)
      >= quantitativeTaperR(t) * unitBumpMass0
      = pi * unitBumpMass0 / (4 t),

and therefore

  - t * quantitativeInnerPole(t)
      >= pi * unitBumpMass0 / 4.

This is the first half of the absolute order-one Gamma-margin theorem.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.PoleQuotientComplementMargin

theorem innerPoleWeight_neg_ge_half
    {t u : ℝ}
    (ht : 0 < t)
    (hu : |u - quantitativeTaperInnerCenter t|
      < quantitativeTaperR t) :
    (1 / 2 : ℝ)
      <= - quantitativePoleWeight t (quantitativeSampleRadius t) u := by
  unfold quantitativeTaperInnerCenter quantitativeTaperR at hu
  rw [abs_lt] at hu
  have htuLow : 3 * Real.pi / 4 < t * u := by
    have h := mul_lt_mul_of_pos_left hu.1 ht
    field_simp at h ⊢
    nlinarith [Real.pi_pos]
  have htuHigh : t * u < 5 * Real.pi / 4 := by
    have h := mul_lt_mul_of_pos_left hu.2 ht
    field_simp at h ⊢
    nlinarith [Real.pi_pos]
  have huPos : 0 < u := by
    have : 0 < 3 * Real.pi / (4*t) := by positivity
    linarith
  have hnearPi :
      |(t*u + Real.pi) - 2 * Real.pi| <= Real.pi / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hct :
      Real.sqrt 2 / 2 <= - Real.cos (t*u) := by
    have h :=
      cos_ge_sqrtTwoHalf_of_near_twoPi
        (x := t*u + Real.pi) hnearPi
    rw [Real.cos_add_pi] at h
    exact h
  have hsampleWindow :
      2 * quantitativeSampleRadius t * |u| < Real.pi / 2 := by
    unfold quantitativeSampleRadius
    rw [abs_of_pos huPos]
    nlinarith [Real.pi_pos]
  have hsample :
      Real.sqrt 2 / 2
        <= Real.cos (quantitativeSampleRadius t * u) :=
    cos_ge_of_window
      (by unfold quantitativeSampleRadius; positivity)
      hsampleWindow
  have hch : 1 <= Real.cosh (u/2) := Real.one_le_cosh _
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrt0 : 0 <= Real.sqrt 2 := Real.sqrt_nonneg _
  unfold quantitativePoleWeight
  have hct0 : 0 <= -Real.cos (t*u) := le_trans (by positivity) hct
  have hs0 : 0 <= Real.cos (quantitativeSampleRadius t * u) :=
    le_trans (by positivity) hsample
  nlinarith [mul_nonneg hct0 hs0]

theorem quantitativeInnerPole_abs_lower
    {t : ℝ} (ht : 18 <= t) :
    quantitativeTaperR t * unitBumpMass0
      <= - quantitativeInnerPole t := by
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
  have hiWeighted : Integrable
      (fun u : ℝ =>
        phi u * (- quantitativePoleWeight t (quantitativeSampleRadius t) u)) :=
    Zeta23Bridge.LiteralWeilParityBalance.taper_integrable
      hphi hphic (by unfold quantitativePoleWeight; fun_prop)
  have hpoint : ∀ u : ℝ,
      (1/2 : ℝ) * phi u
        <= phi u *
          (- quantitativePoleWeight t (quantitativeSampleRadius t) u) := by
    intro u
    by_cases hu : phi u = 0
    · simp [hu]
    · have hwin := scaledUnitBump_support
        (quantitativeTaperR_pos ht0) hu
      exact mul_le_mul_of_nonneg_left
        (innerPoleWeight_neg_ge_half ht0 hwin)
        (scaledUnitBump_nonneg _ _ _)
  have hint := integral_mono
    (hiPhi.const_mul (1/2 : ℝ)) hiWeighted hpoint
  rw [integral_const_mul] at hint
  have hmass :
      (∫ u : ℝ, phi u)
        = quantitativeTaperR t * unitBumpMass0 := by
    have habs : (fun u : ℝ => |phi u|) = phi := by
      funext u
      rw [abs_of_nonneg (scaledUnitBump_nonneg _ _ _)]
    have hm := taperMass_scaledUnitBump
      (c := quantitativeTaperInnerCenter t)
      (quantitativeTaperR_pos ht0)
    unfold taperMass at hm
    rw [habs] at hm
    exact hm
  rw [hmass] at hint
  have hneg :
      -(2 * ∫ u : ℝ,
        phi u * quantitativePoleWeight t (quantitativeSampleRadius t) u)
      =
      2 * ∫ u : ℝ,
        phi u * (- quantitativePoleWeight t (quantitativeSampleRadius t) u) := by
    have hrew :
        (fun u : ℝ =>
          phi u * (- quantitativePoleWeight t (quantitativeSampleRadius t) u))
        =
        fun u : ℝ =>
          -(phi u * quantitativePoleWeight t (quantitativeSampleRadius t) u) := by
      funext u
      ring
    rw [hrew, integral_neg]
    ring
  rw [hneg]
  nlinarith

theorem quantitativeInnerPole_scaled_lower
    {t : ℝ} (ht : 18 <= t) :
    Real.pi * unitBumpMass0 / 4
      <= -t * quantitativeInnerPole t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have h := quantitativeInnerPole_abs_lower ht
  unfold quantitativeTaperR at h
  have hm0 : 0 < unitBumpMass0 := unitBumpMass0_pos
  have htMul :=
    mul_le_mul_of_nonneg_left h ht0.le
  field_simp [ne_of_gt ht0] at htMul ⊢
  nlinarith [Real.pi_pos, hm0]

end Synthesis
