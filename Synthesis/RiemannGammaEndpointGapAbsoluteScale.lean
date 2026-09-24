import Synthesis.RiemannGammaInnerRatioAbsoluteScale
import Synthesis.RiemannQuantitativeGammaDeficit
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Explicit linear lower bound for the canonical endpoint Gamma ratio gap

The literal Gamma-cone consumer is already welded through

  d(t) = R_t(7*pi/(4t)) - R_t(5*pi/(4t)).

This file quantifies that exact endpoint gap.

At theta_5=5*pi/64:
  A(theta_5) <= (10/19) theta_5^2.

At theta_7=7*pi/64:
  A(theta_7) >= 2 (99/100)^2 (theta_7/2)^2.

For the hyperbolic denominator:
  H(5*pi/(4t)) >= 2 * 5*pi/(4t),
  H(7*pi/(4t)) <= (69/59) * 2 * 7*pi/(4t).

Combining the rational constants gives

  canonicalGammaRatioGap(t)
    >= pi * (2636149 / 17899520000) * t

for every t>=18.
-/

noncomputable section

open scoped Real

namespace Synthesis

def canonicalGammaGapLinearConstant : ℝ :=
  Real.pi * (2636149 / 17899520000 : ℝ)

theorem canonicalGammaGapLinearConstant_pos :
    0 < canonicalGammaGapLinearConstant := by
  unfold canonicalGammaGapLinearConstant
  positivity

theorem one_sub_cos_le_sq_div_two
    {x : ℝ} (hx0 : 0 <= x) :
    1 - Real.cos x <= x^2 / 2 := by
  rw [one_sub_cos_eq_two_sin_half_sq]
  have hs0 : 0 <= Real.sin (x/2) := by
    by_cases hpi : x/2 <= Real.pi
    · exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hpi
    · have hsle := Real.sin_le (show 0 <= x/2 by linarith)
      nlinarith [Real.neg_one_le_sin (x/2)]
  have hsle : Real.sin (x/2) <= x/2 :=
    Real.sin_le (by linarith)
  nlinarith

theorem cos_five_pi_64_ge_nineteen_twentieths :
    (19/20 : ℝ) <= Real.cos (5 * Real.pi / 64) := by
  have hx0 : 0 <= 5 * Real.pi / 64 := by positivity
  have h :=
    one_sub_cos_le_sq_div_two (x := 5 * Real.pi / 64) hx0
  have hpi := Real.pi_lt_four
  have hsquare :
      (5 * Real.pi / 64)^2 / 2 < (1/20 : ℝ) := by
    nlinarith [sq_nonneg (Real.pi)]
  linarith

theorem phaseRatio_five_pi_64_upper :
    centeredPolePhaseRatio (5 * Real.pi / 64)
      <= (10/19 : ℝ) * (5 * Real.pi / 64)^2 := by
  have hc : 0 < Real.cos (5 * Real.pi / 64) := by
    have h := cos_five_pi_64_ge_nineteen_twentieths
    linarith
  have hnum :=
    one_sub_cos_le_sq_div_two
      (x := 5 * Real.pi / 64) (by positivity)
  unfold centeredPolePhaseRatio
  rw [div_le_iff₀ hc]
  have hcos := cos_five_pi_64_ge_nineteen_twentieths
  have hsquare : 0 <= (5 * Real.pi / 64)^2 := sq_nonneg _
  nlinarith

theorem sin_seven_pi_128_gt_ninetynine_percent :
    (99/100 : ℝ) * (7 * Real.pi / 128)
      < Real.sin (7 * Real.pi / 128) := by
  let x : ℝ := 7 * Real.pi / 128
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hxSq : x^2 < 3/50 := by
    dsimp [x]
    have hpi := Real.pi_lt_four
    nlinarith [sq_nonneg Real.pi]
  have hs := Real.sin_gt_sub_cube hx0
  have hlin :
      (99/100 : ℝ) * x < x - x^3/6 := by
    nlinarith [mul_pos hx0 (sub_pos.mpr hxSq)]
  exact lt_trans hlin hs

theorem phaseRatio_seven_pi_64_lower :
    2 * (99/100 : ℝ)^2 * (7 * Real.pi / 128)^2
      <= centeredPolePhaseRatio (7 * Real.pi / 64) := by
  have htheta0 : 0 < 7 * Real.pi / 64 := by positivity
  have hthetaPi : 7 * Real.pi / 64 < Real.pi/2 := by
    nlinarith [Real.pi_pos]
  have hc : 0 < Real.cos (7 * Real.pi / 64) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hc1 : Real.cos (7 * Real.pi / 64) <= 1 :=
    Real.cos_le_one _
  have hsin := sin_seven_pi_128_gt_ninetynine_percent
  have hsin0 : 0 <= (99/100 : ℝ) * (7 * Real.pi / 128) := by
    positivity
  have hsq :
      ((99/100 : ℝ) * (7 * Real.pi / 128))^2
        <= Real.sin (7 * Real.pi / 128)^2 := by
    nlinarith
  unfold centeredPolePhaseRatio
  rw [one_sub_cos_eq_two_sin_half_sq]
  have hnum :
      2 * (99/100 : ℝ)^2 * (7 * Real.pi / 128)^2
        <= 2 * Real.sin (7 * Real.pi / 128)^2 := by
    nlinarith
  rw [le_div_iff₀ hc]
  have hleft :
      (2 * (99/100 : ℝ)^2 * (7 * Real.pi / 128)^2)
          * Real.cos (7 * Real.pi / 64)
        <=
      2 * (99/100 : ℝ)^2 * (7 * Real.pi / 128)^2 := by
    exact mul_le_of_le_one_right (by positivity) hc1
  exact le_trans hleft hnum

theorem gammaPoleHyperbolicDenom_five_lower
    {t : ℝ} (ht : 18 <= t) :
    5 * Real.pi / (2*t)
      <= gammaPoleHyperbolicDenom (5 * Real.pi / (4*t)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let u : ℝ := 5 * Real.pi / (4*t)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hs : u <= Real.sinh u :=
    self_le_sinh_of_nonneg hu0.le
  have hc : 1 <= Real.cosh (u/2) := Real.one_le_cosh _
  unfold gammaPoleHyperbolicDenom
  dsimp [u]
  nlinarith [Real.sinh_pos_iff.mpr hu0]

theorem gammaPoleHyperbolicDenom_seven_upper
    {t : ℝ} (ht : 18 <= t) :
    gammaPoleHyperbolicDenom (7 * Real.pi / (4*t))
      <= 483 * Real.pi / (118*t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let u : ℝ := 7 * Real.pi / (4*t)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have huPi : u <= Real.pi/8 := by
    dsimp [u]
    rw [div_le_iff₀ ht0]
    nlinarith [Real.pi_pos]
  have hs :
      Real.sinh u <= u * Real.cosh u :=
    sinh_le_mul_cosh_of_nonneg hu0.le
  have hc :
      Real.cosh u * Real.cosh (u/2) <= 69/59 :=
    cosh_mul_cosh_half_le_sixtynine_fiftynine hu0.le huPi
  unfold gammaPoleHyperbolicDenom
  dsimp [u]
  have hch0 : 0 <= Real.cosh (7 * Real.pi / (8*t)) :=
    (Real.cosh_pos _).le
  have h1 :
      2 * Real.sinh (7 * Real.pi / (4*t))
          * Real.cosh (7 * Real.pi / (8*t))
        <=
      2 * (7 * Real.pi / (4*t))
          * (69/59 : ℝ) := by
    have hs' :
        Real.sinh (7 * Real.pi / (4*t))
          <=
        (7 * Real.pi / (4*t))
          * Real.cosh (7 * Real.pi / (4*t)) := by
      simpa [u] using hs
    have hc' :
        Real.cosh (7 * Real.pi / (4*t))
          * Real.cosh (7 * Real.pi / (8*t))
          <= 69/59 := by
      simpa [u] using hc
    have hstep :
        2 * Real.sinh (7 * Real.pi / (4*t))
            * Real.cosh (7 * Real.pi / (8*t))
          <=
        2 * ((7 * Real.pi / (4*t))
            * Real.cosh (7 * Real.pi / (4*t)))
            * Real.cosh (7 * Real.pi / (8*t)) := by
      gcongr
    nlinarith
  calc
    2 * Real.sinh (7 * Real.pi / (4*t))
        * Real.cosh (7 * Real.pi / (8*t))
      <= 2 * (7 * Real.pi / (4*t)) * (69/59 : ℝ) := h1
    _ = 483 * Real.pi / (118*t) := by
      field_simp [ne_of_gt ht0]
      ring

theorem gammaToPoleRatio_five_upper
    {t : ℝ} (ht : 18 <= t) :
    gammaToPoleRatio t (5 * Real.pi/(4*t))
      <=
    ((10/19 : ℝ) * (5 * Real.pi/64)^2)
      * (2*t/(5*Real.pi)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let u : ℝ := 5 * Real.pi/(4*t)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hangle :
      (t/16)*u = 5 * Real.pi/64 := by
    dsimp [u]
    field_simp [ne_of_gt ht0]
    ring
  have hH := gammaPoleHyperbolicDenom_five_lower ht
  have hH0 : 0 < gammaPoleHyperbolicDenom u :=
    gammaPoleHyperbolicDenom_pos hu0
  have hphase := phaseRatio_five_pi_64_upper
  rw [gammaToPoleRatio_eq_phase_div_hyperbolic
      hu0 (by positivity)
      (by rw [hangle]; nlinarith [Real.pi_pos]),
      hangle]
  have hden0 : 0 < 5 * Real.pi / (2*t) := by positivity
  have hdiv :
      centeredPolePhaseRatio (5 * Real.pi/64)
          / gammaPoleHyperbolicDenom u
        <=
      ((10/19 : ℝ) * (5 * Real.pi/64)^2)
          / (5 * Real.pi/(2*t)) := by
    rw [div_le_div_iff₀ hH0 hden0]
    have h1 :
        centeredPolePhaseRatio (5 * Real.pi/64)
            * (5 * Real.pi/(2*t))
          <=
        ((10/19 : ℝ) * (5 * Real.pi/64)^2)
            * (5 * Real.pi/(2*t)) := by
      exact mul_le_mul_of_nonneg_right hphase hden0.le
    have h2 :
        ((10/19 : ℝ) * (5 * Real.pi/64)^2)
            * (5 * Real.pi/(2*t))
          <=
        ((10/19 : ℝ) * (5 * Real.pi/64)^2)
            * gammaPoleHyperbolicDenom u := by
      exact mul_le_mul_of_nonneg_left hH (by positivity)
    exact le_trans h1 h2
  calc
    centeredPolePhaseRatio (5 * Real.pi/64)
        / gammaPoleHyperbolicDenom u
      <= ((10/19 : ℝ) * (5 * Real.pi/64)^2)
          / (5 * Real.pi/(2*t)) := hdiv
    _ = ((10/19 : ℝ) * (5 * Real.pi/64)^2)
          * (2*t/(5*Real.pi)) := by
      field_simp [ne_of_gt ht0, ne_of_gt Real.pi_pos]
      ring

theorem gammaToPoleRatio_seven_lower
    {t : ℝ} (ht : 18 <= t) :
    (2 * (99/100 : ℝ)^2 * (7 * Real.pi/128)^2)
        * (118*t/(483*Real.pi))
      <=
    gammaToPoleRatio t (7 * Real.pi/(4*t)) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let u : ℝ := 7 * Real.pi/(4*t)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hangle :
      (t/16)*u = 7 * Real.pi/64 := by
    dsimp [u]
    field_simp [ne_of_gt ht0]
    ring
  have hH := gammaPoleHyperbolicDenom_seven_upper ht
  have hH0 : 0 < gammaPoleHyperbolicDenom u :=
    gammaPoleHyperbolicDenom_pos hu0
  have hphase := phaseRatio_seven_pi_64_lower
  rw [gammaToPoleRatio_eq_phase_div_hyperbolic
      hu0 (by positivity)
      (by rw [hangle]; nlinarith [Real.pi_pos]),
      hangle]
  have hdenU : 0 < 483 * Real.pi / (118*t) := by positivity
  have hdiv :
      (2 * (99/100 : ℝ)^2 * (7 * Real.pi/128)^2)
          / (483 * Real.pi/(118*t))
        <=
      centeredPolePhaseRatio (7 * Real.pi/64)
          / gammaPoleHyperbolicDenom u := by
    rw [div_le_div_iff₀ hdenU hH0]
    have h1 :
        (2 * (99/100 : ℝ)^2 * (7 * Real.pi/128)^2)
            * gammaPoleHyperbolicDenom u
          <=
        (2 * (99/100 : ℝ)^2 * (7 * Real.pi/128)^2)
            * (483 * Real.pi/(118*t)) := by
      exact mul_le_mul_of_nonneg_left hH (by positivity)
    have h2 :
        (2 * (99/100 : ℝ)^2 * (7 * Real.pi/128)^2)
            * (483 * Real.pi/(118*t))
          <=
        centeredPolePhaseRatio (7 * Real.pi/64)
            * (483 * Real.pi/(118*t)) := by
      exact mul_le_mul_of_nonneg_right hphase hdenU.le
    exact le_trans h1 h2
  calc
    (2 * (99/100 : ℝ)^2 * (7 * Real.pi/128)^2)
        * (118*t/(483*Real.pi))
      =
    (2 * (99/100 : ℝ)^2 * (7 * Real.pi/128)^2)
        / (483 * Real.pi/(118*t)) := by
          field_simp [ne_of_gt ht0, ne_of_gt Real.pi_pos]
          ring
    _ <= centeredPolePhaseRatio (7 * Real.pi/64)
          / gammaPoleHyperbolicDenom u := hdiv

theorem canonicalGammaRatioGap_linear_lower
    {t : ℝ} (ht : 18 <= t) :
    canonicalGammaGapLinearConstant * t
      <= canonicalGammaRatioGap t := by
  have h5raw := gammaToPoleRatio_five_upper ht
  have h7raw := gammaToPoleRatio_seven_lower ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have h5 :
      gammaToPoleRatio t (5 * Real.pi/(4*t))
        <= (25/19456 : ℝ) * Real.pi * t := by
    calc
      gammaToPoleRatio t (5 * Real.pi/(4*t))
        <= ((10/19 : ℝ) * (5 * Real.pi/64)^2)
            * (2*t/(5*Real.pi)) := h5raw
      _ = (25/19456 : ℝ) * Real.pi * t := by
        field_simp [ne_of_gt Real.pi_pos]
        ring
  have h7 :
      (1349271/942080000 : ℝ) * Real.pi * t
        <= gammaToPoleRatio t (7 * Real.pi/(4*t)) := by
    calc
      (1349271/942080000 : ℝ) * Real.pi * t
        =
      (2 * (99/100 : ℝ)^2 * (7 * Real.pi/128)^2)
        * (118*t/(483*Real.pi)) := by
          field_simp [ne_of_gt Real.pi_pos]
          ring
      _ <= gammaToPoleRatio t (7 * Real.pi/(4*t)) := h7raw
  unfold canonicalGammaRatioGap canonicalGammaGapLinearConstant
  nlinarith [Real.pi_pos]

end Synthesis
