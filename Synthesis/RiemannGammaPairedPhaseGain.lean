import Synthesis.RiemannGammaArchimedeanKernelGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Paired phase gain across the canonical two-window taper

At the same normalized bump coordinate, the inner and outer sample angles differ
by exactly pi/16.  Write

    theta_in  = theta,
    theta_out = theta + pi/16.

For theta in [3pi/64, 5pi/64], the centered-to-pole modulation ratio

    A(theta) = (1-cos theta)/cos theta

grows by a factor strictly larger than 3:

    3 A(theta_in) < A(theta_out).

This is the trigonometric half of the Gamma-vs-pole paired-window comparison.
-/

noncomputable section

open scoped Real

namespace Synthesis

def centeredPolePhaseRatio (theta : ℝ) : ℝ :=
  (1 - Real.cos theta) / Real.cos theta

theorem one_sub_cos_eq_two_sin_half_sq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x/2) ^ 2 := by
  have h := Real.sin_sq_add_cos_sq (x/2)
  have hc := Real.cos_two_mul (x/2)
  rw [show 2 * (x/2) = x by ring] at hc
  nlinarith

theorem canonical_inner_phase_pos {theta : ℝ}
    (hlo : 3 * Real.pi / 64 <= theta) :
    0 < theta := by
  have hp := Real.pi_pos
  nlinarith

theorem canonical_outer_phase_lt_pi_div_two {theta : ℝ}
    (hhi : theta <= 5 * Real.pi / 64) :
    theta + Real.pi/16 < Real.pi/2 := by
  have hp := Real.pi_pos
  nlinarith

theorem sin_outer_half_gt_ninetynine_percent
    {theta : ℝ}
    (hlo : 3 * Real.pi / 64 <= theta)
    (hhi : theta <= 5 * Real.pi / 64) :
    (99/100 : ℝ) * ((theta + Real.pi/16)/2)
      < Real.sin ((theta + Real.pi/16)/2) := by
  let a : ℝ := (theta + Real.pi/16)/2
  have ha0 : 0 < a := by
    dsimp [a]
    have hp := Real.pi_pos
    nlinarith [canonical_inner_phase_pos hlo]
  have haUpper : a < 9 * (3.15 : ℝ) / 128 := by
    dsimp [a]
    have hpi := Real.pi_lt_d2
    nlinarith
  have haSq : a^2 < 3/50 := by
    have hnum : (9 * (3.15 : ℝ) / 128)^2 < 3/50 := by norm_num
    nlinarith [sq_nonneg a]
  have hsin := Real.sin_gt_sub_cube ha0
  have hfactor : (99/100 : ℝ) * a < a - a^3/6 := by
    have haPos := ha0
    nlinarith [mul_pos haPos (sub_pos.mpr haSq)]
  exact lt_trans hfactor hsin

theorem paired_half_phase_ratio_gt
    {theta : ℝ}
    (hlo : 3 * Real.pi / 64 <= theta)
    (hhi : theta <= 5 * Real.pi / 64) :
    (891/500 : ℝ) * (theta/2)
      < Real.sin ((theta + Real.pi/16)/2) := by
  have houter := sin_outer_half_gt_ninetynine_percent hlo hhi
  have hratio :
      (9/5 : ℝ) * (theta/2)
        <= (theta + Real.pi/16)/2 := by
    have hp := Real.pi_pos
    have htheta : theta <= 5 * Real.pi/64 := hhi
    nlinarith
  nlinarith

theorem three_sin_inner_sq_lt_sin_outer_sq
    {theta : ℝ}
    (hlo : 3 * Real.pi / 64 <= theta)
    (hhi : theta <= 5 * Real.pi / 64) :
    3 * Real.sin (theta/2)^2
      < Real.sin ((theta + Real.pi/16)/2)^2 := by
  have htheta0 : 0 < theta := canonical_inner_phase_pos hlo
  have hinnerPos : 0 < theta/2 := by linarith
  have hinnerUpper : Real.sin (theta/2) <= theta/2 :=
    Real.sin_le hinnerPos.le
  have houterLower := paired_half_phase_ratio_gt hlo hhi
  have hsinInner0 : 0 <= Real.sin (theta/2) := by
    have hpi2 : theta/2 <= Real.pi/2 := by
      have hp := Real.pi_pos
      nlinarith
    exact Real.sin_nonneg_of_nonneg_of_le_pi
      hinnerPos.le (by nlinarith)
  have hcoef : (3:ℝ) < (891/500)^2 := by norm_num
  have hsquare :
      ((891/500 : ℝ) * (theta/2))^2
        < Real.sin ((theta + Real.pi/16)/2)^2 := by
    have hleft0 : 0 <= (891/500 : ℝ) * (theta/2) := by positivity
    have hright0 :
        0 < Real.sin ((theta + Real.pi/16)/2) := by
      exact lt_of_lt_of_le houterLower.le ?_
    nlinarith
  have hinnerSq : Real.sin (theta/2)^2 <= (theta/2)^2 := by
    nlinarith
  nlinarith [sq_nonneg (theta/2)]

theorem three_phaseRatio_inner_lt_outer
    {theta : ℝ}
    (hlo : 3 * Real.pi / 64 <= theta)
    (hhi : theta <= 5 * Real.pi / 64) :
    3 * centeredPolePhaseRatio theta
      < centeredPolePhaseRatio (theta + Real.pi/16) := by
  have ht0 : 0 < theta := canonical_inner_phase_pos hlo
  have hout : theta + Real.pi/16 < Real.pi/2 :=
    canonical_outer_phase_lt_pi_div_two hhi
  have htpi : theta < Real.pi/2 := by
    have hp := Real.pi_pos
    nlinarith
  have hct : 0 < Real.cos theta := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hco : 0 < Real.cos (theta + Real.pi/16) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hcosOrder :
      Real.cos (theta + Real.pi/16) < Real.cos theta := by
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      ht0.le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsinSq := three_sin_inner_sq_lt_sin_outer_sq hlo hhi
  rw [centeredPolePhaseRatio, centeredPolePhaseRatio,
      one_sub_cos_eq_two_sin_half_sq,
      one_sub_cos_eq_two_sin_half_sq]
  rw [div_lt_div_iff₀ hct hco]
  have hcosOuter0 : 0 < Real.cos (theta + Real.pi/16) := hco
  have hcosInner0 : 0 < Real.cos theta := hct
  nlinarith [mul_pos hcosOuter0 hcosInner0]

end Synthesis
