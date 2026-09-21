import Synthesis.RiemannGammaPairedWeightRatio

/-!
# Quantitative matched-coordinate Gamma/pole ratio gain

The existing paired Gamma proof deliberately relaxed two quantitative estimates
to the common factor 3.  For the final H2 budget we retain the slack.

On the canonical inner window:

* the phase ratio grows by more than 317/100;
* the hyperbolic denominator grows by at most 161/59.

Since 317/100 > 161/59, the matched Gamma/pole ratio has a uniform relative
gain.  Concretely,

  (2603/16100) * R_t(u)
    < R_t(u+pi/t) - R_t(u).

This is the quantitative matched-coordinate input needed to turn the integrated
Gamma deficit into an explicit high-height margin.
-/

noncomputable section

open scoped Real

namespace Synthesis

theorem cosh_mul_cosh_half_le_sixtynine_fiftynine
    {v : ℝ}
    (hv0 : 0 <= v)
    (hv : v <= Real.pi/8) :
    Real.cosh v * Real.cosh (v/2) <= 69/59 := by
  have hcv :
      Real.cosh v <= Real.exp (v^2/2) :=
    Real.cosh_le_exp_half_sq v
  have hch :
      Real.cosh (v/2) <= Real.exp ((v/2)^2/2) :=
    Real.cosh_le_exp_half_sq (v/2)
  have hvLe : v <= 1/2 := by
    nlinarith [Real.pi_lt_four]
  have hvSq : v^2 <= 1/4 := by
    nlinarith [sq_nonneg v]
  have hexpArg :
      v^2/2 + (v/2)^2/2 <= 5/32 := by
    nlinarith
  have hprod :
      Real.cosh v * Real.cosh (v/2)
        <= Real.exp (v^2/2 + (v/2)^2/2) := by
    calc
      Real.cosh v * Real.cosh (v/2)
          <= Real.exp (v^2/2) * Real.exp ((v/2)^2/2) :=
        mul_le_mul hcv hch (Real.cosh_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (v^2/2 + (v/2)^2/2) := by
        rw [Real.exp_add]
  have hmono :
      Real.exp (v^2/2 + (v/2)^2/2)
        <= Real.exp (5/32 : ℝ) :=
    Real.exp_le_exp.mpr hexpArg
  have hrat :
      Real.exp (5/32 : ℝ) <= (69/59 : ℝ) := by
    have h :=
      Real.exp_le_two_add_div_two_sub
        (x := (5/32 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  exact le_trans hprod (le_trans hmono hrat)

theorem paired_gammaPoleHyperbolicDenom_le_161_59
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    gammaPoleHyperbolicDenom (u + Real.pi/t)
      <= (161/59 : ℝ) * gammaPoleHyperbolicDenom u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) huLower
  let v : ℝ := u + Real.pi/t
  have hv0 : 0 < v := by
    dsimp [v]
    positivity
  have hvPi : v <= Real.pi/8 := by
    dsimp [v]
    exact canonical_paired_outer_le_pi_div_eight ht huUpper
  have hratio : v <= (7/3 : ℝ) * u := by
    dsimp [v]
    exact paired_outer_over_inner_le_seven_thirds ht0 huLower
  have hsinhV :
      Real.sinh v <= v * Real.cosh v :=
    sinh_le_mul_cosh_of_nonneg hv0.le
  have hcoshPair :
      Real.cosh v * Real.cosh (v/2) <= 69/59 :=
    cosh_mul_cosh_half_le_sixtynine_fiftynine hv0.le hvPi
  have hupper :
      gammaPoleHyperbolicDenom v
        <= 2 * v * (69/59 : ℝ) := by
    unfold gammaPoleHyperbolicDenom
    have hcv : 0 <= Real.cosh (v/2) := (Real.cosh_pos _).le
    have h1 :
        2 * Real.sinh v * Real.cosh (v/2)
          <= 2 * (v * Real.cosh v) * Real.cosh (v/2) := by
      gcongr
    have h2 :
        2 * (v * Real.cosh v) * Real.cosh (v/2)
          <= 2 * v * (69/59 : ℝ) := by
      have hvnn : 0 <= 2 * v := by positivity
      nlinarith
    exact le_trans h1 h2
  have hlower :
      2 * u <= gammaPoleHyperbolicDenom u := by
    unfold gammaPoleHyperbolicDenom
    have hsu : u <= Real.sinh u :=
      self_le_sinh_of_nonneg hu0.le
    have hch : 1 <= Real.cosh (u/2) := Real.one_le_cosh _
    nlinarith [Real.sinh_pos_iff.mpr hu0]
  dsimp [v] at hupper hratio
  nlinarith

theorem phaseRatio_317_100_inner_lt_outer
    {theta : ℝ}
    (hlo : 3 * Real.pi / 64 <= theta)
    (hhi : theta <= 5 * Real.pi / 64) :
    (317/100 : ℝ) * centeredPolePhaseRatio theta
      < centeredPolePhaseRatio (theta + Real.pi/16) := by
  have ht0 : 0 < theta := canonical_inner_phase_pos hlo
  have hout : theta + Real.pi/16 < Real.pi/2 :=
    canonical_outer_phase_lt_pi_div_two hhi
  have htpi : theta < Real.pi/2 := by
    nlinarith [Real.pi_pos]
  have hct : 0 < Real.cos theta := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hco : 0 < Real.cos (theta + Real.pi/16) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hcosOrder :
      Real.cos (theta + Real.pi/16) < Real.cos theta :=
    Real.cos_lt_cos_of_nonneg_of_le_pi
      ht0.le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hinnerUpper : Real.sin (theta/2) <= theta/2 :=
    Real.sin_le (by linarith)
  have hsinInner0 : 0 <= Real.sin (theta/2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · nlinarith [Real.pi_pos]
  have houterLower := paired_half_phase_ratio_gt hlo hhi
  have houter0 : 0 < Real.sin ((theta + Real.pi/16)/2) := by
    have hleft : 0 <= (891/500 : ℝ) * (theta/2) := by positivity
    exact lt_of_le_of_lt hleft houterLower
  have hcoef : (317/100 : ℝ) < (891/500)^2 := by norm_num
  have hsinSq :
      (317/100 : ℝ) * Real.sin (theta/2)^2
        < Real.sin ((theta + Real.pi/16)/2)^2 := by
    have hinSq : Real.sin (theta/2)^2 <= (theta/2)^2 := by
      nlinarith
    have houtSq :
        ((891/500 : ℝ) * (theta/2))^2
          < Real.sin ((theta + Real.pi/16)/2)^2 := by
      nlinarith [sq_nonneg ((891/500 : ℝ) * (theta/2))]
    nlinarith [sq_nonneg (theta/2)]
  have hstep1 :
      (317/100 : ℝ) * Real.sin (theta/2)^2
          * Real.cos (theta + Real.pi/16)
        <
      Real.sin ((theta + Real.pi/16)/2)^2
          * Real.cos (theta + Real.pi/16) :=
    mul_lt_mul_of_pos_right hsinSq hco
  have hstep2 :
      Real.sin ((theta + Real.pi/16)/2)^2
          * Real.cos (theta + Real.pi/16)
        <
      Real.sin ((theta + Real.pi/16)/2)^2 * Real.cos theta :=
    mul_lt_mul_of_pos_left hcosOrder (sq_pos_of_pos houter0)
  have hcross := lt_trans hstep1 hstep2
  rw [centeredPolePhaseRatio, centeredPolePhaseRatio,
      one_sub_cos_eq_two_sin_half_sq,
      one_sub_cos_eq_two_sin_half_sq]
  field_simp [hct.ne', hco.ne']
  nlinarith

theorem matched_gammaToPoleRatio_quantitative_gain
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    (2603/16100 : ℝ) * gammaToPoleRatio t u
      <
    gammaToPoleRatio t (u + Real.pi/t)
      - gammaToPoleRatio t u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) huLower
  let v : ℝ := u + Real.pi/t
  have hv0 : 0 < v := by dsimp [v]; positivity
  obtain ⟨hlo,hhi⟩ := paired_inner_phase_bounds ht0 huLower huUpper
  have hphase :
      (317/100 : ℝ) * centeredPolePhaseRatio ((t/16)*u)
        <
      centeredPolePhaseRatio ((t/16)*u + Real.pi/16) :=
    phaseRatio_317_100_inner_lt_outer hlo hhi
  have hH :
      gammaPoleHyperbolicDenom v
        <= (161/59 : ℝ) * gammaPoleHyperbolicDenom u := by
    dsimp [v]
    exact paired_gammaPoleHyperbolicDenom_le_161_59 ht huLower huUpper
  have hHin : 0 < gammaPoleHyperbolicDenom u :=
    gammaPoleHyperbolicDenom_pos hu0
  have hHout : 0 < gammaPoleHyperbolicDenom v :=
    gammaPoleHyperbolicDenom_pos hv0
  have hAin :
      0 < centeredPolePhaseRatio ((t/16)*u) := by
    apply centeredPolePhaseRatio_pos
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hangle :
      (t/16)*v = (t/16)*u + Real.pi/16 := by
    dsimp [v]
    exact paired_outer_phase_eq ht0
  have hinEq :=
    gammaToPoleRatio_eq_phase_div_hyperbolic
      (t:=t) hu0 (by positivity) (by nlinarith [Real.pi_pos])
  have houtEq :=
    gammaToPoleRatio_eq_phase_div_hyperbolic
      (t:=t) hv0
      (by rw [hangle]; nlinarith [Real.pi_pos])
      (by rw [hangle]; nlinarith [Real.pi_pos])
  rw [hinEq, houtEq, hangle]
  have hcross :
      (317/100 : ℝ) *
          centeredPolePhaseRatio ((t/16)*u)
          * gammaPoleHyperbolicDenom v
        <
      (161/59 : ℝ) *
          centeredPolePhaseRatio ((t/16)*u + Real.pi/16)
          * gammaPoleHyperbolicDenom u := by
    have h1 :
        (317/100 : ℝ) *
            centeredPolePhaseRatio ((t/16)*u)
            * gammaPoleHyperbolicDenom v
          <=
        (317/100 : ℝ) *
            centeredPolePhaseRatio ((t/16)*u)
            * ((161/59 : ℝ) * gammaPoleHyperbolicDenom u) := by
      exact mul_le_mul_of_nonneg_left hH
        (mul_nonneg (by norm_num) hAin.le)
    have h2 :
        (317/100 : ℝ) *
            centeredPolePhaseRatio ((t/16)*u)
            * ((161/59 : ℝ) * gammaPoleHyperbolicDenom u)
          <
        (161/59 : ℝ) *
            centeredPolePhaseRatio ((t/16)*u + Real.pi/16)
            * gammaPoleHyperbolicDenom u := by
      have hp := mul_lt_mul_of_pos_right hphase hHin
      nlinarith
    exact lt_of_le_of_lt h1 h2
  have hratio :
      (317/100 : ℝ) *
          (centeredPolePhaseRatio ((t/16)*u) /
            gammaPoleHyperbolicDenom u)
        <
      (161/59 : ℝ) *
          (centeredPolePhaseRatio ((t/16)*u + Real.pi/16) /
            gammaPoleHyperbolicDenom v) := by
    rw [div_lt_div_iff₀ hHin hHout]
    nlinarith
  have hrin :
      0 <
      centeredPolePhaseRatio ((t/16)*u) /
        gammaPoleHyperbolicDenom u := div_pos hAin hHin
  nlinarith

end Synthesis
