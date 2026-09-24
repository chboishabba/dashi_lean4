import Synthesis.RiemannGammaPairedPhaseGain
import Synthesis.RiemannGammaPairedHyperbolicGrowth

/-!
# Paired Gamma-to-pole weight ratio

For u>0 define the positive ratio

    R_t(u)
      = ((1-cos((t/16)u)) * K(u))
          / (cosh(u/2) * cos((t/16)u)),

where

    K(u) = exp(-u/2)/(1-exp(-2u))
         = 1/(2 sinh u).

Equivalently,

    R_t(u)
      = A((t/16)u) / H(u),

with
    A(theta) = (1-cos theta)/cos theta,
    H(u)     = 2 sinh u cosh(u/2).

At paired canonical bump points

    u_out = u_in + pi/t,

the previous two source theorems give

    A_out > 3 A_in,
    H_out < 3 H_in,

and therefore

    R_t(u_in) < R_t(u_out).

This is the exact pointwise comparison needed to transport selected-radius pole
cancellation into a centered Gamma sign.
-/

noncomputable section

open scoped Real

namespace Synthesis

def gammaToPoleRatio (t u : ℝ) : ℝ :=
  centeredRadiusWeight t u * gammaArchKernel u /
    (Real.cosh (u/2) * poleRadiusWeight t u)

theorem centeredPolePhaseRatio_pos
    {theta : ℝ}
    (h0 : 0 < theta)
    (hpi2 : theta < Real.pi/2) :
    0 < centeredPolePhaseRatio theta := by
  unfold centeredPolePhaseRatio
  have hc : 0 < Real.cos theta := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hlt : Real.cos theta < 1 := by
    have hcos0 : Real.cos 0 = 1 := by simp
    rw [← hcos0]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num) (by linarith [Real.pi_pos]) h0
  exact div_pos (by linarith) hc

theorem gammaToPoleRatio_eq_phase_div_hyperbolic
    {t u : ℝ}
    (hu : 0 < u)
    (hangle0 : 0 <= (t/16)*u)
    (hanglePi2 : (t/16)*u < Real.pi/2) :
    gammaToPoleRatio t u
      =
    centeredPolePhaseRatio ((t/16)*u)
      / gammaPoleHyperbolicDenom u := by
  unfold gammaToPoleRatio centeredRadiusWeight poleRadiusWeight
  rw [gammaArchKernel_eq_inv_two_sinh hu]
  unfold centeredPolePhaseRatio gammaPoleHyperbolicDenom
  have hc : 0 < Real.cos ((t/16)*u) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hs : Real.sinh u ≠ 0 := by
    exact (Real.sinh_pos_iff.mpr hu).ne'
  have hch : Real.cosh (u/2) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp [hc.ne', hs, hch]
  ring

theorem paired_inner_phase_bounds
    {t u : ℝ}
    (ht : 0 < t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    3 * Real.pi / 64 <= (t/16)*u
      ∧ (t/16)*u <= 5 * Real.pi/64 := by
  constructor
  · have h := mul_le_mul_of_nonneg_left huLower (show 0 <= t/16 by positivity)
    field_simp [ne_of_gt ht] at h ⊢
    nlinarith [Real.pi_pos]
  · have h := mul_le_mul_of_nonneg_left huUpper (show 0 <= t/16 by positivity)
    field_simp [ne_of_gt ht] at h ⊢
    nlinarith [Real.pi_pos]

theorem paired_outer_phase_eq
    {t u : ℝ} (ht : 0 < t) :
    (t/16) * (u + Real.pi/t)
      = (t/16)*u + Real.pi/16 := by
  field_simp [ne_of_gt ht]
  ring

theorem gammaToPoleRatio_pos_on_inner_window
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    0 < gammaToPoleRatio t u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  obtain ⟨hlo,hhi⟩ := paired_inner_phase_bounds ht0 huLower huUpper
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) huLower
  have hphase :
      0 < centeredPolePhaseRatio ((t/16)*u) := by
    apply centeredPolePhaseRatio_pos
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hH : 0 < gammaPoleHyperbolicDenom u :=
    gammaPoleHyperbolicDenom_pos hu0
  rw [gammaToPoleRatio_eq_phase_div_hyperbolic
    hu0 (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]
  exact div_pos hphase hH

theorem paired_gammaToPoleRatio_strict
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    gammaToPoleRatio t u
      < gammaToPoleRatio t (u + Real.pi/t) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) huLower
  let v : ℝ := u + Real.pi/t
  have hv0 : 0 < v := by
    dsimp [v]
    positivity

  obtain ⟨hlo,hhi⟩ := paired_inner_phase_bounds ht0 huLower huUpper
  have hphase3 :
      3 * centeredPolePhaseRatio ((t/16)*u)
        < centeredPolePhaseRatio ((t/16)*u + Real.pi/16) :=
    three_phaseRatio_inner_lt_outer hlo hhi

  have hH3 :
      gammaPoleHyperbolicDenom v
        < 3 * gammaPoleHyperbolicDenom u := by
    dsimp [v]
    exact paired_gammaPoleHyperbolicDenom_lt_three ht huLower huUpper

  have hPin :
      0 < centeredPolePhaseRatio ((t/16)*u) :=
    centeredPolePhaseRatio_pos
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  have hPout :
      0 < centeredPolePhaseRatio ((t/16)*u + Real.pi/16) := by
    apply centeredPolePhaseRatio_pos
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]

  have hHin : 0 < gammaPoleHyperbolicDenom u :=
    gammaPoleHyperbolicDenom_pos hu0
  have hHout : 0 < gammaPoleHyperbolicDenom v :=
    gammaPoleHyperbolicDenom_pos hv0

  have hcross1 :
      3 * centeredPolePhaseRatio ((t/16)*u)
          * gammaPoleHyperbolicDenom u
        <
      centeredPolePhaseRatio ((t/16)*u + Real.pi/16)
          * gammaPoleHyperbolicDenom u :=
    mul_lt_mul_of_pos_right hphase3 hHin

  have hcross2 :
      centeredPolePhaseRatio ((t/16)*u)
          * gammaPoleHyperbolicDenom v
        <
      3 * centeredPolePhaseRatio ((t/16)*u)
          * gammaPoleHyperbolicDenom u := by
    exact mul_lt_mul_of_pos_left hH3 hPin

  have hcross :
      centeredPolePhaseRatio ((t/16)*u)
          * gammaPoleHyperbolicDenom v
        <
      centeredPolePhaseRatio ((t/16)*u + Real.pi/16)
          * gammaPoleHyperbolicDenom u :=
    lt_trans hcross2 hcross1

  have hinnerEq :=
    gammaToPoleRatio_eq_phase_div_hyperbolic
      (t:=t) hu0
      (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])
  have houterAngle :
      (t/16)*v = (t/16)*u + Real.pi/16 := by
    dsimp [v]
    exact paired_outer_phase_eq ht0
  have houterAngle0 : 0 <= (t/16)*v := by
    rw [houterAngle]
    nlinarith [Real.pi_pos]
  have houterAnglePi : (t/16)*v < Real.pi/2 := by
    rw [houterAngle]
    nlinarith [Real.pi_pos]
  have houterEq :=
    gammaToPoleRatio_eq_phase_div_hyperbolic
      (t:=t) hv0 houterAngle0 houterAnglePi

  rw [hinnerEq, houterEq, houterAngle]
  exact (div_lt_div_iff₀ hHin hHout).2 hcross

end Synthesis
