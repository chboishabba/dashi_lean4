import Synthesis.RiemannGammaArchimedeanKernelGeometry
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Hyperbolic growth across paired canonical taper windows

For the Gamma-to-pole ratio the hyperbolic denominator is

    H(u) = 2 sinh(u) cosh(u/2).

At paired bump coordinates,

    u_out = u_in + pi/t,

with u_in in [3pi/(4t), 5pi/(4t)] and t>=18.

This file proves

    H(u_out) < 3 H(u_in).

Combined with the >3 phase gain, this gives the strict paired increase of the
Gamma-to-pole weight ratio.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

theorem sinh_le_mul_cosh_of_nonneg {x : ℝ} (hx : 0 <= x) :
    Real.sinh x <= x * Real.cosh x := by
  let f : ℝ → ℝ := fun y => y * Real.cosh y - Real.sinh y
  have hmono : MonotoneOn f (Set.Ici (0:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by
      dsimp [f]
      fun_prop)
    · rw [interior_Ici]
      intro y hy
      exact (by
        dsimp [f]
        fun_prop : DifferentiableAt ℝ f y)
    · rw [interior_Ici]
      intro y hy
      have hy0 : 0 <= y := le_of_lt hy
      have hd :
          deriv f y = y * Real.sinh y := by
        have hprod :=
          (hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)
        have hsub := hprod.sub (Real.hasDerivAt_sinh y)
        rw [hsub.deriv]
        dsimp [f]
        ring
      rw [hd]
      exact mul_nonneg hy0 (Real.sinh_nonneg_iff.mpr hy0)
  have h0 : f 0 = 0 := by simp [f]
  have h := hmono (by simp) hx
  rw [h0] at h
  dsimp [f] at h
  linarith

theorem self_le_sinh_of_nonneg {x : ℝ} (hx : 0 <= x) :
    x <= Real.sinh x := by
  exact Real.self_le_sinh_iff.mpr hx

def gammaPoleHyperbolicDenom (u : ℝ) : ℝ :=
  2 * Real.sinh u * Real.cosh (u/2)

theorem gammaPoleHyperbolicDenom_pos {u : ℝ} (hu : 0 < u) :
    0 < gammaPoleHyperbolicDenom u := by
  unfold gammaPoleHyperbolicDenom
  positivity

theorem canonical_paired_outer_le_pi_div_eight
    {t u : ℝ}
    (ht : 18 <= t)
    (huUpper : u <= 5 * Real.pi / (4*t)) :
    u + Real.pi/t <= Real.pi/8 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hv :
      u + Real.pi/t <= 9 * Real.pi/(4*t) := by
    calc
      u + Real.pi/t
          <= 5*Real.pi/(4*t) + Real.pi/t :=
        add_le_add_right huUpper _
      _ = 9*Real.pi/(4*t) := by field_simp [ne_of_gt ht0]; ring
  have h9 : 9 * Real.pi/(4*t) <= Real.pi/8 := by
    rw [div_le_iff₀ ht0]
    nlinarith [Real.pi_pos]
  exact le_trans hv h9

theorem cosh_mul_cosh_half_lt_nine_sevenths
    {v : ℝ}
    (hv0 : 0 <= v)
    (hv : v <= Real.pi/8) :
    Real.cosh v * Real.cosh (v/2) < 9/7 := by
  have hvHalf0 : 0 <= v/2 := by linarith
  have hcv :
      Real.cosh v <= Real.exp (v^2/2) :=
    Real.cosh_le_exp_half_sq v
  have hch :
      Real.cosh (v/2) <= Real.exp ((v/2)^2/2) :=
    Real.cosh_le_exp_half_sq (v/2)
  have hvLe : v <= 1/2 := by
    have hp4 := Real.pi_lt_four
    nlinarith
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
  have h69 : (69/59 : ℝ) < 9/7 := by norm_num
  exact lt_of_le_of_lt (le_trans hprod (le_trans hmono hrat)) h69

theorem paired_outer_over_inner_le_seven_thirds
    {t u : ℝ}
    (ht : 0 < t)
    (huLower : 3 * Real.pi/(4*t) <= u) :
    u + Real.pi/t <= (7/3 : ℝ) * u := by
  have hpiTerm : Real.pi/t <= (4/3 : ℝ) * u := by
    have h := mul_le_mul_of_nonneg_left huLower (show (0:ℝ) <= 4/3 by norm_num)
    field_simp [ne_of_gt ht] at h ⊢
    nlinarith [Real.pi_pos]
  linarith

theorem paired_gammaPoleHyperbolicDenom_lt_three
    {t u : ℝ}
    (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    gammaPoleHyperbolicDenom (u + Real.pi/t)
      < 3 * gammaPoleHyperbolicDenom u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity) huLower
  let v : ℝ := u + Real.pi/t
  have hv0 : 0 < v := by
    dsimp [v]
    positivity
  have hvPi : v <= Real.pi/8 := by
    dsimp [v]
    exact canonical_paired_outer_le_pi_div_eight ht huUpper
  have hratio :
      v <= (7/3 : ℝ) * u := by
    dsimp [v]
    exact paired_outer_over_inner_le_seven_thirds ht0 huLower
  have hsinhV :
      Real.sinh v <= v * Real.cosh v :=
    sinh_le_mul_cosh_of_nonneg hv0.le
  have hsinhU :
      u <= Real.sinh u :=
    self_le_sinh_of_nonneg hu0.le
  have hcoshU : 1 <= Real.cosh (u/2) := Real.one_le_cosh _
  have hcoshPair :
      Real.cosh v * Real.cosh (v/2) < 9/7 :=
    cosh_mul_cosh_half_lt_nine_sevenths hv0.le hvPi
  have hupper :
      gammaPoleHyperbolicDenom v
        <= 2 * v * (Real.cosh v * Real.cosh (v/2)) := by
    unfold gammaPoleHyperbolicDenom
    have hcv : 0 <= Real.cosh (v/2) := (Real.cosh_pos _).le
    nlinarith
  have hlower :
      2 * u <= gammaPoleHyperbolicDenom u := by
    unfold gammaPoleHyperbolicDenom
    have hsu : 0 <= Real.sinh u := (Real.sinh_pos_iff.mpr hu0).le
    nlinarith
  have hstrict :
      2 * v * (Real.cosh v * Real.cosh (v/2))
        < 6 * u := by
    have huPos : 0 < u := hu0
    nlinarith
  dsimp [v] at *
  linarith

end Synthesis
