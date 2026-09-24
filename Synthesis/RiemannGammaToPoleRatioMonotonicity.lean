import Synthesis.RiemannGammaPairedWeightRatio
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Monotonicity of the Gamma-to-pole ratio on the canonical support

Write

    R_t(u) = A((t/16)u) / H(u),

where

    A(theta) = (1-cos theta)/cos theta,
    H(u)     = 2 sinh(u) cosh(u/2).

On the canonical positive support, theta in (0,9pi/64) and u <= pi/8.

The logarithmic growth is separated with room to spare:

    2 A(theta) <= theta A'(theta),
    u H'(u) < (3/2) H(u).

Since 2 > 3/2 and theta=(t/16)u, R_t'(u)>0.

This upgrades the paired-coordinate comparison to strict monotonicity across the
whole positive support; therefore every outer-window Gamma/pole ratio is larger
than every inner-window ratio.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def phaseRatioDerivValue (theta : ℝ) : ℝ :=
  Real.sin theta / Real.cos theta ^ 2

def gammaPoleHyperbolicDerivValue (u : ℝ) : ℝ :=
  2 * Real.cosh u * Real.cosh (u/2)
    + Real.sinh u * Real.sinh (u/2)

theorem centeredPolePhaseRatio_hasDerivAt
    {theta : ℝ} (hc : Real.cos theta ≠ 0) :
    HasDerivAt centeredPolePhaseRatio
      (phaseRatioDerivValue theta) theta := by
  unfold centeredPolePhaseRatio phaseRatioDerivValue
  have hnum :
      HasDerivAt (fun x : ℝ => 1 - Real.cos x) (Real.sin theta) theta := by
    convert (hasDerivAt_const theta 1).sub (Real.hasDerivAt_cos theta) using 1 <;> ring
  have hden := Real.hasDerivAt_cos theta
  have hdiv := hnum.div hden hc
  convert hdiv using 1 <;> field_simp [hc] <;> ring

theorem gammaPoleHyperbolicDenom_hasDerivAt (u : ℝ) :
    HasDerivAt gammaPoleHyperbolicDenom
      (gammaPoleHyperbolicDerivValue u) u := by
  unfold gammaPoleHyperbolicDenom gammaPoleHyperbolicDerivValue
  have hs := Real.hasDerivAt_sinh u
  have hc : HasDerivAt (fun x : ℝ => Real.cosh (x/2))
      ((1/2 : ℝ) * Real.sinh (u/2)) u := by
    convert (Real.hasDerivAt_cosh (u/2)).comp u
      ((hasDerivAt_id u).div_const 2) using 1 <;> ring
  have hp := (hs.mul hc).const_mul 2
  convert hp using 1 <;> ring

theorem phaseRatio_two_le_log_numerator
    {theta : ℝ}
    (htheta0 : 0 < theta)
    (hthetaPi : theta < Real.pi/2) :
    2 * centeredPolePhaseRatio theta
      <= theta * phaseRatioDerivValue theta := by
  have hc : 0 < Real.cos theta := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hs : 0 < Real.sin theta := by
    exact Real.sin_pos_of_pos_of_lt_pi htheta0
      (by linarith [Real.pi_pos])
  have hsinle : Real.sin theta <= theta :=
    Real.sin_le htheta0.le
  have hsq :
      Real.sin theta ^ 2
        = (1 - Real.cos theta) * (1 + Real.cos theta) := by
    have h := Real.sin_sq_add_cos_sq theta
    nlinarith
  have hcosle : Real.cos theta <= 1 := Real.cos_le_one theta
  have hbase :
      2 * Real.cos theta * (1 - Real.cos theta)
        <= theta * Real.sin theta := by
    have h1 :
        2 * Real.cos theta * (1 - Real.cos theta)
          <= Real.sin theta ^ 2 := by
      rw [hsq]
      have hnonneg : 0 <= 1 - Real.cos theta := by linarith
      nlinarith
    have h2 : Real.sin theta ^ 2 <= theta * Real.sin theta := by
      exact mul_le_mul_of_nonneg_right hsinle hs.le
    exact le_trans h1 h2
  unfold centeredPolePhaseRatio phaseRatioDerivValue
  have hc2 : 0 < Real.cos theta ^ 2 := sq_pos_of_pos hc
  rw [div_le_div_iff₀ hc hc2]
  nlinarith

theorem hyperbolic_log_numerator_lt_three_halves
    {u : ℝ}
    (hu0 : 0 < u)
    (hu : u <= Real.pi/8) :
    u * gammaPoleHyperbolicDerivValue u
      < (3/2 : ℝ) * gammaPoleHyperbolicDenom u := by
  have hupi : u < 1/2 := by
    nlinarith [Real.pi_lt_four]
  have huSq : u^2 < 1/4 := by nlinarith [sq_nonneg u]
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hcu : 0 < Real.cosh u := Real.cosh_pos u
  have hch : 0 < Real.cosh (u/2) := Real.cosh_pos _
  have hshu : 0 <= Real.sinh (u/2) :=
    Real.sinh_nonneg_iff.mpr (by linarith)
  have hsinhLower : u <= Real.sinh u :=
    self_le_sinh_of_nonneg hu0.le
  have hsinhHalfUpper :
      Real.sinh (u/2) <= (u/2) * Real.cosh (u/2) :=
    sinh_le_mul_cosh_of_nonneg (by linarith)
  have hcoshBound :
      Real.cosh u <= Real.exp (1/8 : ℝ) := by
    have hc := Real.cosh_le_exp_half_sq u
    have hexp : Real.exp (u^2/2) <= Real.exp (1/8 : ℝ) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact le_trans hc hexp
  have hexpRat : Real.exp (1/8 : ℝ) <= 17/15 := by
    have h := Real.exp_le_two_add_div_two_sub
      (x := (1/8 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hcoshRat : Real.cosh u <= 17/15 :=
    le_trans hcoshBound hexpRat

  unfold gammaPoleHyperbolicDerivValue gammaPoleHyperbolicDenom
  have hfirst :
      u * (2 * Real.cosh u * Real.cosh (u/2))
        <= (17/15 : ℝ) *
          (2 * Real.sinh u * Real.cosh (u/2)) := by
    have hmul :
        u * Real.cosh u
          <= (17/15 : ℝ) * Real.sinh u := by
      calc
        u * Real.cosh u
            <= Real.sinh u * Real.cosh u :=
          mul_le_mul_of_nonneg_right hsinhLower hcu.le
        _ <= Real.sinh u * (17/15 : ℝ) :=
          mul_le_mul_of_nonneg_left hcoshRat hsu.le
        _ = _ := by ring
    nlinarith [hch.le]
  have hsecond :
      u * (Real.sinh u * Real.sinh (u/2))
        <= (1/8 : ℝ) *
          (2 * Real.sinh u * Real.cosh (u/2)) := by
    have hh :
        u * Real.sinh (u/2)
          <= (1/4 : ℝ) * Real.cosh (u/2) := by
      have hm := mul_le_mul_of_nonneg_left hsinhHalfUpper hu0.le
      nlinarith [huSq, hch.le]
    nlinarith [hsu.le, hch.le]
  nlinarith

theorem gammaToPoleRatio_hasDerivAt_pos
    {t u : ℝ}
    (ht : 18 <= t)
    (hu0 : 0 < u)
    (hu : u <= 9 * Real.pi/(4*t)) :
    0 < deriv (gammaToPoleRatio t) u := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  let theta : ℝ := (t/16)*u
  have htheta0 : 0 < theta := by
    dsimp [theta]
    positivity
  have hthetaUpper : theta <= 9 * Real.pi/64 := by
    dsimp [theta]
    have hm := mul_le_mul_of_nonneg_left hu
      (show 0 <= t/16 by positivity)
    field_simp [ne_of_gt ht0] at hm ⊢
    nlinarith [Real.pi_pos]
  have hthetaPi : theta < Real.pi/2 := by
    nlinarith [Real.pi_pos]
  have huPi : u <= Real.pi/8 := by
    have h9 : 9 * Real.pi/(4*t) <= Real.pi/8 := by
      rw [div_le_iff₀ ht0]
      nlinarith [Real.pi_pos]
    exact le_trans hu h9

  have hphase :=
    phaseRatio_two_le_log_numerator htheta0 hthetaPi
  have hhyper :=
    hyperbolic_log_numerator_lt_three_halves hu0 huPi

  have hc : 0 < Real.cos theta := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hA : 0 < centeredPolePhaseRatio theta :=
    centeredPolePhaseRatio_pos htheta0 hthetaPi
  have hH : 0 < gammaPoleHyperbolicDenom u :=
    gammaPoleHyperbolicDenom_pos hu0

  have hthetaEq : theta = (t/16)*u := rfl
  have hcross :
      (t/16) * phaseRatioDerivValue theta *
          gammaPoleHyperbolicDenom u
        >
      centeredPolePhaseRatio theta *
          gammaPoleHyperbolicDerivValue u := by
    have hphaseScaled :
        2 * centeredPolePhaseRatio theta * gammaPoleHyperbolicDenom u
          <= theta * phaseRatioDerivValue theta *
              gammaPoleHyperbolicDenom u :=
      mul_le_mul_of_nonneg_right hphase hH.le
    have hhyperScaled :
        u * centeredPolePhaseRatio theta *
            gammaPoleHyperbolicDerivValue u
          <
        (3/2 : ℝ) * centeredPolePhaseRatio theta *
            gammaPoleHyperbolicDenom u := by
      exact mul_lt_mul_of_pos_left hhyper hA
    have huPos := hu0
    rw [hthetaEq] at hphaseScaled
    nlinarith

  have hAder :=
    centeredPolePhaseRatio_hasDerivAt (theta:=theta) hc.ne'
  have hinner :
      HasDerivAt (fun x : ℝ => centeredPolePhaseRatio ((t/16)*x))
        ((t/16) * phaseRatioDerivValue theta) u := by
    have hlin : HasDerivAt (fun x : ℝ => (t/16)*x) (t/16) u := by
      simpa using (hasDerivAt_id u).const_mul (t/16)
    simpa [theta, mul_comm] using hAder.comp u hlin
  have hHder := gammaPoleHyperbolicDenom_hasDerivAt u
  have hquot := hinner.div hHder hH.ne'
  have hrewrite :
      (fun x : ℝ =>
        centeredPolePhaseRatio ((t/16)*x) /
          gammaPoleHyperbolicDenom x)
        = gammaToPoleRatio t := by
    funext x
    by_cases hx : 0 < x
    · have hangle0 : 0 <= (t/16)*x := by positivity
      have hanglePi : (t/16)*x < Real.pi/2 := by
        by_cases hxcan : x <= 9*Real.pi/(4*t)
        · have hm := mul_le_mul_of_nonneg_left hxcan
            (show 0 <= t/16 by positivity)
          field_simp [ne_of_gt ht0] at hm
          nlinarith [Real.pi_pos]
        · unfold gammaToPoleRatio centeredPolePhaseRatio
          rfl
      symm
      exact gammaToPoleRatio_eq_phase_div_hyperbolic
        hx hangle0 hanglePi
    · unfold gammaToPoleRatio centeredPolePhaseRatio
      rfl
  have hd :
      deriv (gammaToPoleRatio t) u
        =
      (((t/16) * phaseRatioDerivValue theta) *
          gammaPoleHyperbolicDenom u
        - centeredPolePhaseRatio theta *
          gammaPoleHyperbolicDerivValue u)
        / gammaPoleHyperbolicDenom u ^ 2 := by
    rw [← hrewrite]
    rw [hquot.deriv]
    rfl
  rw [hd]
  exact div_pos (sub_pos.mpr hcross) (sq_pos_of_pos hH)

theorem gammaToPoleRatio_strictMonoOn_canonical
    {t x y : ℝ}
    (ht : 18 <= t)
    (hx : 0 < x)
    (hxy : x < y)
    (hy : y <= 9 * Real.pi/(4*t)) :
    gammaToPoleRatio t x < gammaToPoleRatio t y := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hy0 : 0 < y := lt_trans hx hxy
  have hmono : StrictMonoOn (gammaToPoleRatio t) (Set.Icc x y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc x y)
    · intro z hz
      have hz0 : 0 < z := lt_of_lt_of_le hx hz.1
      have hzcan : z <= 9*Real.pi/(4*t) := le_trans hz.2 hy
      have hangle0 : 0 <= (t/16)*z := by positivity
      have hanglePi : (t/16)*z < Real.pi/2 := by
        have hm := mul_le_mul_of_nonneg_left hzcan
          (show 0 <= t/16 by positivity)
        field_simp [ne_of_gt ht0] at hm
        nlinarith [Real.pi_pos]
      have heq :=
        gammaToPoleRatio_eq_phase_div_hyperbolic
          (t:=t) hz0 hangle0 hanglePi
      rw [heq]
      fun_prop
    · intro z hz
      rw [interior_Icc] at hz
      exact gammaToPoleRatio_hasDerivAt_pos ht hz.1
        (le_trans hz.2.le hy)
  exact hmono (by exact ⟨le_rfl, hxy.le⟩)
    (by exact ⟨hxy.le, le_rfl⟩) hxy

end Synthesis
