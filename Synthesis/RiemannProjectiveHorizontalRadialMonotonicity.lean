import Synthesis.RiemannProjectiveMonotoneWeightCovariance
import Synthesis.RiemannGammaPairedHyperbolicGrowth
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Radial monotonicity of the horizontal projective weight

For

  H_alpha(x) = (cosh(alpha*x)-1)/alpha^2

with the continuous extension H_0(x)=x^2/2, define

  W_{alpha,delta}(x) = H_alpha(x) cos(delta*x).

The key differential inequality is

  x H_alpha'(x) >= 2 H_alpha(x),    x >= 0.

It follows from

  2(cosh z-1) <= z sinh z.

Hence W is strictly increasing on x>0 whenever

  2 cos(y) > y sin(y),   y=|delta|x.

A simple Taylor bound proves the latter throughout 0 <= y <= pi/4.
Therefore W is strictly increasing in |x| on every interval satisfying

  |delta| * Lambda <= pi/4.

This is the analytic sign window consumed by the monotone-weight projective
covariance compiler.
-/

noncomputable section

open Set
open scoped Real

namespace Synthesis

def coshMinusOneDivSqDeriv (alpha x : ℝ) : ℝ :=
  if alpha = 0 then x else Real.sinh (alpha*x) / alpha

theorem hasDerivAt_coshMinusOneDivSq
    (alpha x : ℝ) :
    HasDerivAt (coshMinusOneDivSq alpha)
      (coshMinusOneDivSqDeriv alpha x) x := by
  by_cases ha : alpha = 0
  · subst alpha
    simp only [coshMinusOneDivSq, coshMinusOneDivSqDeriv, if_pos rfl]
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;> ring
  · simp only [coshMinusOneDivSq, coshMinusOneDivSqDeriv, if_neg ha]
    have hlin :
        HasDerivAt (fun y : ℝ => alpha*y) alpha x := by
      simpa using (hasDerivAt_id x).const_mul alpha
    have hc :
        HasDerivAt (fun y : ℝ => Real.cosh (alpha*y))
          (alpha * Real.sinh (alpha*x)) x := by
      convert (Real.hasDerivAt_cosh (alpha*x)).comp x hlin using 1 <;> ring
    have hs :=
      hc.sub (hasDerivAt_const x (1:ℝ))
    have hd := hs.div_const (alpha^2)
    convert hd using 1 <;> field_simp [ha] <;> ring

theorem deriv_coshMinusOneDivSq
    (alpha x : ℝ) :
    deriv (coshMinusOneDivSq alpha) x
      = coshMinusOneDivSqDeriv alpha x :=
  (hasDerivAt_coshMinusOneDivSq alpha x).deriv

theorem two_cosh_sub_one_le_mul_sinh_of_nonneg
    {z : ℝ} (hz : 0 ≤ z) :
    2 * (Real.cosh z - 1) ≤ z * Real.sinh z := by
  let f : ℝ → ℝ := fun y =>
    y * Real.sinh y - 2 * (Real.cosh y - 1)
  have hmono : MonotoneOn f (Set.Ici (0:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by
      dsimp [f]
      fun_prop)
    · rw [interior_Ici]
      intro y hy
      dsimp [f]
      fun_prop
    · rw [interior_Ici]
      intro y hy
      have hy0 : 0 ≤ y := le_of_lt hy
      have hderiv :
          deriv f y = y * Real.cosh y - Real.sinh y := by
        have hp := (hasDerivAt_id y).mul (Real.hasDerivAt_sinh y)
        have hsub :=
          hp.sub ((Real.hasDerivAt_cosh y).sub (hasDerivAt_const y 1)).const_mul 2
        rw [hsub.deriv]
        dsimp [f]
        ring
      rw [hderiv]
      exact sub_nonneg.mpr (sinh_le_mul_cosh_of_nonneg hy0)
  have h0 : f 0 = 0 := by simp [f]
  have h := hmono (by simp) hz
  rw [h0] at h
  dsimp [f] at h
  linarith

theorem two_cosh_sub_one_le_mul_sinh (z : ℝ) :
    2 * (Real.cosh z - 1) ≤ z * Real.sinh z := by
  by_cases hz : 0 ≤ z
  · exact two_cosh_sub_one_le_mul_sinh_of_nonneg hz
  · have h :=
      two_cosh_sub_one_le_mul_sinh_of_nonneg
        (show 0 ≤ -z by linarith)
    simpa [Real.cosh_neg, Real.sinh_neg] using h

theorem two_coshMinusOneDivSq_le_x_mul_deriv
    (alpha : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    2 * coshMinusOneDivSq alpha x
      ≤ x * coshMinusOneDivSqDeriv alpha x := by
  by_cases ha : alpha = 0
  · subst alpha
    simp [coshMinusOneDivSq, coshMinusOneDivSqDeriv]
    nlinarith
  · have hbase := two_cosh_sub_one_le_mul_sinh (alpha*x)
    have ha2 : 0 < alpha^2 := sq_pos_of_ne_zero ha
    simp only [coshMinusOneDivSq, coshMinusOneDivSqDeriv, if_neg ha]
    have hrewrite :
        x * (Real.sinh (alpha*x) / alpha)
          =
        ((alpha*x) * Real.sinh (alpha*x)) / alpha^2 := by
      field_simp [ha]
      ring
    rw [hrewrite]
    rw [div_le_div_iff_of_pos_right ha2]
    simpa [mul_assoc] using hbase

theorem coshMinusOneDivSq_pos
    (alpha : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < coshMinusOneDivSq alpha x := by
  by_cases ha : alpha = 0
  · subst alpha
    simp [coshMinusOneDivSq]
    positivity
  · have hax : alpha*x ≠ 0 := mul_ne_zero ha (ne_of_gt hx)
    have hc : 1 < Real.cosh (alpha*x) :=
      Real.one_lt_cosh.mpr hax
    simp only [coshMinusOneDivSq, if_neg ha]
    exact div_pos (sub_pos.mpr hc) (sq_pos_of_ne_zero ha)

def horizontalRadialWeight
    (alpha delta x : ℝ) : ℝ :=
  coshMinusOneDivSq alpha x * Real.cos (delta*x)

theorem horizontalRadialWeight_even
    (alpha delta x : ℝ) :
    horizontalRadialWeight alpha delta (-x)
      = horizontalRadialWeight alpha delta x := by
  unfold horizontalRadialWeight coshMinusOneDivSq
  by_cases ha : alpha = 0
  · simp [ha, Real.cos_neg]
  · simp [ha, Real.cosh_neg, Real.cos_neg]
    ring

theorem horizontalRadialWeight_continuous
    (alpha delta : ℝ) :
    Continuous (horizontalRadialWeight alpha delta) := by
  unfold horizontalRadialWeight
  exact (coshMinusOneDivSq_continuous_in_v alpha).mul (by fun_prop)

def horizontalRadialWeightDeriv
    (alpha delta x : ℝ) : ℝ :=
  coshMinusOneDivSqDeriv alpha x * Real.cos (delta*x)
    - coshMinusOneDivSq alpha x * (delta * Real.sin (delta*x))

theorem hasDerivAt_horizontalRadialWeight
    (alpha delta x : ℝ) :
    HasDerivAt (horizontalRadialWeight alpha delta)
      (horizontalRadialWeightDeriv alpha delta x) x := by
  have hH := hasDerivAt_coshMinusOneDivSq alpha x
  have hlin :
      HasDerivAt (fun y : ℝ => delta*y) delta x := by
    simpa using (hasDerivAt_id x).const_mul delta
  have hc :
      HasDerivAt (fun y : ℝ => Real.cos (delta*y))
        (-delta * Real.sin (delta*x)) x := by
    convert (Real.hasDerivAt_cos (delta*x)).comp x hlin using 1 <;> ring
  have hp := hH.mul hc
  convert hp using 1 <;>
    simp [horizontalRadialWeight, horizontalRadialWeightDeriv] <;> ring

theorem two_cos_sub_y_sin_pos
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ Real.pi/4) :
    0 < 2*Real.cos y - y*Real.sin y := by
  have hpi4 : Real.pi/4 < 1 := by
    nlinarith [Real.pi_lt_four]
  have hy1 : y < 1 := lt_of_le_of_lt hy hpi4
  have hsin : Real.sin y ≤ y := Real.sin_le hy0
  have hcos : 1-y^2/2 ≤ Real.cos y :=
    Real.one_sub_sq_div_two_le_cos y
  have hy2 : y^2 < 1 := by nlinarith [sq_nonneg y]
  have hysin : y*Real.sin y ≤ y^2 :=
    mul_le_mul_of_nonneg_left hsin hy0
  nlinarith

theorem horizontalRadialWeight_deriv_pos_of_phase
    {alpha delta x : ℝ}
    (hx : 0 < x)
    (hdelta : 0 ≤ delta)
    (hphase : delta*x ≤ Real.pi/4) :
    0 < horizontalRadialWeightDeriv alpha delta x := by
  have hy0 : 0 ≤ delta*x := mul_nonneg hdelta hx.le
  have hphasePos :=
    two_cos_sub_y_sin_pos hy0 hphase
  have hcos : 0 < Real.cos (delta*x) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hHpos := coshMinusOneDivSq_pos alpha hx
  have hgrowth :=
    two_coshMinusOneDivSq_le_x_mul_deriv alpha hx.le
  have hgrowthCos :
      2*coshMinusOneDivSq alpha x*Real.cos (delta*x)
        ≤
      x*coshMinusOneDivSqDeriv alpha x*Real.cos (delta*x) := by
    exact mul_le_mul_of_nonneg_right hgrowth hcos.le
  have hmargin :
      0 <
      coshMinusOneDivSq alpha x *
        (2*Real.cos (delta*x)
          - (delta*x)*Real.sin (delta*x)) :=
    mul_pos hHpos hphasePos
  unfold horizontalRadialWeightDeriv
  have hx0 : 0 < x := hx
  nlinarith

theorem horizontalRadialWeight_strictMonoOn_nonneg
    {alpha delta Lambda : ℝ}
    (hdelta : 0 ≤ delta)
    (hLambda : 0 ≤ Lambda)
    (hphase : delta*Lambda ≤ Real.pi/4) :
    StrictMonoOn (horizontalRadialWeight alpha delta) (Set.Icc 0 Lambda) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 Lambda)
  · exact (horizontalRadialWeight_continuous alpha delta).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hdx : delta*x ≤ Real.pi/4 := by
      have := mul_le_mul_of_nonneg_left hx.2.le hdelta
      exact le_trans this hphase
    rw [(hasDerivAt_horizontalRadialWeight alpha delta x).deriv]
    exact horizontalRadialWeight_deriv_pos_of_phase hx.1 hdelta hdx

theorem horizontalRadialWeight_abs_delta
    (alpha delta x : ℝ) :
    horizontalRadialWeight alpha |delta| x
      = horizontalRadialWeight alpha delta x := by
  unfold horizontalRadialWeight
  congr 1
  rw [← Real.cos_abs (delta*x), abs_mul]
  congr 2
  simp

/--
Strict radial order on a symmetric support interval.
-/
theorem horizontalRadialWeight_strict_of_abs_lt
    {alpha delta Lambda u v : ℝ}
    (hLambda : 0 ≤ Lambda)
    (hu : |u| ≤ Lambda)
    (hv : |v| ≤ Lambda)
    (hphase : |delta|*Lambda ≤ Real.pi/4)
    (huv : |u| < |v|) :
    horizontalRadialWeight alpha delta u
      < horizontalRadialWeight alpha delta v := by
  have hm :=
    horizontalRadialWeight_strictMonoOn_nonneg
      (alpha:=alpha) (delta:=|delta|) (Lambda:=Lambda)
      (abs_nonneg delta) hLambda hphase
  have huI : |u| ∈ Set.Icc (0:ℝ) Lambda :=
    ⟨abs_nonneg u,hu⟩
  have hvI : |v| ∈ Set.Icc (0:ℝ) Lambda :=
    ⟨abs_nonneg v,hv⟩
  have h := hm huI hvI huv
  rw [horizontalRadialWeight_abs_delta,
      horizontalRadialWeight_abs_delta] at h
  rw [← horizontalRadialWeight_even alpha delta u,
      ← horizontalRadialWeight_even alpha delta v]
  simpa [abs_eq_self.mpr (abs_nonneg u),
    abs_eq_self.mpr (abs_nonneg v)] using h

theorem horizontalRadialWeight_mono_of_abs_le
    {alpha delta Lambda u v : ℝ}
    (hLambda : 0 ≤ Lambda)
    (hu : |u| ≤ Lambda)
    (hv : |v| ≤ Lambda)
    (hphase : |delta|*Lambda ≤ Real.pi/4)
    (huv : |u| ≤ |v|) :
    horizontalRadialWeight alpha delta u
      ≤ horizontalRadialWeight alpha delta v := by
  rcases lt_or_eq_of_le huv with hlt | heq
  · exact (horizontalRadialWeight_strict_of_abs_lt
      hLambda hu hv hphase hlt).le
  · have huabs :
      horizontalRadialWeight alpha delta u
        = horizontalRadialWeight alpha delta |u| := by
      have := horizontalRadialWeight_even alpha delta u
      by_cases hs : 0 ≤ u
      · simp [abs_of_nonneg hs]
      · rw [abs_of_neg (lt_of_not_ge hs)]
        simpa using this.symm
    have hvabs :
      horizontalRadialWeight alpha delta v
        = horizontalRadialWeight alpha delta |v| := by
      by_cases hs : 0 ≤ v
      · simp [abs_of_nonneg hs]
      · rw [abs_of_neg (lt_of_not_ge hs)]
        simpa using (horizontalRadialWeight_even alpha delta v).symm
    rw [huabs,hvabs,heq]

end Synthesis
