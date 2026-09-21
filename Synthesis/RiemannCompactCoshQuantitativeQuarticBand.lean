import Synthesis.RiemannFourthOrderQuantitativeSignCompiler
import Synthesis.RiemannCompactCoshFourthDerivative

/-!
# Quantitative quartic band for compact hyperbolic transforms

For a continuous compactly-supported profile P define

  H(a) = integral P(u) cosh(a u) du.

Its fifth derivative is

  H5(a) = integral P(u) sinh(a u) u^5.

On |a|<=1,

  |H5(a)| <= K(P),

where

  K(P) = integral |P(u)| cosh(|u|) |u|^5 du.

Hence H4 is K(P)-Lipschitz from zero on the unit interval.

If

  M0(P)=0, M2(P)=0, M4(P)<=-m<0,

the quantitative fourth-order compiler yields the explicit punctured band

  0<|a|<min(1,m/(2(K(P)+1)))  ->  H(a)<0.

This is the quantitative replacement for the earlier existential quartic target
band.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def compactCoshD5 (P : ℝ -> ℝ) (a : ℝ) : ℝ :=
  ∫ u : ℝ, P u * Real.sinh (a*u) * u^5

def compactCoshFourthLipschitzConstant
    (P : ℝ -> ℝ) : ℝ :=
  ∫ u : ℝ, |P u| * Real.cosh |u| * |u|^5

theorem compactCoshFourthLipschitzConstant_nonneg
    (P : ℝ -> ℝ) :
    0 <= compactCoshFourthLipschitzConstant P := by
  unfold compactCoshFourthLipschitzConstant
  positivity

theorem compactCoshFourthLipschitzMajorant_integrable
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Integrable
      (fun u : ℝ => |P u| * Real.cosh |u| * |u|^5) := by
  exact
    ((hP.abs.mul (by fun_prop)).mul (continuous_abs.pow 5))
      .integrable_of_hasCompactSupport
        ((hPc.abs.mul_right).mul_right)

theorem compactCoshD4_hasDerivAt_D5
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (a0 : ℝ) :
    HasDerivAt (compactCoshD4 P) (compactCoshD5 P a0) a0 := by
  let F : ℝ -> ℝ -> ℝ := fun a u =>
    P u * Real.cosh (a*u) * u^4
  let F' : ℝ -> ℝ -> ℝ := fun a u =>
    P u * Real.sinh (a*u) * u^5
  let bound : ℝ -> ℝ := fun u =>
    |P u| * Real.cosh ((|a0|+1)*|u|) * |u|^5
  let s : Set ℝ := Icc (a0-1) (a0+1)
  have ha0 : a0 ∈ interior s := by
    dsimp [s]
    rw [interior_Icc]
    constructor <;> linarith
  have hFmeas :
      ∀ᶠ a in 𝓝 a0, AEStronglyMeasurable (F a) volume := by
    filter_upwards with a
    exact (by dsimp [F]; fun_prop : Continuous (F a)).aestronglyMeasurable
  have hFint : Integrable (F a0) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hF'meas : AEStronglyMeasurable (F' a0) volume := by
    exact (by dsimp [F']; fun_prop : Continuous (F' a0)).aestronglyMeasurable
  have hbound : Integrable bound volume := by
    exact
      ((hP.abs.mul (by fun_prop)).mul (continuous_abs.pow 5))
        .integrable_of_hasCompactSupport
          ((hPc.abs.mul_right).mul_right)
  have hderiv :
      ∀ᵐ u ∂volume, ∀ a ∈ s,
        HasDerivAt (F · u) (F' a u) a := by
    filter_upwards with u
    intro a ha
    dsimp [F,F']
    fun_prop
  have hdom :
      ∀ᵐ u ∂volume, ∀ a ∈ s,
        ‖F' a u‖ <= bound u := by
    filter_upwards with u
    intro a ha
    dsimp [F',bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have hxa : |a| <= |a0|+1 := by
      have hdiff : |a-a0| <= 1 := by
        rw [abs_le]
        constructor <;> linarith [ha.1,ha.2]
      calc
        |a| = |(a-a0)+a0| := by ring_nf
        _ <= |a-a0|+|a0| := abs_add _ _
        _ <= |a0|+1 := by linarith
    rw [Real.abs_sinh]
    have hs :
        Real.sinh |a*u| <= Real.cosh |a*u| :=
      (Real.sinh_lt_cosh).le
    have hc :
        Real.cosh |a*u|
          <= Real.cosh ((|a0|+1)*|u|) := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg (abs_nonneg (a*u)),
          abs_of_nonneg (by positivity :
            0 <= (|a0|+1)*|u|),
          abs_mul]
      exact mul_le_mul_of_nonneg_right hxa (abs_nonneg u)
    nlinarith [abs_nonneg (P u), abs_nonneg u,
      Real.cosh_pos ((|a0|+1)*|u|)]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ:=volume) (F:=F) (x₀:=a0)
      (s:=s) (bound:=bound)
      ha0 hFmeas hFint hF'meas hdom hbound hderiv
  simpa [compactCoshD4,compactCoshD5,F,F'] using h.2

theorem compactCoshD5_abs_le_fifthEnvelope
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    {a : ℝ}
    (ha : |a| <= 1) :
    |compactCoshD5 P a|
      <= compactCoshFourthLipschitzConstant P := by
  have hi :
      Integrable
        (fun u : ℝ => P u * Real.sinh (a*u) * u^5) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) ((hPc.mul_right).mul_right)
  have hmaj :=
    compactCoshFourthLipschitzMajorant_integrable hP hPc
  unfold compactCoshD5 compactCoshFourthLipschitzConstant
  calc
    |∫ u : ℝ, P u * Real.sinh (a*u) * u^5|
      <=
    ∫ u : ℝ, |P u * Real.sinh (a*u) * u^5| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ u : ℝ, |P u| * Real.cosh |u| * |u|^5 := by
      apply integral_mono hi.abs hmaj
      intro u
      rw [abs_mul,abs_mul,abs_pow,Real.abs_sinh]
      have hau : |a*u| <= |u| := by
        rw [abs_mul]
        nlinarith [abs_nonneg u]
      have hs : Real.sinh |a*u| <= Real.cosh |a*u| :=
        (Real.sinh_lt_cosh).le
      have hc : Real.cosh |a*u| <= Real.cosh |u| := by
        rw [Real.cosh_le_cosh]
        simpa [abs_of_nonneg (abs_nonneg (a*u)),
          abs_of_nonneg (abs_nonneg u)] using hau
      nlinarith [abs_nonneg (P u), abs_nonneg u,
        Real.cosh_pos |u|]

/--
The fourth derivative is Lipschitz from zero on the unit parameter interval,
with the explicit fifth-moment envelope.
-/
theorem compactCoshD4_sub_zero_abs_le
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    {a : ℝ}
    (ha : |a| <= 1) :
    |compactCoshD4 P a - compactCoshD4 P 0|
      <=
    compactCoshFourthLipschitzConstant P * |a| := by
  by_cases hzero : a = 0
  · simp [hzero]
  by_cases hpos : 0 < a
  · have hcont :
        ContinuousOn (compactCoshD4 P) (Icc (0:ℝ) a) :=
      (compactCoshD4_continuous hP hPc).continuousOn
    have hder :
        ∀ x ∈ Ioo (0:ℝ) a,
          HasDerivAt (compactCoshD4 P)
            (compactCoshD5 P x) x := by
      intro x hx
      exact compactCoshD4_hasDerivAt_D5 hP hPc x
    obtain ⟨c,hc,hslope⟩ :=
      exists_hasDerivAt_eq_slope
        (compactCoshD4 P) (compactCoshD5 P)
        hpos hcont hder
    have hcabs : |c| <= 1 := by
      have hc0 : 0 <= c := hc.1.le
      have hca : c <= a := hc.2.le
      rw [abs_of_nonneg hc0]
      have haa : a <= 1 := by
        rw [abs_of_pos hpos] at ha
        exact ha
      exact hca.trans haa
    have hD5 :=
      compactCoshD5_abs_le_fifthEnvelope hP hPc hcabs
    have ha0 : a ≠ 0 := ne_of_gt hpos
    have heq :
        compactCoshD4 P a - compactCoshD4 P 0
          = a * compactCoshD5 P c := by
      have := hslope
      field_simp [ha0] at this
      linarith
    rw [heq,abs_mul]
    exact mul_le_mul_of_nonneg_right hD5 (abs_nonneg a)
  · have hneg : a < 0 := lt_of_le_of_ne
      (le_of_not_gt hpos) hzero
    have hcont :
        ContinuousOn (compactCoshD4 P) (Icc a 0) :=
      (compactCoshD4_continuous hP hPc).continuousOn
    have hder :
        ∀ x ∈ Ioo a (0:ℝ),
          HasDerivAt (compactCoshD4 P)
            (compactCoshD5 P x) x := by
      intro x hx
      exact compactCoshD4_hasDerivAt_D5 hP hPc x
    obtain ⟨c,hc,hslope⟩ :=
      exists_hasDerivAt_eq_slope
        (compactCoshD4 P) (compactCoshD5 P)
        hneg.neg hcont hder
    have hcabs : |c| <= 1 := by
      have hca : a <= c := hc.1.le
      have hc0 : c <= 0 := hc.2.le
      have haminus : -1 <= a := by
        rw [abs_of_neg hneg] at ha
        linarith
      rw [abs_of_nonpos hc0]
      linarith
    have hD5 :=
      compactCoshD5_abs_le_fifthEnvelope hP hPc hcabs
    have ha0 : a ≠ 0 := ne_of_lt hneg
    have heq :
        compactCoshD4 P a - compactCoshD4 P 0
          = a * compactCoshD5 P c := by
      have := hslope
      field_simp [ha0] at this
      linarith
    rw [heq,abs_mul]
    exact mul_le_mul_of_nonneg_right hD5 (abs_nonneg a)

/--
Explicit two-sided negative band for a moment-cancelled compact cosh transform.
-/
theorem compactCosh_neg_of_quartic_margin
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    {m : ℝ}
    (hm : 0 < m)
    (hM0 : profileZerothMoment P = 0)
    (hM2 : profileSecondMoment P = 0)
    (hM4 : profileFourthMoment P <= -m) :
    ∀ a : ℝ,
      0 < |a| ->
      |a| <
        quantitativeFourthOrderRadius
          m (compactCoshFourthLipschitzConstant P) ->
      compactCoshTransform P a < 0 := by
  let K := compactCoshFourthLipschitzConstant P
  have hK : 0 <= K :=
    compactCoshFourthLipschitzConstant_nonneg P
  have hf0 : compactCoshTransform P 0 = 0 := by
    unfold compactCoshTransform profileZerothMoment at *
    simpa using hM0
  have hf10 : compactCoshD1 P 0 = 0 :=
    compactCoshD1_zero P
  have hf20 : compactCoshD2 P 0 = 0 := by
    unfold compactCoshD2 profileSecondMoment at *
    simpa using hM2
  have hf30 : compactCoshD3 P 0 = 0 :=
    compactCoshD3_zero P
  have hf40 : compactCoshD4 P 0 <= -m := by
    unfold compactCoshD4 profileFourthMoment at *
    simpa using hM4
  have hright :=
    neg_right_of_fourth_deriv_lipschitz
      hm hK
      (fun x => compactCoshTransform_hasDerivAt hP hPc x)
      (fun x => compactCoshD1_deriv hP hPc x)
      (fun x => compactCoshD2_deriv hP hPc x)
      (fun x => compactCoshD3_deriv hP hPc x)
      hf0 hf10 hf20 hf30 hf40
      (fun x hx =>
        compactCoshD4_sub_zero_abs_le hP hPc hx)
  intro a ha0 hae
  by_cases ha : 0 <= a
  · have habs : |a| = a := abs_of_nonneg ha
    exact hright a
      (by simpa [habs] using ha0)
      (by simpa [habs] using hae)
  · have haneg : a < 0 := lt_of_not_ge ha
    have habs : |a| = -a := abs_of_neg haneg
    have hp := hright (-a)
      (by linarith)
      (by simpa [habs] using hae)
    have heven :
        compactCoshTransform P (-a)
          = compactCoshTransform P a := by
      unfold compactCoshTransform
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        rw [show (-a)*u = -(a*u) by ring, Real.cosh_neg]
    rw [heven] at hp
    exact hp

end Synthesis
