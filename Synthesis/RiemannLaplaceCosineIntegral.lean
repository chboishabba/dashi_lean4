import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Laplace-cosine integral

The Gamma-kernel bridge needs the elementary transform

  integral_0^infinity exp(-a x) cos(b x) dx = a / (a^2+b^2),

for a>0.

This file proves it directly from the improper-integral FTC.  It is the real
analytic primitive used to transform each Lorentzian term in the digamma
partial-fraction series.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Synthesis

def laplaceCosPrimitive (a b x : ℝ) : ℝ :=
  Real.exp (-a*x) *
    ((-a) * Real.cos (b*x) + b * Real.sin (b*x))
      / (a^2 + b^2)

theorem laplaceCosPrimitive_hasDerivAt
    {a b x : ℝ} (ha : 0 < a) :
    HasDerivAt (laplaceCosPrimitive a b)
      (Real.exp (-a*x) * Real.cos (b*x)) x := by
  have hden : a^2 + b^2 ≠ 0 := by
    nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (-a*y))
        (-a * Real.exp (-a*x)) x := by
    convert (((hasDerivAt_id x).const_mul (-a)).exp) using 1 <;> ring
  have hcos :
      HasDerivAt (fun y : ℝ => Real.cos (b*y))
        (-b * Real.sin (b*x)) x := by
    convert (((hasDerivAt_id x).const_mul b).cos) using 1 <;> ring
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (b*y))
        (b * Real.cos (b*x)) x := by
    convert (((hasDerivAt_id x).const_mul b).sin) using 1 <;> ring
  have hnum :
      HasDerivAt
        (fun y : ℝ =>
          (-a) * Real.cos (b*y) + b * Real.sin (b*y))
        ((-a) * (-b * Real.sin (b*x))
          + b * (b * Real.cos (b*x))) x :=
    (hcos.const_mul (-a)).add (hsin.const_mul b)
  have hquot := hnum.div_const (a^2+b^2)
  have hprod := hexp.mul hquot
  convert hprod using 1
  · rfl
  · field_simp [hden]
    ring

theorem laplaceCos_integrableOn_Ioi
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-a*x) * Real.cos (b*x))
      (Set.Ioi 0) := by
  have hdom := exp_neg_integrableOn_Ioi 0 ha
  apply Integrable.mono' hdom
  · exact
      ((measurable_id.const_mul (-a)).exp.mul
        ((measurable_id.const_mul b).cos)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hc := Real.abs_cos_le_one (b*x)
    nlinarith [Real.exp_pos (-a*x)]

theorem laplaceCosPrimitive_tendsto_zero
    {a b : ℝ} (ha : 0 < a) :
    Tendsto (laplaceCosPrimitive a b) atTop (nhds 0) := by
  have hden : 0 < a^2 + b^2 := by
    nlinarith [sq_pos_of_pos ha, sq_nonneg b]
  let C : ℝ := (a + |b|) / (a^2+b^2)
  have hC : 0 <= C := by
    dsimp [C]
    positivity
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (-a*x)) atTop (nhds 0) := by
    have hlin : Tendsto (fun x : ℝ => a*x) atTop atTop :=
      tendsto_id.const_mul_atTop ha
    simpa [neg_mul] using tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have hbound :
      ∀ x : ℝ, |laplaceCosPrimitive a b x|
        <= C * Real.exp (-a*x) := by
    intro x
    unfold laplaceCosPrimitive
    have hc := Real.abs_cos_le_one (b*x)
    have hs := Real.abs_sin_le_one (b*x)
    have hn :
        |(-a) * Real.cos (b*x) + b * Real.sin (b*x)|
          <= a + |b| := by
      calc
        |(-a) * Real.cos (b*x) + b * Real.sin (b*x)|
            <= |(-a) * Real.cos (b*x)| + |b * Real.sin (b*x)| :=
          abs_add _ _
        _ = a * |Real.cos (b*x)| + |b| * |Real.sin (b*x)| := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha]
        _ <= a + |b| := by
          nlinarith [mul_nonneg ha.le (abs_nonneg (Real.cos (b*x))),
            mul_nonneg (abs_nonneg b) (abs_nonneg (Real.sin (b*x)))]
    have he := Real.exp_pos (-a*x)
    rw [abs_mul, abs_div, abs_of_pos he, abs_of_pos hden]
    dsimp [C]
    have hm := mul_le_mul_of_nonneg_left hn he.le
    exact (div_le_div_iff₀ hden hden).2 (by
      nlinarith)
  have hright :
      Tendsto (fun x : ℝ => C * Real.exp (-a*x)) atTop (nhds 0) := by
    simpa using hexp.const_mul C
  apply squeeze_zero'
  · exact fun x => abs_nonneg _
  · exact hbound
  · exact hright

theorem integral_Ioi_exp_neg_mul_cos
    {a b : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Set.Ioi 0,
      Real.exp (-a*x) * Real.cos (b*x))
      = a / (a^2+b^2) := by
  have hderiv :
      ∀ x ∈ Set.Ici (0 : ℝ),
        HasDerivAt (laplaceCosPrimitive a b)
          (Real.exp (-a*x) * Real.cos (b*x)) x :=
    fun x _ => laplaceCosPrimitive_hasDerivAt ha
  have hint := laplaceCos_integrableOn_Ioi (a:=a) (b:=b) ha
  have hlim := laplaceCosPrimitive_tendsto_zero (a:=a) (b:=b) ha
  have hFTC :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv hint hlim
  have hzero :
      laplaceCosPrimitive a b 0 = -a / (a^2+b^2) := by
    unfold laplaceCosPrimitive
    simp
    ring
  rw [hzero] at hFTC
  simpa using hFTC

end Synthesis
