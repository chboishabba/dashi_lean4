import Synthesis.RiemannLorentzianCosineTransform
import Zeta23Bridge.LiteralWeilParityBalance

/-!
# Exact convolution of the repo cosine transform with a digamma Lorentzian

For a>0 and compactly supported continuous h,

  integral_x cosFT h (x-t) * [a/(a^2+x^2/4)]
    = 2*pi * integral_u h(u) cos(tu) exp(-2a|u|).

This is proved directly by Fubini.  The sine piece vanishes because the
Lorentzian is even.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance

def digammaLorentzian (a x : ℝ) : ℝ :=
  a / (a^2 + x^2/4)

theorem digammaLorentzian_nonneg {a x : ℝ} (ha : 0 <= a) :
    0 <= digammaLorentzian a x := by
  unfold digammaLorentzian
  positivity

theorem digammaLorentzian_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (digammaLorentzian a) := by
  have hbase := integrable_inv_one_add_mul_sq (b := (1/(2*a))) (by positivity)
  have hrewrite :
      (fun x : ℝ => digammaLorentzian a x)
        =
      fun x : ℝ => (1/a) * (1 + ((1/(2*a))*x)^2)⁻¹ := by
    funext x
    unfold digammaLorentzian
    field_simp [ne_of_gt ha]
    ring
  rw [hrewrite]
  exact hbase.const_mul _

theorem integral_digammaLorentzian_mul_sin
    {a u : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, digammaLorentzian a x * Real.sin (x*u)) = 0 := by
  let f : ℝ → ℝ :=
    fun x => digammaLorentzian a x * Real.sin (x*u)
  have hf : Integrable f := by
    apply Integrable.mono' (digammaLorentzian_integrable ha)
    · fun_prop
    · filter_upwards with x
      unfold f
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (digammaLorentzian_nonneg ha.le)]
      exact mul_le_of_le_one_right
        (digammaLorentzian_nonneg ha.le)
        (Real.abs_sin_le_one _)
  have hodd : (fun x : ℝ => f (-x)) = fun x => - f x := by
    funext x
    unfold f digammaLorentzian
    simp [Real.sin_neg]
  have hinv :
      (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
    simpa using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding f
  rw [hodd, integral_neg] at hinv
  linarith

theorem integral_cos_shift_mul_digammaLorentzian
    {a t u : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      Real.cos ((x-t)*u) * digammaLorentzian a x)
      =
    2*Real.pi * Real.cos (t*u) * Real.exp (-2*a*|u|) := by
  have hcos :=
    integral_digammaLorentzian_cos (a:=a) (u:=u) ha
  have hsin :=
    integral_digammaLorentzian_mul_sin (a:=a) (u:=u) ha
  have hi1 :
      Integrable
        (fun x : ℝ =>
          digammaLorentzian a x * Real.cos (x*u)) := by
    apply Integrable.mono' (digammaLorentzian_integrable ha)
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (digammaLorentzian_nonneg ha.le)]
      exact mul_le_of_le_one_right
        (digammaLorentzian_nonneg ha.le)
        (Real.abs_cos_le_one _)
  have hi2 :
      Integrable
        (fun x : ℝ =>
          digammaLorentzian a x * Real.sin (x*u)) := by
    apply Integrable.mono' (digammaLorentzian_integrable ha)
    · fun_prop
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (digammaLorentzian_nonneg ha.le)]
      exact mul_le_of_le_one_right
        (digammaLorentzian_nonneg ha.le)
        (Real.abs_sin_le_one _)
  rw [show (fun x : ℝ =>
      Real.cos ((x-t)*u) * digammaLorentzian a x)
      =
      fun x =>
        Real.cos (t*u)
          * (digammaLorentzian a x * Real.cos (x*u))
        + Real.sin (t*u)
          * (digammaLorentzian a x * Real.sin (x*u)) by
      funext x
      rw [Real.cos_sub]
      ring]
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _),
    integral_const_mul, integral_const_mul, hcos, hsin]
  ring

theorem cosFT_digammaLorentzian_fubini_integrable
    {h : ℝ → ℝ} (hh : Continuous h)
    (hcompact : HasCompactSupport h)
    {a t : ℝ} (ha : 0 < a) :
    Integrable
      (fun p : ℝ × ℝ =>
        h p.2 * Real.cos ((p.1-t)*p.2)
          * digammaLorentzian a p.1) := by
  have hhInt : Integrable h :=
    hh.integrable_of_hasCompactSupport hcompact
  have hL := digammaLorentzian_integrable ha
  have hprod : Integrable
      (fun p : ℝ × ℝ => |h p.2| * digammaLorentzian a p.1) :=
    (hL.mul_prod hhInt.abs).congr' (by
      filter_upwards with p
      simp [mul_comm])
  apply Integrable.mono' hprod
  · fun_prop
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (digammaLorentzian_nonneg ha.le)]
    have hc := Real.abs_cos_le_one ((p.1-t)*p.2)
    nlinarith [abs_nonneg (h p.2)]

theorem integral_cosFT_mul_digammaLorentzian
    {h : ℝ → ℝ} (hh : Continuous h)
    (hcompact : HasCompactSupport h)
    {a t : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      cosFT h (x-t) * digammaLorentzian a x)
      =
    2*Real.pi *
      ∫ u : ℝ,
        h u * Real.cos (t*u) * Real.exp (-2*a*|u|) := by
  have hprod :=
    cosFT_digammaLorentzian_fubini_integrable
      hh hcompact ha
  unfold cosFT
  have hswap := integral_integral_swap hprod
  rw [← hswap]
  congr 1
  funext u
  rw [← integral_const_mul]
  congr 1
  funext x
  ring_nf
  rw [integral_cos_shift_mul_digammaLorentzian ha]
  ring

end Synthesis
