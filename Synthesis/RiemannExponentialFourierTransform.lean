import Synthesis.RiemannLaplaceCosineIntegral
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Fourier transform of the two-sided exponential kernel

For c>0,

    f_c(x) = exp(-c |x|)

has the normalized Mathlib Fourier transform

    Fourier(f_c)(w) = 2c / (c^2 + (2*pi*w)^2).

The proof is componentwise.  The real part is the even cosine integral and the
imaginary part vanishes by oddness.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Real FourierTransform RealInnerProductSpace Complex

namespace Synthesis

def expAbsKernel (c : ℝ) (x : ℝ) : ℂ :=
  (Real.exp (-c * |x|) : ℂ)

theorem exp_neg_abs_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) := by
  rw [← integrableOn_univ]
  have hp : IntegrableOn (fun x : ℝ => Real.exp (-c*x)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  have hn : IntegrableOn (fun x : ℝ => Real.exp (-c*|x|)) (Set.Iic 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_zero]
    apply hp.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [abs_neg, abs_of_pos hx]
  have hpos : IntegrableOn
      (fun x : ℝ => Real.exp (-c*|x|)) (Set.Ioi 0) := by
    apply hp.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [abs_of_pos hx]
  rw [← integrableOn_Iic_union_Ioi]
  exact hn.add_measure hpos

theorem expAbsKernel_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (expAbsKernel c) := by
  apply Integrable.ofReal
  exact exp_neg_abs_integrable hc

theorem integral_exp_neg_abs_mul_cos {c k : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (-c*|x|) * Real.cos (k*x))
      = 2*c / (c^2+k^2) := by
  have hcomp :
      (fun x : ℝ => Real.exp (-c*|x|) * Real.cos (k*x))
        =
      fun x : ℝ =>
        (fun y : ℝ => Real.exp (-c*y) * Real.cos (k*y)) |x| := by
    funext x
    rw [Real.cos_abs]
  rw [hcomp, integral_comp_abs,
    integral_Ioi_exp_neg_mul_cos hc]
  ring

theorem integral_exp_neg_abs_mul_sin {c k : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (-c*|x|) * Real.sin (k*x)) = 0 := by
  let f : ℝ → ℝ :=
    fun x => Real.exp (-c*|x|) * Real.sin (k*x)
  have hf : Integrable f := by
    apply Integrable.mono' (exp_neg_abs_integrable hc)
    · fun_prop
    · filter_upwards with x
      unfold f
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le
        (Real.abs_sin_le_one _)
  have hneg : (fun x : ℝ => f (-x)) = fun x => - f x := by
    funext x
    unfold f
    simp [abs_neg, Real.sin_neg]
  have hinv :
      (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
    simpa using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding f
  rw [hneg, integral_neg] at hinv
  linarith

theorem fourier_expAbsKernel {c w : ℝ} (hc : 0 < c) :
    𝓕 (expAbsKernel c) w
      = ((2*c / (c^2 + (2*Real.pi*w)^2) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint :
      Integrable
        (fun x : ℝ =>
          Complex.exp (↑(-2 * Real.pi * x * w) * Complex.I)
            • expAbsKernel c x) :=
    (Real.fourierIntegral_convergent_iff w).2
      (expAbsKernel_integrable hc)
  apply Complex.ext
  · rw [← integral_re hint]
    simp only [Complex.exp_mul_I, Complex.real_smul, expAbsKernel,
      Complex.ofReal_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    have hcos :=
      integral_exp_neg_abs_mul_cos
        (c:=c) (k:=2*Real.pi*w) hc
    simpa [mul_comm, mul_left_comm, mul_assoc, Real.cos_neg] using hcos
  · rw [← integral_im hint]
    simp only [Complex.exp_mul_I, Complex.imag_smul, expAbsKernel,
      Complex.ofReal_re, Complex.ofReal_im, mul_im, zero_mul, add_zero]
    have hsin :=
      integral_exp_neg_abs_mul_sin
        (c:=c) (k:=2*Real.pi*w) hc
    simpa [mul_comm, mul_left_comm, mul_assoc, Real.sin_neg] using hsin

end Synthesis
