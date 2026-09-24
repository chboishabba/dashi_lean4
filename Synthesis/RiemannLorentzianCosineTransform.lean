import Synthesis.RiemannExponentialFourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Lorentzian cosine transform from Fourier inversion

Using the normalized Mathlib Fourier transform

  Fourier(exp(-c|x|))(w) = 2c / (c^2 + (2*pi*w)^2),

Fourier inversion gives

  integral_w [2c/(c^2+(2*pi*w)^2)] cos(2*pi*w*u) dw
    = exp(-c|u|).

After the change of variable x=2*pi*w,

  integral_x [2c/(c^2+x^2)] cos(x*u) dx
    = 2*pi*exp(-c|u|).

Putting c=2a yields the exact reciprocal term occurring in the digamma series:

  integral_x [a/(a^2+x^2/4)] cos(x*u) dx
    = 2*pi*exp(-2a|u|).
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Real FourierTransform RealInnerProductSpace Complex

namespace Synthesis

def normalizedLorentzian (c : ℝ) (w : ℝ) : ℂ :=
  ((2*c / (c^2 + (2*Real.pi*w)^2) : ℝ) : ℂ)

theorem normalizedLorentzian_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (normalizedLorentzian c) := by
  have hb : (2*Real.pi/c) ≠ 0 := by positivity
  have hbase :
      Integrable (fun w : ℝ => (1 + ((2*Real.pi/c)*w)^2)⁻¹) :=
    integrable_inv_one_add_mul_sq hb
  have hreal :
      Integrable
        (fun w : ℝ => (2/c) * (1 + ((2*Real.pi/c)*w)^2)⁻¹) :=
    hbase.const_mul _
  apply Integrable.congr (hreal.ofReal)
  filter_upwards with w
  unfold normalizedLorentzian
  push_cast
  congr 1
  field_simp [ne_of_gt hc]
  ring

theorem expAbsKernel_continuous (c : ℝ) :
    Continuous (expAbsKernel c) := by
  unfold expAbsKernel
  fun_prop

theorem fourier_expAbsKernel_function {c : ℝ} (hc : 0 < c) :
    𝓕 (expAbsKernel c) = normalizedLorentzian c := by
  funext w
  exact fourier_expAbsKernel hc

theorem normalizedLorentzian_fourierInv
    {c u : ℝ} (hc : 0 < c) :
    𝓕⁻ (normalizedLorentzian c) u = expAbsKernel c u := by
  have hf := expAbsKernel_integrable hc
  have hF : Integrable (𝓕 (expAbsKernel c)) := by
    rw [fourier_expAbsKernel_function hc]
    exact normalizedLorentzian_integrable hc
  exact hf.fourierInv_fourier_eq hF
    (expAbsKernel_continuous c).continuousAt

theorem integral_normalizedLorentzian_mul_cos
    {c u : ℝ} (hc : 0 < c) :
    (∫ w : ℝ,
      (2*c / (c^2 + (2*Real.pi*w)^2))
        * Real.cos (2*Real.pi*w*u))
      = Real.exp (-c*|u|) := by
  have hInv := normalizedLorentzian_fourierInv (c:=c) (u:=u) hc
  rw [Real.fourierInv_eq'] at hInv
  have hint :
      Integrable
        (fun w : ℝ =>
          Complex.exp (↑(2 * Real.pi * (w*u)) * Complex.I)
            • normalizedLorentzian c w) := by
    have hN := normalizedLorentzian_integrable hc
    exact (Real.fourierIntegral_convergent_iff (-u)).2 hN
  have hre := congrArg Complex.re hInv
  rw [← integral_re hint] at hre
  simp only [normalizedLorentzian, expAbsKernel, Complex.exp_mul_I,
    Complex.real_smul, Complex.ofReal_re, Complex.ofReal_im,
    mul_re, mul_zero, sub_zero] at hre
  simpa [mul_assoc, mul_comm, mul_left_comm] using hre

theorem integral_two_mul_lorentzian_cos
    {c u : ℝ} (hc : 0 < c) :
    (∫ x : ℝ,
      (2*c / (c^2 + x^2)) * Real.cos (x*u))
      = 2*Real.pi * Real.exp (-c*|u|) := by
  let F : ℝ → ℝ :=
    fun x => (2*c / (c^2+x^2)) * Real.cos (x*u)
  have hscale := Measure.integral_comp_mul_left
    F (2*Real.pi)
  have hpi : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hinv : |(2*Real.pi)⁻¹| = (2*Real.pi)⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hpi)]
  have hnorm :=
    integral_normalizedLorentzian_mul_cos (c:=c) (u:=u) hc
  have hcomp :
      (fun w : ℝ => F ((2*Real.pi)*w))
        =
      fun w : ℝ =>
        (2*c / (c^2+(2*Real.pi*w)^2))
          * Real.cos (2*Real.pi*w*u) := by
    funext w
    unfold F
    ring_nf
  rw [hcomp, hnorm, hinv] at hscale
  unfold F at hscale
  have hpi0 : 2*Real.pi ≠ 0 := ne_of_gt hpi
  field_simp [hpi0] at hscale ⊢
  nlinarith [Real.exp_pos (-c*|u|)]

theorem integral_digammaLorentzian_cos
    {a u : ℝ} (ha : 0 < a) :
    (∫ x : ℝ,
      (a / (a^2 + x^2/4)) * Real.cos (x*u))
      = 2*Real.pi * Real.exp (-2*a*|u|) := by
  have h :=
    integral_two_mul_lorentzian_cos
      (c:=2*a) (u:=u) (by positivity)
  have hfun :
      (fun x : ℝ =>
        ((2*(2*a)) / ((2*a)^2+x^2)) * Real.cos (x*u))
      =
      fun x : ℝ =>
        (a / (a^2+x^2/4)) * Real.cos (x*u) := by
    funext x
    congr 1
    field_simp
    ring
  rw [hfun] at h
  simpa [mul_assoc] using h

end Synthesis
