import Synthesis.RiemannNormalizedRvMFourierCosineWeld
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact cancellation of the constant normalized spectral density

The preceding files prove

  F[4 H_t](w) = Phi_t(2*pi*w),

and realize 4 H_t as a compactly supported Schwartz function.  Fourier inversion
at zero therefore gives

  integral_w Phi_t(2*pi*w) dw = 0.

The exact Haar/Lebesgue scaling lemmas from Mathlib then transfer both
integrability and the integral identity from w to q=2*pi*w.

Result:

  integral_q Phi_t(q) dq = 0.

Thus every q-constant smooth spectral density contributes exactly zero to the
normalized Off main pairing.  In particular, after writing a local RvM density
as a constant log(t)-piece plus q-dependent residual, the dangerous log(t)
coefficient is structurally annihilated before any absolute value.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

theorem normalizedCenteredBaseTransform_scaled_integrable (t : ℝ) :
    Integrable
      (fun w : ℝ =>
        normalizedCenteredBaseTransform t (2 * Real.pi * w)) := by
  have hFC :
      Integrable
        (fun w : ℝ =>
          ((normalizedCenteredBaseTransform t
            (2 * Real.pi * w) : ℝ) : ℂ)) := by
    have hf :=
      normalizedCenteredComplexProfile_fourier_integrable t
    have heq :
        (fun w : ℝ =>
          ((normalizedCenteredBaseTransform t
            (2 * Real.pi * w) : ℝ) : ℂ))
          =
        FourierTransform.fourier
          (normalizedCenteredComplexProfile t) := by
      funext w
      exact (normalizedCenteredFourier_eq_cosineTransform t w).symm
    rw [heq]
    exact hf
  have hr := hFC.re
  simpa using hr

theorem normalizedCenteredBaseTransform_integrable (t : ℝ) :
    Integrable (normalizedCenteredBaseTransform t) := by
  have hscale := normalizedCenteredBaseTransform_scaled_integrable t
  exact
    (integrable_comp_mul_left_iff
      (normalizedCenteredBaseTransform t)
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))).1
      (by simpa [mul_assoc] using hscale)

theorem normalizedCenteredBaseTransform_scaled_integral_zero (t : ℝ) :
    (∫ w : ℝ,
      normalizedCenteredBaseTransform t (2 * Real.pi * w)) = 0 := by
  have hfourier :=
    normalizedCenteredComplexProfile_fourier_total_zero_unconditional t
  have heq :
      (fun w : ℝ =>
        FourierTransform.fourier
          (normalizedCenteredComplexProfile t) w)
        =
      fun w : ℝ =>
        ((normalizedCenteredBaseTransform t
          (2 * Real.pi * w) : ℝ) : ℂ) := by
    funext w
    exact normalizedCenteredFourier_eq_cosineTransform t w
  rw [heq, integral_complex_ofReal] at hfourier
  have hre := congrArg Complex.re hfourier
  simpa using hre

theorem normalizedCenteredBaseTransform_integral_zero (t : ℝ) :
    (∫ q : ℝ, normalizedCenteredBaseTransform t q) = 0 := by
  have hscaled :=
    normalizedCenteredBaseTransform_scaled_integral_zero t
  have hchange :=
    Measure.integral_comp_mul_left
      (normalizedCenteredBaseTransform t)
      (2 * Real.pi)
  rw [hscaled] at hchange
  have hcoef :
      0 < |(2 * Real.pi)⁻¹| := by
    positivity
  have hmul :
      |(2 * Real.pi)⁻¹|
        * (∫ q : ℝ, normalizedCenteredBaseTransform t q)
        = 0 := by
    simpa [smul_eq_mul] using hchange.symm
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hcoef)

theorem constant_density_pair_zero (t c : ℝ) :
    (∫ q : ℝ,
      c * normalizedCenteredBaseTransform t q) = 0 := by
  rw [integral_const_mul,
      normalizedCenteredBaseTransform_integral_zero,
      mul_zero]

end Synthesis
