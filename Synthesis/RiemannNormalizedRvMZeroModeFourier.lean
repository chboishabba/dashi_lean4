import Synthesis.RiemannNormalizedCenteredProfileSpectralGap
import Mathlib.Analysis.Fourier.Inversion

/-!
# Zero-mode Fourier cancellation compiler for the normalized RvM main term

Mathlib uses the real-line Fourier convention

  F[f](w) = integral exp(-2*pi*i*v*w) f(v) dv.

Fourier inversion at v=0 therefore says, whenever f and F[f] are integrable
and f is continuous,

  integral F[f](w) dw = f(0).

Hence any profile with f(0)=0 has exactly zero total Fourier mass.

The normalized centered canonical profile has an open gap around zero, so its
complexification vanishes at zero.  This file provides the exact structural
compiler needed for the constant-in-q part of the smooth Riemann--von Mangoldt
density.  Integrability of the Fourier transform and the bridge to the repo's
real cosine transform are kept as explicit separate obligations.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedCenteredComplexProfile (t : ℝ) : ℝ → ℂ :=
  fun v => (4 * normalizedCenteredFixedProfile t v : ℝ)

theorem normalizedCenteredComplexProfile_continuous (t : ℝ) :
    Continuous (normalizedCenteredComplexProfile t) := by
  unfold normalizedCenteredComplexProfile
  fun_prop

theorem normalizedCenteredComplexProfile_compact (t : ℝ) :
    HasCompactSupport (normalizedCenteredComplexProfile t) := by
  unfold normalizedCenteredComplexProfile
  exact (normalizedCenteredFixedProfile_compact t).mul_left.ofReal

theorem normalizedCenteredComplexProfile_integrable (t : ℝ) :
    Integrable (normalizedCenteredComplexProfile t) := by
  exact (normalizedCenteredComplexProfile_continuous t).integrable_of_hasCompactSupport
    (normalizedCenteredComplexProfile_compact t)

theorem normalizedCenteredComplexProfile_zero (t : ℝ) :
    normalizedCenteredComplexProfile t 0 = 0 := by
  unfold normalizedCenteredComplexProfile
  rw [normalizedCenteredFixedProfile_zero]
  norm_num

/--
Generic exact zero-mode Fourier cancellation.

No RvM theorem enters here: this is only the analytic Fourier-inversion
compiler that kills a constant spectral density once the Fourier transform is
known to be integrable.
-/
theorem integral_fourier_eq_zero_of_value_zero
    {f : ℝ → ℂ}
    (hcont : Continuous f)
    (hint : Integrable f)
    (hfourier : Integrable (FourierTransform.fourier f))
    (hzero : f 0 = 0) :
    (∫ w : ℝ, FourierTransform.fourier f w) = 0 := by
  have hinv :=
    Continuous.fourierInv_fourier_eq hcont hint hfourier
  have h0 := congrFun hinv (0 : ℝ)
  have hinv0 :
      FourierTransformInv.fourierInv
          (FourierTransform.fourier f) (0 : ℝ)
        =
      ∫ w : ℝ, FourierTransform.fourier f w := by
    rw [Real.fourierInv_eq_fourier_neg]
    simp only [neg_zero]
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp
  rw [hinv0, hzero] at h0
  exact h0

/--
The normalized centered canonical profile has exact zero total Fourier mass as
soon as its Fourier transform is placed in L1.
-/
theorem normalizedCenteredComplexProfile_fourier_total_zero
    (t : ℝ)
    (hfourier :
      Integrable
        (FourierTransform.fourier
          (normalizedCenteredComplexProfile t))) :
    (∫ w : ℝ,
      FourierTransform.fourier
        (normalizedCenteredComplexProfile t) w) = 0 := by
  exact integral_fourier_eq_zero_of_value_zero
    (normalizedCenteredComplexProfile_continuous t)
    (normalizedCenteredComplexProfile_integrable t)
    hfourier
    (normalizedCenteredComplexProfile_zero t)

end Synthesis
