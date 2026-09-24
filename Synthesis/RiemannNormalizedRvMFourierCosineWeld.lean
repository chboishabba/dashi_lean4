import Synthesis.RiemannNormalizedCenteredProfileSchwartz
import Synthesis.RiemannNormalizedCenteredOffHorizontalSplit
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Exact Fourier / cosine-transform weld for the normalized centered profile

For the real-even profile H_t, Mathlib's Fourier convention gives

  F[4 H_t](w)
    = integral 4 H_t(v) exp(-2*pi*i*v*w) dv.

The sine part is odd and integrates to zero. Therefore the Fourier transform is
literally real and equals the existing RH base transform at q=2*pi*w:

  F[4 H_t](w)
    = (normalizedCenteredBaseTransform t (2*pi*w) : C).

This is the same-object bridge from the Schwartz/Fourier machinery back to the
literal normalized Off counting functional.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

theorem normalizedInnerFixedProfile_even :
    Function.Even normalizedInnerFixedProfile := by
  intro v
  unfold normalizedInnerFixedProfile
  congr 1 <;> congr 1 <;>
    field_simp [ne_of_gt Real.pi_pos] <;> ring

theorem normalizedOuterFixedProfile_even :
    Function.Even normalizedOuterFixedProfile := by
  intro v
  unfold normalizedOuterFixedProfile
  congr 1 <;> congr 1 <;>
    field_simp [ne_of_gt Real.pi_pos] <;> ring

theorem normalizedCanonicalFixedProfile_even (t : ℝ) :
    Function.Even (normalizedCanonicalFixedProfile t) := by
  intro v
  unfold normalizedCanonicalFixedProfile
  rw [normalizedInnerFixedProfile_even v,
      normalizedOuterFixedProfile_even v]

theorem normalizedCenteredFixedProfile_even (t : ℝ) :
    Function.Even (normalizedCenteredFixedProfile t) := by
  intro v
  unfold normalizedCenteredFixedProfile
  rw [normalizedCanonicalFixedProfile_even]
  simp [Real.cos_neg]

def normalizedCenteredSineTransform (t q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCenteredFixedProfile t v * Real.sin (q * v)

theorem normalizedCenteredSineTransform_zero (t q : ℝ) :
    normalizedCenteredSineTransform t q = 0 := by
  let g : ℝ → ℝ := fun v =>
    4 * normalizedCenteredFixedProfile t v * Real.sin (q * v)
  have hodd : ∀ v, g (-v) = - g v := by
    intro v
    dsimp [g]
    rw [normalizedCenteredFixedProfile_even]
    simp [Real.sin_neg]
  have hchange :=
    MeasureTheory.integral_neg_eq_self g (volume : Measure ℝ)
  have hfun : (fun v : ℝ => g (-v)) = fun v => - g v := by
    funext v
    exact hodd v
  rw [hfun, integral_neg] at hchange
  unfold normalizedCenteredSineTransform
  dsimp [g] at hchange
  linarith

theorem normalizedCenteredFourier_integrand_eq
    (t w v : ℝ) :
    Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I)
        • normalizedCenteredComplexProfile t v
      =
    (4 * normalizedCenteredFixedProfile t v
        * Real.cos ((2 * Real.pi * w) * v) : ℝ)
      -
    (4 * normalizedCenteredFixedProfile t v
        * Real.sin ((2 * Real.pi * w) * v) : ℝ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I]
  simp only [smul_eq_mul, normalizedCenteredComplexProfile]
  push_cast
  simp [Real.cos_neg, Real.sin_neg]
  ring

theorem normalizedCenteredFourier_eq_cosineTransform
    (t w : ℝ) :
    FourierTransform.fourier
        (normalizedCenteredComplexProfile t) w
      =
    (normalizedCenteredBaseTransform t
        (2 * Real.pi * w) : ℝ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hcosC :
      Integrable
        (fun v : ℝ =>
          ((4 * normalizedCenteredFixedProfile t v
            * Real.cos ((2 * Real.pi * w) * v) : ℝ) : ℂ)) := by
    have hreal :=
      integrable_normalizedCenteredBase t (2 * Real.pi * w)
    exact hreal.ofReal
  have hsinR :
      Integrable
        (fun v : ℝ =>
          4 * normalizedCenteredFixedProfile t v
            * Real.sin ((2 * Real.pi * w) * v)) := by
    have hc : Continuous
        (fun v : ℝ =>
          4 * normalizedCenteredFixedProfile t v
            * Real.sin ((2 * Real.pi * w) * v)) := by
      exact (continuous_const.mul
        (normalizedCenteredFixedProfile_contDiff t).continuous).mul
          (by fun_prop)
    have hs : HasCompactSupport
        (fun v : ℝ =>
          4 * normalizedCenteredFixedProfile t v
            * Real.sin ((2 * Real.pi * w) * v)) := by
      exact (normalizedCenteredFixedProfile_compact t).mul_left.mul_right
    exact hc.integrable_of_hasCompactSupport hs
  have hsinC :
      Integrable
        (fun v : ℝ =>
          (((4 * normalizedCenteredFixedProfile t v
            * Real.sin ((2 * Real.pi * w) * v) : ℝ) : ℂ)
              * Complex.I)) := by
    exact (hsinR.ofReal).mul_const Complex.I
  have hpoint :
      (fun v : ℝ =>
        Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I)
          • normalizedCenteredComplexProfile t v)
      =
      fun v : ℝ =>
        ((4 * normalizedCenteredFixedProfile t v
          * Real.cos ((2 * Real.pi * w) * v) : ℝ) : ℂ)
        -
        (((4 * normalizedCenteredFixedProfile t v
          * Real.sin ((2 * Real.pi * w) * v) : ℝ) : ℂ)
            * Complex.I) := by
    funext v
    exact normalizedCenteredFourier_integrand_eq t w v
  rw [hpoint, integral_sub hcosC hsinC]
  rw [integral_complex_ofReal]
  have hsin0 :=
    normalizedCenteredSineTransform_zero
      t (2 * Real.pi * w)
  have hsinIntegral :
      (∫ v : ℝ,
        (((4 * normalizedCenteredFixedProfile t v
          * Real.sin ((2 * Real.pi * w) * v) : ℝ) : ℂ)
            * Complex.I))
        = 0 := by
    rw [← integral_mul_const, integral_complex_ofReal, hsin0]
    simp
  rw [hsinIntegral, sub_zero]
  rfl

end Synthesis
