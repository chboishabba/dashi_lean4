import Synthesis.RiemannNormalizedProjectiveBaseProfile
import Synthesis.RiemannNormalizedCenteredProfileSchwartz
import Synthesis.RiemannNormalizedRvMPhysicalDomainCompiler
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Projective-native RvM consumer

The projective q-only base observable is already the cosine transform of one
physical profile

  P_t(v) = 4 G_t(v)
    (A0(r) cos(v/8) - A0(2r) cos(v/16)).

This file pays the remaining structural Fourier obligations for that exact
consumer.

First, P_t is even, C-infinity and compactly supported, hence its complexification
is a Schwartz function.  Mathlib Fourier inversion therefore gives an
unconditional whole-line zero-mode cancellation

  integral_R Phi_proj(q) dq = 0.

Second, the physical Riemann--von Mangoldt density only inhabits q > -1.  The
whole-line identity is therefore transported through the honest domain split:

  integral_(q>-1) Phi_proj(q) dq
    = - integral_(q<=-1) Phi_proj(q) dq.

Consequently the q-independent RvM coefficient does not disappear merely from
P_t(0)=0; on the literal physical domain it is *exactly* the missing negative
half-line tail.  Any prize-facing cancellation/sign theorem must therefore prove
that this tail vanishes, has the favourable sign, or is absorbed into a
target-dependent quadratic residual.

No absolute estimate is introduced here.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

theorem normalizedProjectivePhysicalProfile_even (t : ℝ) :
    Function.Even (normalizedProjectivePhysicalProfile t) := by
  intro v
  unfold normalizedProjectivePhysicalProfile
  rw [normalizedCanonicalFixedProfile_even]
  simp [Real.cos_neg]

def normalizedProjectiveSineTransform (t q : ℝ) : ℝ :=
  ∫ v : ℝ,
    normalizedProjectivePhysicalProfile t v * Real.sin (q * v)

theorem normalizedProjectiveSineTransform_zero (t q : ℝ) :
    normalizedProjectiveSineTransform t q = 0 := by
  let g : ℝ → ℝ := fun v =>
    normalizedProjectivePhysicalProfile t v * Real.sin (q * v)
  have hodd : ∀ v, g (-v) = - g v := by
    intro v
    dsimp [g]
    rw [normalizedProjectivePhysicalProfile_even]
    simp [Real.sin_neg]
  have hchange :=
    MeasureTheory.integral_neg_eq_self g (volume : Measure ℝ)
  have hfun : (fun v : ℝ => g (-v)) = fun v => - g v := by
    funext v
    exact hodd v
  rw [hfun, integral_neg] at hchange
  unfold normalizedProjectiveSineTransform
  dsimp [g] at hchange
  linarith

theorem normalizedProjectiveComplexProfile_contDiff_top (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedProjectiveComplexProfile t) := by
  unfold normalizedProjectiveComplexProfile normalizedProjectivePhysicalProfile
  fun_prop

def normalizedProjectiveSchwartz (t : ℝ) : SchwartzMap ℝ ℂ :=
  (normalizedProjectiveComplexProfile_compact t).toSchwartzMap
    (normalizedProjectiveComplexProfile_contDiff_top t)

@[simp] theorem normalizedProjectiveSchwartz_apply (t v : ℝ) :
    normalizedProjectiveSchwartz t v = normalizedProjectiveComplexProfile t v := by
  rfl

theorem normalizedProjectiveSchwartz_fourier_coe (t : ℝ) :
    (fun w : ℝ =>
      (FourierTransform.fourier (normalizedProjectiveSchwartz t)) w)
      =
    FourierTransform.fourier (normalizedProjectiveComplexProfile t) := by
  rw [SchwartzMap.fourier_coe]
  rfl

theorem normalizedProjectiveComplexProfile_fourier_integrable (t : ℝ) :
    Integrable
      (FourierTransform.fourier
        (normalizedProjectiveComplexProfile t)) := by
  have hs :
      Integrable
        (fun w : ℝ =>
          (FourierTransform.fourier
            (normalizedProjectiveSchwartz t)) w) :=
    (FourierTransform.fourier (normalizedProjectiveSchwartz t)).integrable
  rw [normalizedProjectiveSchwartz_fourier_coe] at hs
  exact hs

theorem normalizedProjectiveFourier_integrand_eq
    (t w v : ℝ) :
    Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I)
        • normalizedProjectiveComplexProfile t v
      =
    (normalizedProjectivePhysicalProfile t v
        * Real.cos ((2 * Real.pi * w) * v) : ℝ)
      -
    (normalizedProjectivePhysicalProfile t v
        * Real.sin ((2 * Real.pi * w) * v) : ℝ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I]
  simp only [smul_eq_mul, normalizedProjectiveComplexProfile]
  push_cast
  simp [Real.cos_neg, Real.sin_neg]
  ring

/-- Exact same-object weld from the projective Schwartz Fourier transform to
the q-only base transform consumed by the projective zero measure. -/
theorem normalizedProjectiveFourier_eq_cosineTransform
    (t w : ℝ) :
    FourierTransform.fourier
        (normalizedProjectiveComplexProfile t) w
      =
    (normalizedProjectiveBaseTransform t
        (2 * Real.pi * w) : ℝ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hcosR :
      Integrable
        (fun v : ℝ =>
          normalizedProjectivePhysicalProfile t v
            * Real.cos ((2 * Real.pi * w) * v)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedProjectivePhysicalProfile_compact t).mul_right)
  have hcosC :
      Integrable
        (fun v : ℝ =>
          ((normalizedProjectivePhysicalProfile t v
            * Real.cos ((2 * Real.pi * w) * v) : ℝ) : ℂ)) :=
    hcosR.ofReal
  have hsinR :
      Integrable
        (fun v : ℝ =>
          normalizedProjectivePhysicalProfile t v
            * Real.sin ((2 * Real.pi * w) * v)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedProjectivePhysicalProfile_compact t).mul_right)
  have hsinC :
      Integrable
        (fun v : ℝ =>
          (((normalizedProjectivePhysicalProfile t v
            * Real.sin ((2 * Real.pi * w) * v) : ℝ) : ℂ)
              * Complex.I)) :=
    (hsinR.ofReal).mul_const Complex.I
  have hpoint :
      (fun v : ℝ =>
        Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I)
          • normalizedProjectiveComplexProfile t v)
      =
      fun v : ℝ =>
        ((normalizedProjectivePhysicalProfile t v
          * Real.cos ((2 * Real.pi * w) * v) : ℝ) : ℂ)
        -
        (((normalizedProjectivePhysicalProfile t v
          * Real.sin ((2 * Real.pi * w) * v) : ℝ) : ℂ)
            * Complex.I) := by
    funext v
    exact normalizedProjectiveFourier_integrand_eq t w v
  rw [hpoint, integral_sub hcosC hsinC]
  rw [integral_complex_ofReal]
  have hsin0 :=
    normalizedProjectiveSineTransform_zero
      t (2 * Real.pi * w)
  have hsinIntegral :
      (∫ v : ℝ,
        (((normalizedProjectivePhysicalProfile t v
          * Real.sin ((2 * Real.pi * w) * v) : ℝ) : ℂ)
            * Complex.I))
        = 0 := by
    rw [← integral_mul_const, integral_complex_ofReal, hsin0]
    simp
  rw [hsinIntegral, sub_zero]
  rw [normalizedProjectiveBaseTransform_eq_physicalCosine]
  rfl

theorem normalizedProjectiveComplexProfile_fourier_total_zero_unconditional
    (t : ℝ) :
    (∫ w : ℝ,
      FourierTransform.fourier
        (normalizedProjectiveComplexProfile t) w) = 0 := by
  exact normalizedProjectiveComplexProfile_fourier_total_zero t
    (normalizedProjectiveComplexProfile_fourier_integrable t)

theorem normalizedProjectiveBaseTransform_scaled_integrable (t : ℝ) :
    Integrable
      (fun w : ℝ =>
        normalizedProjectiveBaseTransform t (2 * Real.pi * w)) := by
  have hFC :
      Integrable
        (fun w : ℝ =>
          ((normalizedProjectiveBaseTransform t
            (2 * Real.pi * w) : ℝ) : ℂ)) := by
    have hf :=
      normalizedProjectiveComplexProfile_fourier_integrable t
    have heq :
        (fun w : ℝ =>
          ((normalizedProjectiveBaseTransform t
            (2 * Real.pi * w) : ℝ) : ℂ))
          =
        FourierTransform.fourier
          (normalizedProjectiveComplexProfile t) := by
      funext w
      exact (normalizedProjectiveFourier_eq_cosineTransform t w).symm
    rw [heq]
    exact hf
  have hr := hFC.re
  simpa using hr

theorem normalizedProjectiveBaseTransform_integrable (t : ℝ) :
    Integrable (normalizedProjectiveBaseTransform t) := by
  have hscale := normalizedProjectiveBaseTransform_scaled_integrable t
  exact
    (integrable_comp_mul_left_iff
      (normalizedProjectiveBaseTransform t)
      (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos))).1
      (by simpa [mul_assoc] using hscale)

theorem normalizedProjectiveBaseTransform_scaled_integral_zero (t : ℝ) :
    (∫ w : ℝ,
      normalizedProjectiveBaseTransform t (2 * Real.pi * w)) = 0 := by
  have hfourier :=
    normalizedProjectiveComplexProfile_fourier_total_zero_unconditional t
  have heq :
      (fun w : ℝ =>
        FourierTransform.fourier
          (normalizedProjectiveComplexProfile t) w)
        =
      fun w : ℝ =>
        ((normalizedProjectiveBaseTransform t
          (2 * Real.pi * w) : ℝ) : ℂ) := by
    funext w
    exact normalizedProjectiveFourier_eq_cosineTransform t w
  rw [heq, integral_complex_ofReal] at hfourier
  have hre := congrArg Complex.re hfourier
  simpa using hre

/-- The projective q-only base transform has exactly zero whole-line mass. -/
theorem normalizedProjectiveBaseTransform_integral_zero (t : ℝ) :
    (∫ q : ℝ, normalizedProjectiveBaseTransform t q) = 0 := by
  have hscaled :=
    normalizedProjectiveBaseTransform_scaled_integral_zero t
  have hchange :=
    Measure.integral_comp_mul_left
      (normalizedProjectiveBaseTransform t)
      (2 * Real.pi)
  rw [hscaled] at hchange
  have hcoef :
      0 < |(2 * Real.pi)⁻¹| := by
    positivity
  have hmul :
      |(2 * Real.pi)⁻¹|
        * (∫ q : ℝ, normalizedProjectiveBaseTransform t q)
        = 0 := by
    simpa [smul_eq_mul] using hchange.symm
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hcoef)

theorem normalizedProjectivePhysicalIndicator_integrable (t : ℝ) :
    Integrable
      (normalizedRvMPhysicalIndicator
        (normalizedProjectiveBaseTransform t)) := by
  unfold normalizedRvMPhysicalIndicator
  exact (normalizedProjectiveBaseTransform_integrable t).indicator
    measurableSet_Ioi

theorem normalizedProjectiveMissingTailIndicator_integrable (t : ℝ) :
    Integrable
      (normalizedRvMMissingTailIndicator
        (normalizedProjectiveBaseTransform t)) := by
  unfold normalizedRvMMissingTailIndicator
  exact (normalizedProjectiveBaseTransform_integrable t).indicator
    measurableSet_Iic

/-- Honest physical-domain transport of the projective zero-mode cancellation.

The physical q>-1 mass equals minus the missing q<=-1 tail; it is not asserted
to vanish. -/
theorem normalizedProjective_physical_eq_neg_missing (t : ℝ) :
    (∫ q : ℝ,
      normalizedRvMPhysicalIndicator
        (normalizedProjectiveBaseTransform t) q)
      =
    - (∫ q : ℝ,
      normalizedRvMMissingTailIndicator
        (normalizedProjectiveBaseTransform t) q) := by
  exact integral_physical_eq_neg_missing_of_total_zero
    (normalizedProjectivePhysicalIndicator_integrable t)
    (normalizedProjectiveMissingTailIndicator_integrable t)
    (normalizedProjectiveBaseTransform_integral_zero t)

/-- Exact consumer-level constant-mode identity.

The target-independent constant RvM mode on the physical domain is precisely
the negative missing-domain tail multiplied by the literal constant density.
Thus zero-mode quotienting is consumer-sufficient iff the tail is subsequently
shown to vanish or have a favourable signed role. -/
theorem normalizedProjective_constantMode_physical_eq_neg_missing
    (t : ℝ) :
    normalizedRvMConstantMode t *
      (∫ q : ℝ,
        normalizedRvMPhysicalIndicator
          (normalizedProjectiveBaseTransform t) q)
      =
    - normalizedRvMConstantMode t *
      (∫ q : ℝ,
        normalizedRvMMissingTailIndicator
          (normalizedProjectiveBaseTransform t) q) := by
  rw [normalizedProjective_physical_eq_neg_missing]
  ring

end Synthesis
