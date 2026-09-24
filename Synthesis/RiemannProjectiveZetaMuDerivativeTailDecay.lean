import Synthesis.RiemannProjectiveZetaMuEndpointDecay
import Synthesis.RiemannNormalizedProjectiveBaseTransformDerivativeRegularity
import Zeta23Bridge.OscillatoryKernelDecay

/-!
# Quadratic tail decay of the physical projective Abel derivative

The physical Abel integrand is

  phi_t'(x) E_A(x).

The discrepancy E_A(x) grows only logarithmically. To pass the exact finite
Abel identity to an infinite physical window we therefore want oscillatory
decay.

Write

  Phi_t'(q) = integral W_t(v) sin(qv) dv,
  W_t(v) = -v P_t(v).

Since P_t is C^2 and compactly supported, so is W_t. One sine integration by
parts followed by one cosine integration by parts gives quadratic decay

  |Phi_t'(q)| <= C'_t / q^2,

with C'_t = integral |W_t''|.

After q=(x-t)/t and the outer chain-rule factor 1/t this becomes

  |phi_t'(x)| <= C'_t * t / (x-t)^2.

This is precisely the tail scale needed to pair against logarithmic
Zeta23 discrepancy.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.OscillatoryKernelDecay

def normalizedProjectiveDerivativeWeight (t v : ℝ) : ℝ :=
  - normalizedProjectivePhysicalProfile t v * v

theorem normalizedProjectiveDerivativeWeight_contDiff_two
    (t : ℝ) :
    ContDiff ℝ 2 (normalizedProjectiveDerivativeWeight t) := by
  unfold normalizedProjectiveDerivativeWeight
  exact (normalizedProjectivePhysicalProfile_contDiff_two t).neg.mul contDiff_id

theorem normalizedProjectiveDerivativeWeight_compact
    (t : ℝ) :
    HasCompactSupport (normalizedProjectiveDerivativeWeight t) := by
  unfold normalizedProjectiveDerivativeWeight
  exact (normalizedProjectivePhysicalProfile_compact t).neg.mul_right

def normalizedProjectiveDerivativeCurvature (t : ℝ) : ℝ :=
  ∫ v : ℝ,
    |deriv (deriv (normalizedProjectiveDerivativeWeight t)) v|

theorem normalizedProjectiveDerivativeCurvature_nonneg
    (t : ℝ) :
    0 ≤ normalizedProjectiveDerivativeCurvature t := by
  unfold normalizedProjectiveDerivativeCurvature
  positivity

theorem normalizedProjectiveBaseTransformDeriv_abs_le_invSq
    {t q : ℝ} (hq : q ≠ 0) :
    |normalizedProjectiveBaseTransformDeriv t q|
      ≤ normalizedProjectiveDerivativeCurvature t / q^2 := by
  let w : ℝ → ℝ := normalizedProjectiveDerivativeWeight t
  have hw2 : ContDiff ℝ 2 w := normalizedProjectiveDerivativeWeight_contDiff_two t
  have hw1 : ContDiff ℝ 1 w := hw2.of_le (by norm_num)
  have hw1d : ContDiff ℝ 1 (deriv w) := ContDiff.deriv' hw2
  have hws : HasCompactSupport w := normalizedProjectiveDerivativeWeight_compact t
  have h1 := integral_mul_sin_eq hw1 hws hq
  have h2 := integral_mul_cos_eq hw1d hws.deriv hq

  have hsecond :
      (∫ v : ℝ, w v * Real.sin (q*v))
        =
      -(1 / q^2) *
        ∫ v : ℝ, deriv (deriv w) v * Real.sin (q*v) := by
    rw [h1, h2]
    field_simp
    ring

  have hd2c : Continuous (deriv (deriv w)) :=
    hw1d.continuous_deriv le_rfl
  have hd2s : HasCompactSupport (deriv (deriv w)) :=
    hws.deriv.deriv
  have hi :
      Integrable
        (fun v : ℝ => deriv (deriv w) v * Real.sin (q*v)) :=
    Continuous.integrable_of_hasCompactSupport
      (hd2c.mul (by fun_prop)) hd2s.mul_right
  have hiabs :
      Integrable
        (fun v : ℝ => |deriv (deriv w) v|) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop) hd2s.abs
  have hbound :
      |∫ v : ℝ, deriv (deriv w) v * Real.sin (q*v)|
        ≤
      ∫ v : ℝ, |deriv (deriv w) v| := by
    calc
      |∫ v : ℝ, deriv (deriv w) v * Real.sin (q*v)|
        ≤ ∫ v : ℝ, |deriv (deriv w) v * Real.sin (q*v)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ v : ℝ, |deriv (deriv w) v| := by
        apply integral_mono hi.abs hiabs
        intro v
        rw [abs_mul]
        exact mul_le_of_le_one_right
          (abs_nonneg _) (Real.abs_sin_le_one _)

  unfold normalizedProjectiveBaseTransformDeriv
  change
    |∫ v : ℝ, w v * Real.sin (q*v)|
      ≤ normalizedProjectiveDerivativeCurvature t / q^2
  rw [hsecond, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ 1 / q^2)]
  unfold normalizedProjectiveDerivativeCurvature
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

theorem normalizedProjectiveOrdinateTestDeriv_abs_le_gap_sq
    {t x : ℝ} (ht : 0 < t) (hxt : x ≠ t) :
    |normalizedProjectiveOrdinateTestDeriv t x|
      ≤ normalizedProjectiveDerivativeCurvature t * t / (x-t)^2 := by
  unfold normalizedProjectiveOrdinateTestDeriv
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hq : (x-t)/t ≠ 0 := by
    apply div_ne_zero
    · exact sub_ne_zero.mpr hxt
    · exact ht0
  rw [abs_mul, abs_of_pos (one_div_pos.mpr ht)]
  have hdec :=
    normalizedProjectiveBaseTransformDeriv_abs_le_invSq
      (t := t) (q := (x-t)/t) hq
  calc
    (1/t) * |normalizedProjectiveBaseTransformDeriv t ((x-t)/t)|
      ≤ (1/t) *
          (normalizedProjectiveDerivativeCurvature t / (((x-t)/t)^2)) := by
        exact mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = normalizedProjectiveDerivativeCurvature t * t / (x-t)^2 := by
      field_simp [ht0, sub_ne_zero.mpr hxt]
      ring

end Synthesis
