import Synthesis.RiemannNormalizedProjectiveRvMConsumer
import Zeta23Bridge.OscillatoryKernelDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Projective-native missing-domain tail bound

The previous missing-tail estimate was still stated for the one-radius centered
base transform.  The reflection-pair cutset consumes the projective base
transform

  Phi_proj(t,q) = integral P_t(v) cos(qv) dv.

Because P_t is C^2 and compactly supported, the existing signed oscillatory
integration-by-parts theorem applies directly:

  |Phi_proj(t,q)| <= C_proj(t) / q^2,  q != 0,

with

  C_proj(t) = integral |(P_t)''(v)| dv.

On the physical-domain complement q<=-1 this gives an explicit integrable
Cauchy majorant and therefore

  | integral_{q<=-1} Phi_proj(t,q) dq |
    <= 2*pi*C_proj(t).

This pays B0 on the correct projective observable.  It is deliberately only an
absolute bound: because the target signal vanishes like a_rho^2, this theorem
alone is not a uniform high-side closure.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.OscillatoryKernelDecay

theorem normalizedProjectivePhysicalProfile_contDiff_two (t : ℝ) :
    ContDiff ℝ 2 (normalizedProjectivePhysicalProfile t) := by
  unfold normalizedProjectivePhysicalProfile
  fun_prop

def normalizedProjectiveBaseCurvature (t : ℝ) : ℝ :=
  ∫ v : ℝ,
    |deriv (deriv (normalizedProjectivePhysicalProfile t)) v|

theorem normalizedProjectiveBaseCurvature_nonneg (t : ℝ) :
    0 <= normalizedProjectiveBaseCurvature t := by
  unfold normalizedProjectiveBaseCurvature
  exact integral_nonneg fun _ => abs_nonneg _

/-- Direct q^-2 decay for the actual projective base transform. -/
theorem normalizedProjectiveBaseTransform_abs_le_invSq
    {t q : ℝ} (hq : q ≠ 0) :
    |normalizedProjectiveBaseTransform t q|
      <= normalizedProjectiveBaseCurvature t / q ^ 2 := by
  rw [normalizedProjectiveBaseTransform_eq_physicalCosine]
  exact abs_integral_mul_cos_le
    (normalizedProjectivePhysicalProfile_contDiff_two t)
    (normalizedProjectivePhysicalProfile_compact t)
    hq

theorem normalizedProjectiveBaseTransform_abs_le_of_le_neg_one
    {t q : ℝ} (hq : q <= -1) :
    |normalizedProjectiveBaseTransform t q|
      <= normalizedProjectiveBaseCurvature t / q ^ 2 := by
  apply normalizedProjectiveBaseTransform_abs_le_invSq
  linarith

def normalizedProjectiveCauchyMajorant (t q : ℝ) : ℝ :=
  2 * normalizedProjectiveBaseCurvature t * (1 + q ^ 2)⁻¹

theorem normalizedProjectiveCauchyMajorant_nonneg
    (t q : ℝ) :
    0 <= normalizedProjectiveCauchyMajorant t q := by
  unfold normalizedProjectiveCauchyMajorant
  have hc := normalizedProjectiveBaseCurvature_nonneg t
  positivity

theorem projectiveMissingTailIndicator_abs_le_cauchyMajorant
    (t q : ℝ) :
    |normalizedRvMMissingTailIndicator
        (normalizedProjectiveBaseTransform t) q|
      <=
    normalizedProjectiveCauchyMajorant t q := by
  by_cases hq : q <= -1
  · have hmem : q ∈ Set.Iic (-1 : ℝ) := hq
    simp only [normalizedRvMMissingTailIndicator,
      Set.indicator_of_mem hmem]
    have hdecay :=
      normalizedProjectiveBaseTransform_abs_le_of_le_neg_one
        (t := t) hq
    have hkernel := inv_sq_le_two_inv_one_add_sq hq
    have hc := normalizedProjectiveBaseCurvature_nonneg t
    calc
      |normalizedProjectiveBaseTransform t q|
        <= normalizedProjectiveBaseCurvature t / q ^ 2 := hdecay
      _ = normalizedProjectiveBaseCurvature t * (1 / q ^ 2) := by ring
      _ <= normalizedProjectiveBaseCurvature t
          * (2 * (1 + q ^ 2)⁻¹) := by
            exact mul_le_mul_of_nonneg_left hkernel hc
      _ = normalizedProjectiveCauchyMajorant t q := by
            unfold normalizedProjectiveCauchyMajorant
            ring
  · have hnot : q ∉ Set.Iic (-1 : ℝ) := by
      simpa [Set.mem_Iic] using hq
    simp [normalizedRvMMissingTailIndicator,
      Set.indicator_of_not_mem hnot,
      normalizedProjectiveCauchyMajorant_nonneg]

theorem integrable_normalizedProjectiveCauchyMajorant
    (t : ℝ) :
    Integrable (normalizedProjectiveCauchyMajorant t) := by
  unfold normalizedProjectiveCauchyMajorant
  exact integrable_inv_one_add_sq.const_mul
    (2 * normalizedProjectiveBaseCurvature t)

theorem integral_normalizedProjectiveCauchyMajorant
    (t : ℝ) :
    (∫ q : ℝ, normalizedProjectiveCauchyMajorant t q)
      =
    2 * Real.pi * normalizedProjectiveBaseCurvature t := by
  unfold normalizedProjectiveCauchyMajorant
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  ring

/-- Explicit B0 bound on the same projective base consumer used by the cutset. -/
theorem normalizedProjective_missingTail_abs_le
    (t : ℝ) :
    |∫ q : ℝ,
      normalizedRvMMissingTailIndicator
        (normalizedProjectiveBaseTransform t) q|
      <=
    2 * Real.pi * normalizedProjectiveBaseCurvature t := by
  calc
    |∫ q : ℝ,
      normalizedRvMMissingTailIndicator
        (normalizedProjectiveBaseTransform t) q|
      <=
    ∫ q : ℝ,
      |normalizedRvMMissingTailIndicator
        (normalizedProjectiveBaseTransform t) q| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ q : ℝ, normalizedProjectiveCauchyMajorant t q := by
      exact integral_mono
        (normalizedProjectiveMissingTailIndicator_integrable t).abs
        (integrable_normalizedProjectiveCauchyMajorant t)
        (fun q => projectiveMissingTailIndicator_abs_le_cauchyMajorant t q)
    _ =
    2 * Real.pi * normalizedProjectiveBaseCurvature t :=
      integral_normalizedProjectiveCauchyMajorant t

end Synthesis
