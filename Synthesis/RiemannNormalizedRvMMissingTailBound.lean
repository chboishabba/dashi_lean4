import Synthesis.RiemannNormalizedRvMPhysicalDomainCompiler
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Explicit missing-domain bound for the normalized RvM constant mode

On q<=-1 the normalized base transform obeys

  |Phi_t(q)| <= C_t / q^2.

To avoid any delicate change-of-variables theorem for the negative half-line,
majorize by the globally integrable Cauchy kernel:

  1/q^2 <= 2/(1+q^2)        (|q|>=1).

Mathlib owns

  integral_R 1/(1+q^2) dq = pi.

Therefore, for every integrable missing-tail restriction,

  | integral_(q<=-1) Phi_t(q) dq |
    <= 2*pi*C_t.

This constant is intentionally crude.  The Clay high threshold is enormous and
we only need a finite explicit constant multiplying log(t)/t.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedBaseCauchyMajorant (t q : ℝ) : ℝ :=
  2 * normalizedBaseTransformCurvature t * (1 + q ^ 2)⁻¹

theorem normalizedBaseCauchyMajorant_nonneg
    (t q : ℝ) :
    0 <= normalizedBaseCauchyMajorant t q := by
  unfold normalizedBaseCauchyMajorant
  have hc := normalizedBaseTransformCurvature_nonneg t
  positivity

theorem inv_sq_le_two_inv_one_add_sq
    {q : ℝ} (hq : q <= -1) :
    1 / q ^ 2 <= 2 * (1 + q ^ 2)⁻¹ := by
  have hq2 : 1 <= q ^ 2 := by
    nlinarith
  have hq2pos : 0 < q ^ 2 := lt_of_lt_of_le (by norm_num) hq2
  have hone : 0 < 1 + q ^ 2 := by positivity
  rw [div_eq_mul_inv]
  rw [inv_le_iff₀ hq2pos]
  rw [← div_eq_mul_inv]
  rw [div_le_iff₀ hone]
  nlinarith

theorem missingTailIndicator_abs_le_cauchyMajorant
    (t q : ℝ) :
    |normalizedRvMMissingTailIndicator
        (normalizedCenteredBaseTransform t) q|
      <=
    normalizedBaseCauchyMajorant t q := by
  by_cases hq : q <= -1
  · have hmem : q ∈ Set.Iic (-1 : ℝ) := hq
    simp only [normalizedRvMMissingTailIndicator,
      Set.indicator_of_mem hmem]
    have hdecay :=
      normalizedCenteredBaseTransform_abs_le_of_le_neg_one
        (t := t) hq
    have hkernel := inv_sq_le_two_inv_one_add_sq hq
    have hc := normalizedBaseTransformCurvature_nonneg t
    calc
      |normalizedCenteredBaseTransform t q|
        <= normalizedBaseTransformCurvature t / q ^ 2 := hdecay
      _ = normalizedBaseTransformCurvature t * (1 / q ^ 2) := by ring
      _ <= normalizedBaseTransformCurvature t
          * (2 * (1 + q ^ 2)⁻¹) := by
            exact mul_le_mul_of_nonneg_left hkernel hc
      _ = normalizedBaseCauchyMajorant t q := by
            unfold normalizedBaseCauchyMajorant
            ring
  · have hnot : q ∉ Set.Iic (-1 : ℝ) := by
      simpa [Set.mem_Iic] using hq
    simp [normalizedRvMMissingTailIndicator,
      Set.indicator_of_not_mem hnot,
      normalizedBaseCauchyMajorant_nonneg]

theorem integrable_normalizedBaseCauchyMajorant
    (t : ℝ) :
    Integrable (normalizedBaseCauchyMajorant t) := by
  unfold normalizedBaseCauchyMajorant
  exact integrable_inv_one_add_sq.const_mul
    (2 * normalizedBaseTransformCurvature t)

theorem integral_normalizedBaseCauchyMajorant
    (t : ℝ) :
    (∫ q : ℝ, normalizedBaseCauchyMajorant t q)
      =
    2 * Real.pi * normalizedBaseTransformCurvature t := by
  unfold normalizedBaseCauchyMajorant
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  ring

/--
Explicit negative-domain tail bound.  Integrability of the restricted transform
is kept as a separate same-object analytic input; the quantitative estimate
itself is now a closed consequence of the existing q^-2 theorem.
-/
theorem normalizedBase_missingTail_abs_le
    (t : ℝ)
    (htail :
      Integrable
        (normalizedRvMMissingTailIndicator
          (normalizedCenteredBaseTransform t))) :
    |∫ q : ℝ,
      normalizedRvMMissingTailIndicator
        (normalizedCenteredBaseTransform t) q|
      <=
    2 * Real.pi * normalizedBaseTransformCurvature t := by
  calc
    |∫ q : ℝ,
      normalizedRvMMissingTailIndicator
        (normalizedCenteredBaseTransform t) q|
      <=
    ∫ q : ℝ,
      |normalizedRvMMissingTailIndicator
        (normalizedCenteredBaseTransform t) q| :=
      abs_integral_le_integral_abs
    _ <=
    ∫ q : ℝ, normalizedBaseCauchyMajorant t q := by
      exact integral_mono
        htail.abs
        (integrable_normalizedBaseCauchyMajorant t)
        (fun q => missingTailIndicator_abs_le_cauchyMajorant t q)
    _ =
    2 * Real.pi * normalizedBaseTransformCurvature t :=
      integral_normalizedBaseCauchyMajorant t

end Synthesis
