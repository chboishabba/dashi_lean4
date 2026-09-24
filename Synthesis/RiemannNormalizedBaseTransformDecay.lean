import Synthesis.RiemannNormalizedCenteredOffHorizontalSplit
import Synthesis.RiemannNormalizedCenteredOffOscillatoryDecay

/-!
# Pointwise decay of the one-dimensional normalized base transform

The common base transform is

  Phi_t(q) = integral 4 H_t(v) cos(q v) dv.

It is exactly the alpha=0 specialization of the already-proved normalized
reflection-pair transform.  Therefore for q != 0,

  |Phi_t(q)| <= C_t / q^2,

where

  C_t = normalizedPairCurvature t 0.

This is the key domain-tail estimate needed by the smooth RvM main term.  The
whole-line constant mode cancels by Fourier inversion; restricting the smooth
RvM density to q>-1 leaves only q<=-1, and on that half-line q^-2 is
integrable with finite mass 1.

The present file pays the same-object pointwise bridge.  Improper half-line
integration is kept separate so the Fourier/domain argument can be audited
without conflating it with this specialization.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedBaseTransformCurvature (t : ℝ) : ℝ :=
  normalizedPairCurvature t 0

theorem normalizedPairWeight_zero_eq_baseWeight
    (t v : ℝ) :
    normalizedPairWeight t 0 v
      =
    4 * normalizedCenteredFixedProfile t v := by
  unfold normalizedPairWeight
  simp

theorem normalizedBaseTransform_eq_pairIntegral_zero
    (t q : ℝ) :
    normalizedCenteredBaseTransform t q
      =
    ∫ v : ℝ,
      4 * normalizedCenteredFixedProfile t v
        * Real.cosh ((0 : ℝ) * v)
        * Real.cos (q * v) := by
  unfold normalizedCenteredBaseTransform
  simp

theorem normalizedCenteredBaseTransform_abs_le_invSq
    {t q : ℝ} (hq : q ≠ 0) :
    |normalizedCenteredBaseTransform t q|
      <= normalizedBaseTransformCurvature t / q ^ 2 := by
  rw [normalizedBaseTransform_eq_pairIntegral_zero]
  exact abs_integral_normalizedCenteredPair_le
    (t := t) (alpha := 0) hq

theorem normalizedBaseTransformCurvature_nonneg
    (t : ℝ) :
    0 <= normalizedBaseTransformCurvature t := by
  unfold normalizedBaseTransformCurvature normalizedPairCurvature
  positivity

/--
On the missing RvM domain q<=-1 the base transform is bounded by the curvature
constant times q^-2, with no singularity.
-/
theorem normalizedCenteredBaseTransform_abs_le_of_le_neg_one
    {t q : ℝ} (hq : q <= -1) :
    |normalizedCenteredBaseTransform t q|
      <= normalizedBaseTransformCurvature t / q ^ 2 := by
  apply normalizedCenteredBaseTransform_abs_le_invSq
  linarith

/--
A slightly coarser form convenient for monotone tail comparison:
for q<=-1, |q|>=1 and the transform is bounded by the curvature constant.
-/
theorem normalizedCenteredBaseTransform_abs_le_curvature_of_le_neg_one
    {t q : ℝ} (hq : q <= -1) :
    |normalizedCenteredBaseTransform t q|
      <= normalizedBaseTransformCurvature t := by
  have hdecay :=
    normalizedCenteredBaseTransform_abs_le_of_le_neg_one
      (t := t) hq
  have hqabs : 1 <= |q| := by
    rw [abs_of_nonpos (le_trans hq (by norm_num : (-1 : ℝ) <= 0))]
    linarith
  have hq2 : 1 <= q ^ 2 := by
    nlinarith [sq_abs q]
  have hc := normalizedBaseTransformCurvature_nonneg t
  have hdiv :
      normalizedBaseTransformCurvature t / q ^ 2
        <= normalizedBaseTransformCurvature t := by
    have hq2pos : 0 < q ^ 2 := by
      nlinarith
    rw [div_le_iff₀ hq2pos]
    nlinarith
  exact le_trans hdecay hdiv

end Synthesis
