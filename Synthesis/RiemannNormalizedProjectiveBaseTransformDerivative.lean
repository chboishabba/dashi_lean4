import Synthesis.RiemannNormalizedProjectiveBaseTransformVariation
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivative of the exact projective base consumer

The projective zero-minus-mu residual is consumed by

  Phi_t(q) = ∫ P_t(v) cos(q v) dv.

This file differentiates that exact same object under the integral sign.  The
derivative is dominated by the already-defined first absolute moment of the
physical projective profile:

  |Phi_t'(q)| <= ∫ |P_t(v)| |v| dv.

Composing with the physical ordinate q=(gamma-t)/t gives the exact derivative
needed by the literal continuous Abel identity.

No finite q-grid and no quadrature are used.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

def normalizedProjectiveBaseTransformDeriv (t q : ℝ) : ℝ :=
  ∫ v : ℝ,
    - normalizedProjectivePhysicalProfile t v
      * Real.sin (q * v) * v

theorem normalizedProjectiveBaseTransform_hasDerivAt
    (t q : ℝ) :
    HasDerivAt
      (normalizedProjectiveBaseTransform t)
      (normalizedProjectiveBaseTransformDeriv t q)
      q := by
  let F : ℝ → ℝ → ℝ := fun x v =>
    normalizedProjectivePhysicalProfile t v * Real.cos (x * v)
  let F' : ℝ → ℝ → ℝ := fun x v =>
    - normalizedProjectivePhysicalProfile t v * Real.sin (x * v) * v
  let bound : ℝ → ℝ := fun v =>
    |normalizedProjectivePhysicalProfile t v| * |v|

  have hFmeas :
      ∀ᶠ x in 𝓝 q, AEStronglyMeasurable (F x) volume := by
    filter_upwards with x
    exact (by
      dsimp [F]
      fun_prop : Continuous
        (fun v : ℝ =>
          normalizedProjectivePhysicalProfile t v * Real.cos (x * v))).aestronglyMeasurable
  have hFint : Integrable (F q) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedProjectivePhysicalProfile_compact t).mul_right)
  have hF'meas : AEStronglyMeasurable (F' q) volume := by
    exact (by
      dsimp [F']
      fun_prop : Continuous
        (fun v : ℝ =>
          - normalizedProjectivePhysicalProfile t v
            * Real.sin (q * v) * v)).aestronglyMeasurable
  have hbound : Integrable bound volume := by
    dsimp [bound]
    exact normalizedProjectiveProfile_firstMoment_integrable t
  have hderiv :
      ∀ᵐ v ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (F · v) (F' x v) x := by
    filter_upwards with v
    intro x hx
    dsimp [F, F']
    fun_prop
  have hdom :
      ∀ᵐ v ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        ‖F' x v‖ ≤ bound v := by
    filter_upwards with v
    intro x hx
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
    have hs : |Real.sin (x * v)| ≤ 1 :=
      Real.abs_sin_le_one (x * v)
    nlinarith [abs_nonneg (normalizedProjectivePhysicalProfile t v),
      abs_nonneg v]

  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume)
      (F := F)
      (x₀ := q)
      (s := (Set.univ : Set ℝ))
      (bound := bound)
      (by simp)
      hFmeas hFint hF'meas hdom hbound hderiv
  have hder :=
    h.2
  have heq :
      (fun x : ℝ => ∫ v : ℝ, F x v)
        = normalizedProjectiveBaseTransform t := by
    funext x
    dsimp [F]
    exact (normalizedProjectiveBaseTransform_eq_physicalCosine t x).symm
  rw [heq] at hder
  simpa [normalizedProjectiveBaseTransformDeriv, F'] using hder

theorem normalizedProjectiveBaseTransformDeriv_abs_le
    (t q : ℝ) :
    |normalizedProjectiveBaseTransformDeriv t q|
      ≤ normalizedProjectiveProfileFirstMoment t := by
  unfold normalizedProjectiveBaseTransformDeriv
  have hderInt :
      Integrable
        (fun v : ℝ =>
          - normalizedProjectivePhysicalProfile t v
            * Real.sin (q * v) * v) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((normalizedProjectivePhysicalProfile_compact t).neg.mul_right).mul_right)
  calc
    |∫ v : ℝ,
      - normalizedProjectivePhysicalProfile t v
        * Real.sin (q * v) * v|
      ≤
    ∫ v : ℝ,
      |- normalizedProjectivePhysicalProfile t v
        * Real.sin (q * v) * v| :=
      abs_integral_le_integral_abs
    _ ≤
    ∫ v : ℝ,
      |normalizedProjectivePhysicalProfile t v| * |v| := by
      apply integral_mono hderInt.abs
        (normalizedProjectiveProfile_firstMoment_integrable t)
      intro v
      rw [abs_mul, abs_mul, abs_neg]
      have hs := Real.abs_sin_le_one (q * v)
      nlinarith [abs_nonneg (normalizedProjectivePhysicalProfile t v),
        abs_nonneg v]
    _ = normalizedProjectiveProfileFirstMoment t := rfl

def normalizedProjectiveOrdinateTest (t gamma : ℝ) : ℝ :=
  normalizedProjectiveBaseTransform t ((gamma - t) / t)

def normalizedProjectiveOrdinateTestDeriv (t gamma : ℝ) : ℝ :=
  (1 / t) *
    normalizedProjectiveBaseTransformDeriv t ((gamma - t) / t)

theorem normalizedProjectiveOrdinateTest_hasDerivAt
    {t gamma : ℝ} (ht : t ≠ 0) :
    HasDerivAt
      (normalizedProjectiveOrdinateTest t)
      (normalizedProjectiveOrdinateTestDeriv t gamma)
      gamma := by
  have hinner :
      HasDerivAt (fun x : ℝ => (x - t) / t) (1 / t) gamma := by
    convert ((hasDerivAt_id gamma).sub_const t).div_const t using 1 <;>
      field_simp [ht]
  have houter :=
    normalizedProjectiveBaseTransform_hasDerivAt
      t ((gamma - t) / t)
  have hcomp := houter.comp gamma hinner
  simpa [normalizedProjectiveOrdinateTest,
    normalizedProjectiveOrdinateTestDeriv, mul_comm] using hcomp

theorem normalizedProjectiveOrdinateTestDeriv_abs_le
    {t gamma : ℝ} (ht : 0 < t) :
    |normalizedProjectiveOrdinateTestDeriv t gamma|
      ≤
    (1 / t) * normalizedProjectiveProfileFirstMoment t := by
  unfold normalizedProjectiveOrdinateTestDeriv
  rw [abs_mul, abs_of_pos (one_div_pos.mpr ht)]
  exact mul_le_mul_of_nonneg_left
    (normalizedProjectiveBaseTransformDeriv_abs_le
      t ((gamma - t) / t))
    (one_div_nonneg.mpr ht.le)

end Synthesis
