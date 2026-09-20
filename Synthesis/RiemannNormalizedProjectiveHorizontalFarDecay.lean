import Synthesis.RiemannNormalizedProjectiveHorizontalOscillation
import Zeta23Bridge.OscillatoryKernelDecay

/-!
# Far-q decay for the exact horizontal quadratic consumer

After the completed-density collapse, the useful oscillatory object is the
divided-square horizontal consumer

  Q_proj(t,alpha,q)
    = integral H_{t,alpha}(v) cos(qv) dv

with one compactly supported physical profile H_{t,alpha}.

For fixed alpha this profile is C^2 and compactly supported, hence the existing
twice-integrated cosine estimate gives

  |Q_proj(t,alpha,q)| <= C_horiz(t,alpha) / q^2, q != 0.

This is the far half of the signed-near / small-far decomposition on the
correct post-cancellation observable.  No cosine-sign window in the original
u variable is required.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.OscillatoryKernelDecay

theorem coshMinusOneDivSq_contDiff_two_in_v
    (alpha : ℝ) :
    ContDiff ℝ 2 (coshMinusOneDivSq alpha) := by
  by_cases ha : alpha = 0
  · subst alpha
    simp only [coshMinusOneDivSq, if_pos rfl]
    fun_prop
  · simp only [coshMinusOneDivSq, if_neg ha]
    fun_prop

theorem normalizedProjectiveHorizontalPhysicalProfile_contDiff_two
    (t alpha : ℝ) :
    ContDiff ℝ 2 (normalizedProjectiveHorizontalPhysicalProfile t alpha) := by
  unfold normalizedProjectiveHorizontalPhysicalProfile
  exact (normalizedProjectivePhysicalProfile_contDiff_two t).mul
    (coshMinusOneDivSq_contDiff_two_in_v alpha)

def normalizedProjectiveHorizontalCurvature
    (t alpha : ℝ) : ℝ :=
  ∫ v : ℝ,
    |deriv (deriv
      (normalizedProjectiveHorizontalPhysicalProfile t alpha)) v|

theorem normalizedProjectiveHorizontalCurvature_nonneg
    (t alpha : ℝ) :
    0 ≤ normalizedProjectiveHorizontalCurvature t alpha := by
  unfold normalizedProjectiveHorizontalCurvature
  exact integral_nonneg fun _ => abs_nonneg _

/-- Direct q^-2 decay for the exact divided-square horizontal consumer. -/
theorem normalizedProjectiveHorizontalQuadratic_abs_le_invSq
    {t alpha q : ℝ} (hq : q ≠ 0) :
    |normalizedProjectiveHorizontalQuadratic t alpha q|
      ≤
    normalizedProjectiveHorizontalCurvature t alpha / q^2 := by
  rw [normalizedProjectiveHorizontalQuadratic_eq_physicalCosine]
  exact abs_integral_mul_cos_le
    (normalizedProjectiveHorizontalPhysicalProfile_contDiff_two t alpha)
    (normalizedProjectiveHorizontalPhysicalProfile_compact t alpha)
    hq

/-- A convenient far-region specialization. -/
theorem normalizedProjectiveHorizontalQuadratic_abs_le_of_one_le_abs
    {t alpha q : ℝ} (hq : 1 ≤ |q|) :
    |normalizedProjectiveHorizontalQuadratic t alpha q|
      ≤
    normalizedProjectiveHorizontalCurvature t alpha / q^2 := by
  apply normalizedProjectiveHorizontalQuadratic_abs_le_invSq
  intro hz
  subst q
  simp at hq

/-- Cauchy majorant convenient for integration or counting-measure attachment. -/
def normalizedProjectiveHorizontalCauchyMajorant
    (t alpha q : ℝ) : ℝ :=
  2 * normalizedProjectiveHorizontalCurvature t alpha
    * (1 + q^2)⁻¹

theorem normalizedProjectiveHorizontalCauchyMajorant_nonneg
    (t alpha q : ℝ) :
    0 ≤ normalizedProjectiveHorizontalCauchyMajorant t alpha q := by
  unfold normalizedProjectiveHorizontalCauchyMajorant
  have hc := normalizedProjectiveHorizontalCurvature_nonneg t alpha
  positivity

theorem normalizedProjectiveHorizontalQuadratic_abs_le_cauchy_of_one_le_abs
    {t alpha q : ℝ} (hq : 1 ≤ |q|) :
    |normalizedProjectiveHorizontalQuadratic t alpha q|
      ≤ normalizedProjectiveHorizontalCauchyMajorant t alpha q := by
  have hq0 : q ≠ 0 := by
    intro hz
    subst q
    simp at hq
  have hdecay :=
    normalizedProjectiveHorizontalQuadratic_abs_le_invSq
      (t := t) (alpha := alpha) hq0
  have hq2 : 1 ≤ q^2 := by
    rw [← sq_abs]
    nlinarith
  have hkernel : 1 / q^2 ≤ 2 * (1 + q^2)⁻¹ := by
    rw [inv_eq_one_div]
    have hq2pos : 0 < q^2 := lt_of_lt_of_le zero_lt_one hq2
    rw [le_div_iff₀ hq2pos]
    have hden : 0 < 1 + q^2 := by positivity
    rw [inv_eq_one_div, div_eq_mul_inv]
    rw [mul_comm, ← div_eq_mul_inv]
    rw [div_le_iff₀ hden]
    nlinarith
  have hc := normalizedProjectiveHorizontalCurvature_nonneg t alpha
  calc
    |normalizedProjectiveHorizontalQuadratic t alpha q|
      ≤ normalizedProjectiveHorizontalCurvature t alpha / q^2 := hdecay
    _ = normalizedProjectiveHorizontalCurvature t alpha * (1 / q^2) := by ring
    _ ≤ normalizedProjectiveHorizontalCurvature t alpha
        * (2 * (1 + q^2)⁻¹) := by
          exact mul_le_mul_of_nonneg_left hkernel hc
    _ = normalizedProjectiveHorizontalCauchyMajorant t alpha q := by
          unfold normalizedProjectiveHorizontalCauchyMajorant
          ring

theorem integrable_normalizedProjectiveHorizontalCauchyMajorant
    (t alpha : ℝ) :
    Integrable (normalizedProjectiveHorizontalCauchyMajorant t alpha) := by
  unfold normalizedProjectiveHorizontalCauchyMajorant
  exact integrable_inv_one_add_sq.const_mul
    (2 * normalizedProjectiveHorizontalCurvature t alpha)

theorem integral_normalizedProjectiveHorizontalCauchyMajorant
    (t alpha : ℝ) :
    (∫ q : ℝ,
      normalizedProjectiveHorizontalCauchyMajorant t alpha q)
      =
    2 * Real.pi *
      normalizedProjectiveHorizontalCurvature t alpha := by
  unfold normalizedProjectiveHorizontalCauchyMajorant
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  ring

end Synthesis
