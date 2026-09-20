import Synthesis.RiemannNormalizedProjectiveHorizontalUniformSign
import Synthesis.RiemannNormalizedProjectiveHorizontalOscillation
import Zeta23Bridge.LiteralWeilProjectiveTaper

/-!
# Quadratic q-variation of the exact horizontal projective consumer

The existing near-sign compiler used a first-moment Lipschitz estimate in q.
But Q_proj is a cosine transform, so comparison with q=0 has no linear term.

For the exact horizontal physical profile H,

  Q(q) - Q(0) = integral H(v) (cos(qv)-1) dv,

and the elementary bound |cos x - 1| <= x^2/2 gives

  |Q(q)-Q(0)| <= q^2/2 * integral |H(v)| v^2 dv.

This is strictly stronger in the narrow physical band |q| < 1/t and is the
correct local sign compiler after the synthetic q=0 negativity theorem.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveTaper

def normalizedProjectiveHorizontalSecondMoment
    (t alpha : ℝ) : ℝ :=
  ∫ v : ℝ,
    |normalizedProjectiveHorizontalPhysicalProfile t alpha v| * v^2

theorem normalizedProjectiveHorizontalSecondMoment_nonneg
    (t alpha : ℝ) :
    0 ≤ normalizedProjectiveHorizontalSecondMoment t alpha := by
  unfold normalizedProjectiveHorizontalSecondMoment
  exact integral_nonneg fun v => mul_nonneg (abs_nonneg _) (sq_nonneg _)

theorem normalizedProjectiveHorizontalSecondMoment_integrable
    (t alpha : ℝ) :
    Integrable fun v : ℝ =>
      |normalizedProjectiveHorizontalPhysicalProfile t alpha v| * v^2 := by
  exact Continuous.integrable_of_hasCompactSupport
    (by fun_prop)
    ((normalizedProjectiveHorizontalPhysicalProfile_compact t alpha).abs.mul_right)

/-- Exact quadratic variation estimate around q=0. -/
theorem normalizedProjectiveHorizontalQuadratic_sub_zero_abs_le_sq
    (t alpha q : ℝ) :
    |normalizedProjectiveHorizontalQuadratic t alpha q
        - normalizedProjectiveHorizontalQuadratic t alpha 0|
      ≤
    q^2 / 2 * normalizedProjectiveHorizontalSecondMoment t alpha := by
  rw [normalizedProjectiveHorizontalQuadratic_eq_physicalCosine,
      normalizedProjectiveHorizontalQuadratic_eq_physicalCosine]
  simp only [zero_mul, Real.cos_zero, mul_one]
  let H : ℝ → ℝ :=
    normalizedProjectiveHorizontalPhysicalProfile t alpha
  have hH : Integrable H := by
    exact Continuous.integrable_of_hasCompactSupport
      (normalizedProjectiveHorizontalPhysicalProfile_continuous t alpha)
      (normalizedProjectiveHorizontalPhysicalProfile_compact t alpha)
  have hHcos : Integrable fun v : ℝ => H v * Real.cos (q*v) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by dsimp [H]; fun_prop)
      ((normalizedProjectiveHorizontalPhysicalProfile_compact t alpha).mul_right)
  have hdiff :
      (∫ v : ℝ, H v * Real.cos (q*v))
        - (∫ v : ℝ, H v)
        =
      ∫ v : ℝ, H v * (Real.cos (q*v) - 1) := by
    rw [← integral_sub hHcos hH]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by ring
  rw [hdiff]
  calc
    |∫ v : ℝ, H v * (Real.cos (q*v) - 1)|
      ≤
    ∫ v : ℝ, |H v * (Real.cos (q*v) - 1)| := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (fun v : ℝ => H v * (Real.cos (q*v) - 1))
    _ ≤
    ∫ v : ℝ, q^2 / 2 * (|H v| * v^2) := by
      apply integral_mono
      · exact Continuous.integrable_of_hasCompactSupport
          (by dsimp [H]; fun_prop)
          (((normalizedProjectiveHorizontalPhysicalProfile_compact t alpha).mul_right).sub
            (normalizedProjectiveHorizontalPhysicalProfile_compact t alpha)).abs
      · exact
          (normalizedProjectiveHorizontalSecondMoment_integrable t alpha).const_mul
            (q^2 / 2)
      · intro v
        rw [abs_mul]
        have hcos := abs_cos_sub_one_le (q*v)
        have hq : 0 ≤ q^2 / 2 := by positivity
        calc
          |H v| * |Real.cos (q*v) - 1|
            ≤ |H v| * ((q*v)^2 / 2) :=
              mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
          _ = q^2 / 2 * (|H v| * v^2) := by ring
    _ =
    q^2 / 2 * normalizedProjectiveHorizontalSecondMoment t alpha := by
      rw [integral_const_mul]
      rfl

/-- Quadratic signed-near compiler. -/
theorem normalizedProjectiveHorizontalQuadratic_neg_of_quadratic_near
    {t alpha q : ℝ}
    (hzero : normalizedProjectiveHorizontalQuadratic t alpha 0 < 0)
    (hnear :
      q^2 / 2 * normalizedProjectiveHorizontalSecondMoment t alpha
        <
      - normalizedProjectiveHorizontalQuadratic t alpha 0) :
    normalizedProjectiveHorizontalQuadratic t alpha q < 0 := by
  have hvar :=
    normalizedProjectiveHorizontalQuadratic_sub_zero_abs_le_sq
      t alpha q
  have hup :
      normalizedProjectiveHorizontalQuadratic t alpha q
        - normalizedProjectiveHorizontalQuadratic t alpha 0
      ≤
      q^2 / 2 * normalizedProjectiveHorizontalSecondMoment t alpha :=
    le_trans (le_abs_self _) hvar
  linarith

/-- Actual-source specialization with the synthetic q=0 sign theorem. -/
theorem normalizedProjectiveHorizontalQuadratic_actualSource_neg_of_quadratic_near
    {t : ℝ} (ht : 18 ≤ t)
    {sigma : Zeta23.Zeros}
    (hoff : heightOf sigma ≠ 0)
    (hnear :
      (normalizedGap t sigma)^2 / 2
          * normalizedProjectiveHorizontalSecondMoment t
              (normalizedHorizontalHeight t sigma)
        <
      - normalizedProjectiveHorizontalQuadratic t
          (normalizedHorizontalHeight t sigma) 0) :
    normalizedProjectiveHorizontalQuadratic t
      (normalizedHorizontalHeight t sigma)
      (normalizedGap t sigma) < 0 := by
  exact normalizedProjectiveHorizontalQuadratic_neg_of_quadratic_near
    (normalizedProjectiveHorizontalQuadratic_actualSource_zero_neg ht hoff)
    hnear

end Synthesis
