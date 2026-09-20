import Synthesis.RiemannNormalizedProjectiveHorizontalSourceSign
import Synthesis.RiemannNormalizedProjectiveHorizontalFarDecay

/-!
# Signed near / decaying far reduction for the actual horizontal source term

For each source zero sigma, define the near region by the exact Lipschitz sign
margin

  M1(t,alpha_sigma) * |q_sigma|
    < -Q_proj(t,alpha_sigma,0).

If sigma is critical its horizontal source term is exactly zero.  If it is
off-line and satisfies the margin, its source term is strictly negative.

On the complement, q_sigma cannot be zero.  Therefore the already-proved q^-2
oscillatory estimate applies.  This yields a one-sided majorant which charges
the signed-near region by zero and only charges the complementary sources by a
curvature/q^2 tail.

The finite aggregate theorem is exact enough to be the template for the
subsequent summable restricted-carrier attachment.
-/

noncomputable section

open Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

def normalizedProjectiveHorizontalSourceNear
    (t : ℝ) (sigma : Zeros) : Prop :=
  heightOf sigma = 0
    ∨
  normalizedProjectiveHorizontalFirstMoment t
      (normalizedHorizontalHeight t sigma)
      * |normalizedGap t sigma|
    <
  - normalizedProjectiveHorizontalQuadratic t
      (normalizedHorizontalHeight t sigma) 0

theorem normalizedProjectiveHorizontalSourceTerm_nonpos_of_near
    {t : ℝ} (ht : 18 ≤ t)
    {sigma : Zeros}
    (hnear : normalizedProjectiveHorizontalSourceNear t sigma) :
    normalizedProjectiveHorizontalSourceTerm t sigma ≤ 0 := by
  rcases hnear with hcrit | hmargin
  · rw [normalizedProjectiveHorizontalSourceTerm_eq_zero_of_critical hcrit]
  · by_cases hcrit : heightOf sigma = 0
    · rw [normalizedProjectiveHorizontalSourceTerm_eq_zero_of_critical hcrit]
    · exact
        (normalizedProjectiveHorizontalSourceTerm_neg_of_near
          ht hcrit hmargin).le

theorem normalizedProjectiveHorizontalSource_notNear_height_ne_zero
    {t : ℝ} {sigma : Zeros}
    (hfar : ¬ normalizedProjectiveHorizontalSourceNear t sigma) :
    heightOf sigma ≠ 0 := by
  intro h
  apply hfar
  exact Or.inl h

theorem normalizedProjectiveHorizontalSource_notNear_gap_ne_zero
    {t : ℝ} (ht : 18 ≤ t)
    {sigma : Zeros}
    (hfar : ¬ normalizedProjectiveHorizontalSourceNear t sigma) :
    normalizedGap t sigma ≠ 0 := by
  have hoff :=
    normalizedProjectiveHorizontalSource_notNear_height_ne_zero hfar
  have hQ0 :=
    normalizedProjectiveHorizontalQuadratic_actualSource_zero_neg ht hoff
  intro hq
  apply hfar
  right
  rw [hq, abs_zero, mul_zero]
  linarith

/-- Positive far majorant for one actual horizontal source term. -/
def normalizedProjectiveHorizontalSourceFarMajorant
    (t : ℝ) (sigma : Zeros) : ℝ :=
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
    * ((heightOf sigma)^2 / t^2)
    * (normalizedProjectiveHorizontalCurvature t
        (normalizedHorizontalHeight t sigma)
      / (normalizedGap t sigma)^2)

theorem normalizedProjectiveHorizontalSourceFarMajorant_nonneg
    {t : ℝ} (ht : 18 ≤ t)
    (sigma : Zeros) :
    0 ≤ normalizedProjectiveHorizontalSourceFarMajorant t sigma := by
  have ht0 : 0 < t := by linarith
  have hm :
      0 ≤ ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have ha : 0 ≤ (heightOf sigma)^2 / t^2 := by positivity
  have hc :=
    normalizedProjectiveHorizontalCurvature_nonneg t
      (normalizedHorizontalHeight t sigma)
  unfold normalizedProjectiveHorizontalSourceFarMajorant
  positivity

/-- Every source outside the signed-near region is bounded above by the q^-2
curvature majorant. -/
theorem normalizedProjectiveHorizontalSourceTerm_le_farMajorant_of_notNear
    {t : ℝ} (ht : 18 ≤ t)
    {sigma : Zeros}
    (hfar : ¬ normalizedProjectiveHorizontalSourceNear t sigma) :
    normalizedProjectiveHorizontalSourceTerm t sigma
      ≤ normalizedProjectiveHorizontalSourceFarMajorant t sigma := by
  have ht0 : 0 < t := by linarith
  have hq :
      normalizedGap t sigma ≠ 0 :=
    normalizedProjectiveHorizontalSource_notNear_gap_ne_zero ht hfar
  have hdecay :=
    normalizedProjectiveHorizontalQuadratic_abs_le_invSq
      (t := t)
      (alpha := normalizedHorizontalHeight t sigma)
      (q := normalizedGap t sigma)
      hq
  have hm :
      0 ≤ ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have ha :
      0 ≤ (heightOf sigma)^2 / t^2 := by positivity
  have hcoef :
      0 ≤
      ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * ((heightOf sigma)^2 / t^2) :=
    mul_nonneg hm ha
  unfold normalizedProjectiveHorizontalSourceTerm
  unfold normalizedProjectiveHorizontalSourceFarMajorant
  calc
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * ((heightOf sigma)^2 / t^2)
        * normalizedProjectiveHorizontalQuadratic t
            (normalizedHorizontalHeight t sigma)
            (normalizedGap t sigma)
      ≤
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * ((heightOf sigma)^2 / t^2)
        * |normalizedProjectiveHorizontalQuadratic t
            (normalizedHorizontalHeight t sigma)
            (normalizedGap t sigma)| := by
          exact mul_le_mul_of_nonneg_left
            (le_abs_self
              (normalizedProjectiveHorizontalQuadratic t
                (normalizedHorizontalHeight t sigma)
                (normalizedGap t sigma)))
            hcoef
    _ ≤
    ((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
        * ((heightOf sigma)^2 / t^2)
        * (normalizedProjectiveHorizontalCurvature t
            (normalizedHorizontalHeight t sigma)
          / (normalizedGap t sigma)^2) := by
          exact mul_le_mul_of_nonneg_left hdecay hcoef

/-- One-sided source majorant: signed-near sources cost zero; only the complement
pays the oscillatory far charge. -/
def normalizedProjectiveHorizontalSourceSignedMajorant
    (t : ℝ) (sigma : Zeros) : ℝ :=
  if normalizedProjectiveHorizontalSourceNear t sigma
  then 0
  else normalizedProjectiveHorizontalSourceFarMajorant t sigma

theorem normalizedProjectiveHorizontalSourceTerm_le_signedMajorant
    {t : ℝ} (ht : 18 ≤ t)
    (sigma : Zeros) :
    normalizedProjectiveHorizontalSourceTerm t sigma
      ≤ normalizedProjectiveHorizontalSourceSignedMajorant t sigma := by
  classical
  by_cases hnear : normalizedProjectiveHorizontalSourceNear t sigma
  · simp [normalizedProjectiveHorizontalSourceSignedMajorant, hnear,
      normalizedProjectiveHorizontalSourceTerm_nonpos_of_near ht hnear]
  · simp [normalizedProjectiveHorizontalSourceSignedMajorant, hnear]
    exact
      normalizedProjectiveHorizontalSourceTerm_le_farMajorant_of_notNear
        ht hnear

/-- Finite aggregate signed-near/far reduction.  No absolute value is paid on
the near region. -/
theorem sum_normalizedProjectiveHorizontalSourceTerm_le_signedMajorant
    {t : ℝ} (ht : 18 ≤ t)
    (F : Finset Zeros) :
    (∑ sigma ∈ F,
      normalizedProjectiveHorizontalSourceTerm t sigma)
      ≤
    ∑ sigma ∈ F,
      normalizedProjectiveHorizontalSourceSignedMajorant t sigma := by
  classical
  apply Finset.sum_le_sum
  intro sigma hsigma
  apply Finset.sum_le_sum
  intro _ _
  exact normalizedProjectiveHorizontalSourceTerm_le_signedMajorant ht sigma

end Synthesis
