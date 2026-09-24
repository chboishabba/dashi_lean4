import Synthesis.RiemannNormalizedProjectiveHorizontalUniformSign
import Synthesis.RiemannProjectiveHorizontalTargetFactorFirewall

/-!
# Actual-source signed near region for the projective horizontal term

The synthetic q=0 theorem removes the old same-ordinate realization premise.
For every actual off-line source zero sigma,

  Q_proj(t, alpha_sigma, 0) < 0.

The existing q-Lipschitz theorem therefore gives a signed near-ordinate region
around the target ordinate.  Inside that region the *actual source horizontal
term* is strictly negative, because its multiplicity and horizontal-square
prefactor are strictly positive.

This is a pointwise source theorem.  It deliberately does not replace the
remaining far-q aggregate by an absolute global budget.
-/

noncomputable section

open Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

theorem normalizedHorizontalHeight_ne_zero_of_height_ne_zero
    {t : ℝ} (ht : t ≠ 0)
    {sigma : Zeros}
    (hoff : heightOf sigma ≠ 0) :
    normalizedHorizontalHeight t sigma ≠ 0 := by
  unfold normalizedHorizontalHeight
  exact div_ne_zero hoff ht

/-- Every actual off-line source zero has a strictly negative q=0 horizontal
quadratic anchor. -/
theorem normalizedProjectiveHorizontalQuadratic_actualSource_zero_neg
    {t : ℝ} (ht : 18 ≤ t)
    {sigma : Zeros}
    (hoff : heightOf sigma ≠ 0) :
    normalizedProjectiveHorizontalQuadratic t
      (normalizedHorizontalHeight t sigma) 0 < 0 := by
  have ht0 : t ≠ 0 := by linarith
  exact normalizedProjectiveHorizontalQuadratic_zero_neg
    ht
    (normalizedHorizontalHeight_ne_zero_of_height_ne_zero ht0 hoff)

/-- Signed near-q theorem at the actual normalized ordinate gap of a source
zero. -/
theorem normalizedProjectiveHorizontalQuadratic_actualSource_neg_of_near
    {t : ℝ} (ht : 18 ≤ t)
    {sigma : Zeros}
    (hoff : heightOf sigma ≠ 0)
    (hnear :
      normalizedProjectiveHorizontalFirstMoment t
          (normalizedHorizontalHeight t sigma)
          * |normalizedGap t sigma|
        <
      - normalizedProjectiveHorizontalQuadratic t
          (normalizedHorizontalHeight t sigma) 0) :
    normalizedProjectiveHorizontalQuadratic t
      (normalizedHorizontalHeight t sigma)
      (normalizedGap t sigma) < 0 := by
  exact normalizedProjectiveHorizontalQuadratic_neg_of_near_zero
    (normalizedProjectiveHorizontalQuadratic_actualSource_zero_neg ht hoff)
    hnear

/-- The literal normalized horizontal source term is strictly negative in the
signed near region. -/
theorem normalizedProjectiveHorizontalSourceTerm_neg_of_near
    {t : ℝ} (ht : 18 ≤ t)
    {sigma : Zeros}
    (hoff : heightOf sigma ≠ 0)
    (hnear :
      normalizedProjectiveHorizontalFirstMoment t
          (normalizedHorizontalHeight t sigma)
          * |normalizedGap t sigma|
        <
      - normalizedProjectiveHorizontalQuadratic t
          (normalizedHorizontalHeight t sigma) 0) :
    normalizedProjectiveHorizontalSourceTerm t sigma < 0 := by
  have htpos : 0 < t := by linarith
  have hQ :=
    normalizedProjectiveHorizontalQuadratic_actualSource_neg_of_near
      ht hoff hnear
  have hmNat :
      (1 : ℕ) ≤ (zetaZeroConfig).mult (sigma : ℂ) :=
    (zetaZeroConfig).one_le_mult (sigma : ℂ) sigma.2
  have hm :
      0 < ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by
    exact_mod_cast hmNat
  have ha2 :
      0 < (heightOf sigma)^2 / t^2 := by
    exact div_pos (sq_pos_of_ne_zero hoff) (sq_pos_of_pos htpos)
  unfold normalizedProjectiveHorizontalSourceTerm
  exact mul_neg_of_pos_of_neg (mul_pos hm ha2) hQ

end Synthesis
