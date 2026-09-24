import Synthesis.RiemannNormalizedProjectiveOffHorizontalSplit

/-!
# Exact quadratic factorization of the projective horizontal correction

The normalized projective atom splits exactly into a q-only base plus a
horizontal correction.  The latter contains the universal factor

  cosh(alpha v) - 1,

which vanishes to second order at alpha=0.

Rather than estimate this factor, define its exact divided-square kernel and
factor alpha^2 *before* any zero summation.  This preserves sign information and
makes the near-line scale explicit:

  E_proj(t,alpha,q) = alpha^2 Q_proj(t,alpha,q).

For an actual zero, alpha = heightOf(rho)/t, hence the correction is exactly

  (heightOf(rho)^2 / t^2) Q_proj(...).

Crucial scope note: for an aggregate over source zeros sigma, this factor is
a_sigma^2, not the hypothetical target zero's a_rho^2.  Therefore this
factorization removes the critical-line constant part of each source atom, but
does NOT by itself solve the uniform near-line comparison against D_rho ~
a_rho^2.  A signed aggregate theorem or an additional relation between source
and target displacements is still required.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23

/-- Exact continuous-extension-style quotient.  Its alpha=0 value is immaterial
for the factorization theorem because it is multiplied by alpha^2. -/
def coshMinusOneDivSq (alpha v : ℝ) : ℝ :=
  if alpha = 0 then v ^ 2 / 2
  else (Real.cosh (alpha * v) - 1) / alpha ^ 2

theorem cosh_sub_one_eq_sq_mul_divSq (alpha v : ℝ) :
    Real.cosh (alpha * v) - 1
      = alpha ^ 2 * coshMinusOneDivSq alpha v := by
  by_cases ha : alpha = 0
  · subst alpha
    simp [coshMinusOneDivSq]
  · rw [coshMinusOneDivSq, if_neg ha]
    field_simp [ha]

def normalizedCenteredHorizontalQuadraticAtScale
    (t k alpha q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCenteredFixedProfileAtScale t k v
      * coshMinusOneDivSq alpha v
      * Real.cos (q * v)

def normalizedRadiusZeroHorizontalQuadratic
    (t alpha q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCanonicalFixedProfile t v
      * coshMinusOneDivSq alpha v
      * Real.cos (q * v)

theorem normalizedCenteredHorizontalCorrectionAtScale_eq_sq_mul
    (t k alpha q : ℝ) :
    normalizedCenteredHorizontalCorrectionAtScale t k alpha q
      =
    alpha ^ 2 *
      normalizedCenteredHorizontalQuadraticAtScale t k alpha q := by
  unfold normalizedCenteredHorizontalCorrectionAtScale
    normalizedCenteredHorizontalQuadraticAtScale
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    rw [cosh_sub_one_eq_sq_mul_divSq]
    ring

theorem normalizedRadiusZeroHorizontalCorrection_eq_sq_mul
    (t alpha q : ℝ) :
    normalizedRadiusZeroHorizontalCorrection t alpha q
      =
    alpha ^ 2 *
      normalizedRadiusZeroHorizontalQuadratic t alpha q := by
  unfold normalizedRadiusZeroHorizontalCorrection
    normalizedRadiusZeroHorizontalQuadratic
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    rw [cosh_sub_one_eq_sq_mul_divSq]
    ring

/-- The exact projective divided-square horizontal consumer. -/
def normalizedProjectiveHorizontalQuadratic
    (t alpha q : ℝ) : ℝ :=
  normalizedCenteredHorizontalQuadraticAtScale t 2 alpha q
      * onLineRadiusProfile (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t)
    - normalizedCenteredHorizontalQuadraticAtScale t 1 alpha q
      * onLineRadiusProfile (quantitativeCanonicalTaper t)
          (2 * quantitativeSampleRadius t)
    + normalizedRadiusZeroHorizontalQuadratic t alpha q
      * (onLineRadiusProfile (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t)
          - onLineRadiusProfile (quantitativeCanonicalTaper t)
            (2 * quantitativeSampleRadius t))

/-- Exact second-order factorization of the same projective horizontal
correction consumed by the normalized projective atom. -/
theorem normalizedProjectiveHorizontalCorrection_eq_sq_mul
    (t alpha q : ℝ) :
    normalizedProjectiveHorizontalCorrection t alpha q
      =
    alpha ^ 2 * normalizedProjectiveHorizontalQuadratic t alpha q := by
  rw [normalizedCenteredHorizontalCorrectionAtScale_eq_sq_mul
        t 2 alpha q,
      normalizedCenteredHorizontalCorrectionAtScale_eq_sq_mul
        t 1 alpha q,
      normalizedRadiusZeroHorizontalCorrection_eq_sq_mul
        t alpha q]
  unfold normalizedProjectiveHorizontalCorrection
    normalizedProjectiveHorizontalQuadratic
  ring

/-- Exact projective atom split with the horizontal square factored before any
finite or infinite summation. -/
theorem normalizedProjectiveOffZeroAtom_eq_base_add_sq_horizontal
    (t : ℝ) (rho : Zeros) :
    normalizedProjectiveOffZeroAtom t rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedProjectiveBaseTransform t (normalizedGap t rho)
      +
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * (normalizedHorizontalHeight t rho) ^ 2
      * normalizedProjectiveHorizontalQuadratic t
          (normalizedHorizontalHeight t rho) (normalizedGap t rho) := by
  rw [normalizedProjectiveOffZeroAtom_eq_base_add_horizontal]
  rw [normalizedProjectiveHorizontalCorrection_eq_sq_mul]
  ring

theorem normalizedHorizontalHeight_sq
    {t : ℝ} (ht : t ≠ 0) (rho : Zeros) :
    (normalizedHorizontalHeight t rho) ^ 2
      = (heightOf rho) ^ 2 / t ^ 2 := by
  unfold normalizedHorizontalHeight
  field_simp [ht]
  ring

/-- Literal actual-zero version: the projective horizontal piece carries the
explicit horizontal-height square divided by t^2. -/
theorem normalizedProjectiveOffZeroAtom_eq_base_add_heightSq_horizontal
    {t : ℝ} (ht : t ≠ 0) (rho : Zeros) :
    normalizedProjectiveOffZeroAtom t rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedProjectiveBaseTransform t (normalizedGap t rho)
      +
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * ((heightOf rho) ^ 2 / t ^ 2)
      * normalizedProjectiveHorizontalQuadratic t
          (normalizedHorizontalHeight t rho) (normalizedGap t rho) := by
  rw [normalizedProjectiveOffZeroAtom_eq_base_add_sq_horizontal]
  rw [normalizedHorizontalHeight_sq ht rho]

end Synthesis
