import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2AtomicDecision

/-!
# Fully quantitative atomic-to-smooth J2 sign regions

The normalized selected J2 polynomial and its finite atomic model are

  J_smooth(eps) = eps*A + eps^2*B,
  J_atomic(eps) = eps*a + eps^2*b.

The coefficient errors are already exact same-object quantities on this branch.
This file packages them into the polynomial envelope

  |eps| E_A + eps^2 E_B

and gives direct positive/negative sign compilers.  Thus the remaining input is
only an atomic phase margin that beats this source-written smooth-transfer
error.
-/

noncomputable section
namespace Synthesis

open scoped Real

def QuarticFourSignedPolePair.threeTapJ2LinearError
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  |W.threeTapNormalizedJ2LinearCoeff
    - W.threeTapAtomicJ2LinearCoeff|

def QuarticFourSignedPolePair.threeTapJ2QuadraticError
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  |W.threeTapNormalizedJ2QuadraticCoeff
    - W.threeTapAtomicJ2QuadraticCoeff|

def QuarticFourSignedPolePair.threeTapJ2PolynomialErrorEnvelope
    {t : ℝ} (W : QuarticFourSignedPolePair t) (eps : ℝ) : ℝ :=
  |eps| * W.threeTapJ2LinearError
    + eps^2 * W.threeTapJ2QuadraticError

theorem QuarticFourSignedPolePair.threeTapJ2LinearError_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapJ2LinearError := by
  unfold QuarticFourSignedPolePair.threeTapJ2LinearError
  exact abs_nonneg _

theorem QuarticFourSignedPolePair.threeTapJ2QuadraticError_nonneg
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapJ2QuadraticError := by
  unfold QuarticFourSignedPolePair.threeTapJ2QuadraticError
  exact abs_nonneg _

theorem QuarticFourSignedPolePair.threeTapJ2PolynomialErrorEnvelope_nonneg
    {t eps : ℝ} (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapJ2PolynomialErrorEnvelope eps := by
  unfold QuarticFourSignedPolePair.threeTapJ2PolynomialErrorEnvelope
  positivity

/-- Exact coefficient errors compile to the requested polynomial error envelope. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_sub_atomic_abs_le
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    |W.threeTapNormalizedJ2Polynomial eps
      - W.threeTapAtomicJ2Polynomial eps|
      <= W.threeTapJ2PolynomialErrorEnvelope eps := by
  rw [W.threeTapNormalizedJ2Polynomial_sub_atomic]
  calc
    |eps *
        (W.threeTapNormalizedJ2LinearCoeff
          - W.threeTapAtomicJ2LinearCoeff)
      + eps^2 *
        (W.threeTapNormalizedJ2QuadraticCoeff
          - W.threeTapAtomicJ2QuadraticCoeff)|
      <=
      |eps *
        (W.threeTapNormalizedJ2LinearCoeff
          - W.threeTapAtomicJ2LinearCoeff)|
      +
      |eps^2 *
        (W.threeTapNormalizedJ2QuadraticCoeff
          - W.threeTapAtomicJ2QuadraticCoeff)| := abs_add _ _
    _ =
      |eps| * W.threeTapJ2LinearError
        + |eps^2| * W.threeTapJ2QuadraticError := by
      unfold QuarticFourSignedPolePair.threeTapJ2LinearError
        QuarticFourSignedPolePair.threeTapJ2QuadraticError
      rw [abs_mul, abs_mul]
    _ = W.threeTapJ2PolynomialErrorEnvelope eps := by
      unfold QuarticFourSignedPolePair.threeTapJ2PolynomialErrorEnvelope
      rw [abs_of_nonneg (sq_nonneg eps)]

/-- If the atomic polynomial exceeds the full coefficient-transfer envelope,
the actual smooth selected J2 polynomial is strictly positive. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_pos_of_atomic_gt_errorEnvelope
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hmargin :
      W.threeTapJ2PolynomialErrorEnvelope eps
        < W.threeTapAtomicJ2Polynomial eps) :
    0 < W.threeTapNormalizedJ2Polynomial eps := by
  have herr := W.threeTapNormalizedJ2Polynomial_sub_atomic_abs_le (eps:=eps)
  have hlo := (abs_le.mp herr).1
  linarith

/-- Symmetric negative-margin compiler. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_neg_of_atomic_lt_neg_errorEnvelope
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hmargin :
      W.threeTapAtomicJ2Polynomial eps
        < - W.threeTapJ2PolynomialErrorEnvelope eps) :
    W.threeTapNormalizedJ2Polynomial eps < 0 := by
  have herr := W.threeTapNormalizedJ2Polynomial_sub_atomic_abs_le (eps:=eps)
  have hup := (abs_le.mp herr).2
  linarith

/-- Expanded positive phase diagram in the exact form used by the roadmap. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_pos_of_atomic_coeff_margin
    {t eps EA EB : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hEA : W.threeTapJ2LinearError <= EA)
    (hEB : W.threeTapJ2QuadraticError <= EB)
    (hmargin :
      |eps| * EA + eps^2 * EB
        < W.threeTapAtomicJ2Polynomial eps) :
    0 < W.threeTapNormalizedJ2Polynomial eps := by
  have hEAnon : 0 <= |eps| := abs_nonneg eps
  have heps2 : 0 <= eps^2 := sq_nonneg eps
  have henvelope :
      W.threeTapJ2PolynomialErrorEnvelope eps
        <= |eps| * EA + eps^2 * EB := by
    unfold QuarticFourSignedPolePair.threeTapJ2PolynomialErrorEnvelope
    gcongr
  apply W.threeTapNormalizedJ2Polynomial_pos_of_atomic_gt_errorEnvelope
  exact lt_of_le_of_lt henvelope hmargin

/-- Expanded negative phase diagram. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_neg_of_atomic_coeff_margin
    {t eps EA EB : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hEA : W.threeTapJ2LinearError <= EA)
    (hEB : W.threeTapJ2QuadraticError <= EB)
    (hmargin :
      W.threeTapAtomicJ2Polynomial eps
        < - (|eps| * EA + eps^2 * EB)) :
    W.threeTapNormalizedJ2Polynomial eps < 0 := by
  have henvelope :
      W.threeTapJ2PolynomialErrorEnvelope eps
        <= |eps| * EA + eps^2 * EB := by
    unfold QuarticFourSignedPolePair.threeTapJ2PolynomialErrorEnvelope
    gcongr
  apply W.threeTapNormalizedJ2Polynomial_neg_of_atomic_lt_neg_errorEnvelope
  linarith

end Synthesis
