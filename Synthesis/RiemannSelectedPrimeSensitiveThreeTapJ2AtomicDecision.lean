import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2SmoothAtomicError
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapNearLineDecision

/-!
# Atomic-margin compiler for the transformed near-line decision

The smooth selected J2 polynomial is the exact near-line decision quantity.
The previous file gives finite-t atomic models for both of its coefficients and
exact smooth-to-atomic error decompositions.

This file packages the final scalar comparison.  It deliberately does not
assert a uniform sign of the oscillatory atomic phase.  Instead, for each
chosen height/tap strength, an atomic sign margin plus a smaller certified
smooth error compiles immediately to the actual selected smooth target sign.
-/

noncomputable section
namespace Synthesis

open scoped Real

def QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t) (eps : ℝ) : ℝ :=
  eps * W.threeTapNormalizedJ2LinearCoeff
    + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff

def QuarticFourSignedPolePair.threeTapAtomicJ2Polynomial
    {t : ℝ} (W : QuarticFourSignedPolePair t) (eps : ℝ) : ℝ :=
  eps * W.threeTapAtomicJ2LinearCoeff
    + eps^2 * W.threeTapAtomicJ2QuadraticCoeff

theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_sub_atomic
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedJ2Polynomial eps
      - W.threeTapAtomicJ2Polynomial eps
    =
    eps *
      (W.threeTapNormalizedJ2LinearCoeff
        - W.threeTapAtomicJ2LinearCoeff)
      +
    eps^2 *
      (W.threeTapNormalizedJ2QuadraticCoeff
        - W.threeTapAtomicJ2QuadraticCoeff) := by
  unfold QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial
    QuarticFourSignedPolePair.threeTapAtomicJ2Polynomial
  ring

theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_neg_of_atomic_margin
    {t eps delta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hatom : W.threeTapAtomicJ2Polynomial eps <= -delta)
    (herr :
      |W.threeTapNormalizedJ2Polynomial eps
        - W.threeTapAtomicJ2Polynomial eps| < delta) :
    W.threeTapNormalizedJ2Polynomial eps < 0 := by
  have hupper := (abs_lt.mp herr).2
  linarith

theorem QuarticFourSignedPolePair.threeTapNormalizedJ2Polynomial_pos_of_atomic_margin
    {t eps delta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hatom : delta <= W.threeTapAtomicJ2Polynomial eps)
    (herr :
      |W.threeTapNormalizedJ2Polynomial eps
        - W.threeTapAtomicJ2Polynomial eps| < delta) :
    0 < W.threeTapNormalizedJ2Polynomial eps := by
  have hlower := (abs_lt.mp herr).1
  linarith

/-- Atomic negative margin + certified smooth transfer error gives the actual
positive quadratic target band. -/
theorem QuarticFourSignedPolePair.exists_threeTapCombinedHeightDefect_pos_right_of_atomic_J2_margin
    {t eps delta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hatom : W.threeTapAtomicJ2Polynomial eps <= -delta)
    (herr :
      |W.threeTapNormalizedJ2Polynomial eps
        - W.threeTapAtomicJ2Polynomial eps| < delta) :
    ∃ d : ℝ, 0 < d ∧
      ∀ a : ℝ, 0 < a → a < d →
        0 < W.threeTapCombinedHeightDefect eps a := by
  apply W.exists_threeTapCombinedHeightDefect_pos_right_of_J2poly_neg ht
  exact W.threeTapNormalizedJ2Polynomial_neg_of_atomic_margin hatom herr

/-- Atomic positive margin + certified smooth transfer error gives the actual
negative quadratic target band, i.e. a local one-scale target failure for that
height/tap strength. -/
theorem QuarticFourSignedPolePair.exists_threeTapCombinedHeightDefect_neg_right_of_atomic_J2_margin
    {t eps delta : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hatom : delta <= W.threeTapAtomicJ2Polynomial eps)
    (herr :
      |W.threeTapNormalizedJ2Polynomial eps
        - W.threeTapAtomicJ2Polynomial eps| < delta) :
    ∃ d : ℝ, 0 < d ∧
      ∀ a : ℝ, 0 < a → a < d →
        W.threeTapCombinedHeightDefect eps a < 0 := by
  apply W.exists_threeTapCombinedHeightDefect_neg_right_of_J2poly_pos ht
  exact W.threeTapNormalizedJ2Polynomial_pos_of_atomic_margin hatom herr

/-- Exact normalized resonance coordinate.  The prime resonance is a condition
on sixteen times the normalized translation phase. -/
theorem threeTap_resonance_eq_normalized_shift
    (t : ℝ) :
    Real.cos (t * Real.log 2) = 0
      ↔
    Real.cos
      (16 * threeTapNormalizedShift t (Real.log 2)) = 0 := by
  unfold threeTapNormalizedShift
  ring_nf

end Synthesis
