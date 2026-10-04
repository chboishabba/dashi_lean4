import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveGlobal
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapJ2Atomic

/-!
# Decisive near-line target fork for the one-scale three-tap family

The exact normalized J2 polynomial now decides the sign of the transformed
same-ordinate target at the first nonzero order.

If the polynomial is negative, D''(0)>0 and the transformed target is strictly
positive on a right punctured neighborhood.
If the polynomial is positive, D''(0)<0 and the transformed target is strictly
negative on a right punctured neighborhood.

The exceptional zero-polynomial locus is the only branch on which quartic J4
analysis is needed.
-/

noncomputable section
namespace Synthesis

open scoped Real

theorem QuarticFourSignedPolePair.threeTapCombinedHeightDefect_zero
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCombinedHeightDefect eps 0 = 0 := by
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightDefect
  rw [heightDefect_at_zero_height, heightDefect_at_zero_height]
  ring

theorem QuarticFourSignedPolePair.threeTapCombinedHeightD1_zero
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCombinedHeightD1 eps 0 = 0 := by
  unfold QuarticFourSignedPolePair.threeTapCombinedHeightD1
    compactCoshD1
  simp

theorem QuarticFourSignedPolePair.threeTapCombinedHeightD2_continuous
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    Continuous (W.threeTapCombinedHeightD2 eps) := by
  apply continuous_iff_continuousAt.2
  intro a
  exact (W.threeTapCombinedHeightD2_hasDerivAt
    (eps:=eps) ht (a:=a)).continuousAt

/-- Negative normalized J2 polynomial gives a genuine positive quadratic target
band.  This is the generic one-scale near-line PASS condition for the target
component. -/
theorem QuarticFourSignedPolePair.exists_threeTapCombinedHeightDefect_pos_right_of_J2poly_neg
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hneg :
      eps * W.threeTapNormalizedJ2LinearCoeff
        + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff < 0) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapCombinedHeightDefect eps a := by
  have h2 :
      0 < W.threeTapCombinedHeightD2 eps 0 :=
    W.threeTap_target_quadratic_positive_of_J2poly_neg ht hneg
  exact
    exists_pos_right_of_second_deriv_pos
      (f := W.threeTapCombinedHeightDefect eps)
      (f1 := W.threeTapCombinedHeightD1 eps)
      (f2 := W.threeTapCombinedHeightD2 eps)
      (fun a => W.threeTapCombinedHeight_hasDerivAt ht)
      (fun a => W.threeTapCombinedHeightD1_hasDerivAt ht)
      (W.threeTapCombinedHeightD2_continuous ht)
      W.threeTapCombinedHeightDefect_zero
      W.threeTapCombinedHeightD1_zero
      h2

/-- Positive normalized J2 polynomial gives the opposite target sign on a
right punctured neighborhood.  Thus such a tap strength cannot inherit the
old positive-target quartic mechanism. -/
theorem QuarticFourSignedPolePair.exists_threeTapCombinedHeightDefect_neg_right_of_J2poly_pos
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hpos :
      0 <
      eps * W.threeTapNormalizedJ2LinearCoeff
        + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapCombinedHeightDefect eps a < 0 := by
  have h2 :
      W.threeTapCombinedHeightD2 eps 0 < 0 :=
    W.threeTap_target_quadratic_negative_of_J2poly_pos ht hpos
  have hposNeg :
      0 < - W.threeTapCombinedHeightD2 eps 0 := by
    linarith
  obtain ⟨delta,hdelta,hband⟩ :=
    exists_pos_right_of_second_deriv_pos
      (f := fun a => - W.threeTapCombinedHeightDefect eps a)
      (f1 := fun a => - W.threeTapCombinedHeightD1 eps a)
      (f2 := fun a => - W.threeTapCombinedHeightD2 eps a)
      (fun a => (W.threeTapCombinedHeight_hasDerivAt ht).neg)
      (fun a => (W.threeTapCombinedHeightD1_hasDerivAt ht).neg)
      (W.threeTapCombinedHeightD2_continuous ht).neg
      (by rw [W.threeTapCombinedHeightDefect_zero]; ring)
      (by rw [W.threeTapCombinedHeightD1_zero]; ring)
      hposNeg
  refine ⟨delta,hdelta,?_⟩
  intro a ha had
  have h := hband a ha had
  linarith

/-- For a nonzero tap, exactly one of the generic quadratic branches or the
single exceptional quartic equation holds. -/
theorem QuarticFourSignedPolePair.threeTap_nearLine_trichotomy
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (heps : eps ≠ 0) :
    (
      eps * W.threeTapNormalizedJ2LinearCoeff
        + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff < 0
    )
    ∨
    (
      eps * W.threeTapNormalizedJ2LinearCoeff
        + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff = 0
    )
    ∨
    (
      0 <
      eps * W.threeTapNormalizedJ2LinearCoeff
        + eps^2 * W.threeTapNormalizedJ2QuadraticCoeff
    ) := by
  exact lt_trichotomy _ 0

end Synthesis
