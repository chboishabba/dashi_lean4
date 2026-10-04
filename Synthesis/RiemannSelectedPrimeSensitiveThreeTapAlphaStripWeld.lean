import Synthesis.RiemannSelectedPrimeSensitiveThreeTapKernelAlphaEnvelope

/-!
# Canonical normalized horizontal strip for zeta zeros

The external Zeta23 zero package already owns the standard critical-strip
bound

  |heightOf rho| <= 1/2.

For the selected normalized scale r=t/16 this becomes

  |heightOf rho / r| <= 8/t.

Thus the alpha envelope introduced by the adverse pair cut has a canonical
source-written radius; no additional horizontal-strip hypothesis remains.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- Canonical normalized horizontal radius at height t. -/
def threeTapCanonicalAlphaRadius (t : ℝ) : ℝ := 8/t

theorem threeTapCanonicalAlphaRadius_nonneg
    {t : ℝ} (ht : 0 < t) :
    0 <= threeTapCanonicalAlphaRadius t := by
  unfold threeTapCanonicalAlphaRadius
  positivity

/-- Standard zeta critical-strip bound at the selected normalized scale. -/
theorem QuarticFourSignedPolePair.abs_normalized_height_le_canonicalAlphaRadius
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    |heightOf rho / (t/16)| <= threeTapCanonicalAlphaRadius t := by
  have hr : 0 < t/16 := by positivity
  have hz := zetaZero_height_abs_le_half rho
  rw [abs_div, abs_of_pos hr]
  unfold threeTapCanonicalAlphaRadius
  have hdiv :
      |heightOf rho| / (t/16) <= (1/2 : ℝ) / (t/16) :=
    div_le_div_of_nonneg_right hz hr.le
  calc
    |heightOf rho| / (t/16)
      <= (1/2 : ℝ) / (t/16) := hdiv
    _ = 8/t := by
      field_simp [ne_of_gt ht]
      ring

/-- The abstract alpha-strip premise is discharged canonically for every
selected off-ordinate zero. -/
theorem QuarticFourSignedPolePair.threeTapAlphaStripBound_canonical
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.ThreeTapAlphaStripBound (threeTapCanonicalAlphaRadius t) := by
  intro sigma
  exact W.abs_normalized_height_le_canonicalAlphaRadius ht (sigma : Zeros)

end Synthesis
