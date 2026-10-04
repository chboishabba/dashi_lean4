import Synthesis.RiemannSelectedPrimeSensitiveThreeTapInverseSquareWindow

/-!
# Exact half-height inverse-square carrier audit

The right endpoint has already been repaired by the widened first source window.
This file removes the remaining elementary absolute-value geometry from the A1
carrier cut: every point in the exact complement of `nearOffFinset t (t/2)` is
literally in the left chart `gamma <= t/2` or the right chart `3t/2 <= gamma`.

No countable shell assignment or summation theorem is asserted here.  After
this split, that countable assignment is the only remaining carrier step.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators
open Zeta23Bridge.OffOrdinateCutoffCarrier

/-- Exact left/right chart split for the literal half-height complement. -/
theorem threeTapHalfHeightComplement_left_or_right
    {t : ℝ}
    (ht : 0 <= t)
    (sigma : ((SameOrd t)ᶜ : Set Zeros))
    (hfar : sigma ∉ nearOffFinset t (t/2)) :
    ((((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im <= t/2)
      ∨
    (3*t/2 <= (((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im) := by
  let gamma : ℝ :=
    (((sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros) : ℂ).im
  have hnotlt : ¬ |gamma - t| < t/2 := by
    intro hlt
    exact hfar ((mem_nearOffFinset_iff t (t/2) sigma).2 hlt)
  have hdist : t/2 <= |gamma-t| := le_of_not_gt hnotlt
  by_cases hgt : t <= gamma
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr hgt)] at hdist
    dsimp [gamma] at hdist ⊢
    linarith
  · left
    have hle : gamma <= t := le_of_not_ge hgt
    rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hdist
    dsimp [gamma] at hdist ⊢
    linarith

/-- The right boundary point `gamma=3t/2` is owned by the widened first source
window `(3t/2-1,2t]`.  More generally the whole first right block
`[3t/2,2t]` is contained in that literal half-open source window. -/
theorem threeTapFirstRightBlock_mem_boundarySafeWindow
    {t gamma : ℝ}
    (ht : 200 <= t)
    (hlo : 3*t/2 <= gamma)
    (hhi : gamma <= 2*t) :
    3*t/2 - 1 < gamma ∧ gamma <= 2*t := by
  constructor
  · linarith
  · exact hhi

/-- The first left dyadic chart already owns the half-height boundary because
its literal convention is `(0,t/2]` at `k=0`. -/
theorem threeTapFirstLeftBoundary_owned
    {t : ℝ} (ht : 0 < t) :
    threeTapLeftShellLower t 0 < t/2
      ∧ t/2 <= threeTapLeftShellUpper t 0 := by
  rw [threeTapLeftShellUpper_zero]
  simp [threeTapLeftShellLower, threeTapDyadicRadius]
  linarith

end Synthesis
