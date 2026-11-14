import Synthesis.MillenniumBSDCMLevel32ActualEtaInfiniteNonzeroExact
import Mathlib.Tactic

/-!
# K4: strict positivity of the ORIGINAL analytic eta quotient on iℝ₊

This imports the literal mathlib Dedekind eta expression
  cmLevel32EtaAnalyticExpression z = η(4z)^2 η(8z)^2,
NOT a separate candidate, finite q-prefix, or formal positivity flag.

Mathlib v4.28 already proves η(z) ≠ 0 on the upper half-plane.
If η(4it) and η(8it) are shown to be real for t>0, then the
original expression is the product of TWO strictly positive real
squares. Thus no independent infinite-product positive LOWER BOUND
is needed. The remaining original analytic obligation is precisely
realness on the imaginary axis, plus the same-curve modularity/Mellin
identification. Eta realness is an explicit premise, not postulated.

This module is source-written for pinned local Lean kernel replay.
-/


namespace Synthesis.Millennium.BSD

open UpperHalfPlane

/-- The original imaginary-axis input really lies in the upper
half-plane, without using a symbolic "positive imaginary" flag. -/
theorem cmOriginalImaginaryAxis_mem_upperHalfPlane
    {t : ℝ} (ht : 0 < t) :
    ((t : ℂ) * Complex.I) ∈ upperHalfPlaneSet := by
  change 0 < (((t : ℂ) * Complex.I).im)
  simpa [Complex.mul_im] using ht

/-- A genuine complex eta value with zero imaginary part is
exactly the complex embedding of its real component. -/
theorem cmEta_eq_ofReal_of_im_eq_zero
    {w : ℂ} (h : w.im = 0) :
    w = (w.re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using h

/-- The ORIGINAL infinite analytic η(4it)²η(8it)² is strictly
positive on the imaginary axis as soon as BOTH actual eta factors
are proved real. Mathlib's already-established infinite product
nonvanishing pays the only remaining positivity premise. -/
theorem cmLevel32EtaAnalyticExpression_imaginary_pos_of_real
    {t : ℝ} (ht : 0 < t)
    (h4real :
      (ModularForm.eta (4 * ((t : ℂ) * Complex.I))).im = 0)
    (h8real :
      (ModularForm.eta (8 * ((t : ℂ) * Complex.I))).im = 0) :
    0 < (cmLevel32EtaAnalyticExpression
      ((t : ℂ) * Complex.I)).re := by
  let z : ℂ := (t : ℂ) * Complex.I
  have hz : z ∈ upperHalfPlaneSet :=
    cmOriginalImaginaryAxis_mem_upperHalfPlane ht
  have hn4 : ModularForm.eta (4 * z) ≠ 0 :=
    ModularForm.eta_ne_zero (cmUpperHalfPlane_scale_four hz)
  have hn8 : ModularForm.eta (8 * z) ≠ 0 :=
    ModularForm.eta_ne_zero (cmUpperHalfPlane_scale_eight hz)
  have hr4 : ModularForm.eta (4 * z) =
      ((ModularForm.eta (4 * z)).re : ℂ) :=
    cmEta_eq_ofReal_of_im_eq_zero (by simpa [z] using h4real)
  have hr8 : ModularForm.eta (8 * z) =
      ((ModularForm.eta (8 * z)).re : ℂ) :=
    cmEta_eq_ofReal_of_im_eq_zero (by simpa [z] using h8real)
  have h4ne : (ModularForm.eta (4 * z)).re ≠ 0 := by
    intro h
    apply hn4
    calc
      ModularForm.eta (4 * z) =
        ((ModularForm.eta (4 * z)).re : ℂ) := hr4
      _ = 0 := by simp [h]
  have h8ne : (ModularForm.eta (8 * z)).re ≠ 0 := by
    intro h
    apply hn8
    calc
      ModularForm.eta (8 * z) =
        ((ModularForm.eta (8 * z)).re : ℂ) := hr8
      _ = 0 := by simp [h]
  have hp4 : 0 < ((ModularForm.eta (4 * z)).re) ^ 2 :=
    sq_pos_of_ne_zero h4ne
  have hp8 : 0 < ((ModularForm.eta (8 * z)).re) ^ 2 :=
    sq_pos_of_ne_zero h8ne
  have hproduct :
      0 < ((ModularForm.eta (4 * z)).re) ^ 2 *
          ((ModularForm.eta (8 * z)).re) ^ 2 :=
    mul_pos hp4 hp8
  change 0 < (cmLevel32EtaAnalyticExpression z).re
  have hrealProduct :
      (cmLevel32EtaAnalyticExpression z).re =
      ((ModularForm.eta (4 * z)).re) ^ 2 *
      ((ModularForm.eta (8 * z)).re) ^ 2 := by
    simp [cmLevel32EtaAnalyticExpression, hr4, hr8]
  exact hrealProduct ▸ hproduct

end Synthesis.Millennium.BSD
