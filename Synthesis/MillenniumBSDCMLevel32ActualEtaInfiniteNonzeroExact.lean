import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Tactic

/-!
# K4: actual infinite Dedekind eta product for the selected level-32 form

Unlike finite q truncations, this module uses Mathlib's REAL infinite
Dedekind eta product as a function on the upper complex half-plane.
The same pinned mathlib v4.28.0 already proves
  ModularForm.eta_ne_zero
by summability and the nonzero infinite-product theorem.

The analytically selected weight-2 form is the expression
  f₃₂(z) = eta(4z)^2 eta(8z)^2.
Its NONVANISHING on the upper half-plane is established here,
without assuming a product limit is positive.

THIS IS NOT CENTRAL L-NONVANISHING:
we still owe the modular-form identification with the curve
y²=x³−x, its exact Mellin transform, and positivity of the
integral at s=1. A nonzero holomorphic function can have
a zero Mellin transform without additional analysis.

Source attribution: Mathlib.NumberTheory.ModularForms.DedekindEta
(Birkbeck, Loeffler); external same-form identity and special
value: Huber–Liu–McLaughlin–Ye–Yuan–Zhang, Computing Special
L-Values of Certain Modular Forms with CM.
Exact-head pinned Lean kernel acceptance remains pending.
-/

namespace Synthesis.Millennium.BSD

open UpperHalfPlane

/-- The ORIGINAL infinite eta-product expression for level 32,
formed from Mathlib's already-existing Dedekind eta function.
No finite truncation or synthetic analytic carrier. -/
noncomputable def cmLevel32EtaAnalyticExpression (z : ℂ) : ℂ :=
  ModularForm.eta (4 * z) ^ 2 * ModularForm.eta (8 * z) ^ 2

/-- Positive imaginary part survives scaling by 4. -/
theorem cmUpperHalfPlane_scale_four
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    (4 : ℂ) * z ∈ upperHalfPlaneSet := by
  have hzIm : 0 < z.im := hz
  change 0 < ((4 : ℂ) * z).im
  simpa [Complex.mul_im] using
    (mul_pos (show (0 : ℝ) < 4 by norm_num) hzIm)

/-- Positive imaginary part survives scaling by 8. -/
theorem cmUpperHalfPlane_scale_eight
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    (8 : ℂ) * z ∈ upperHalfPlaneSet := by
  have hzIm : 0 < z.im := hz
  change 0 < ((8 : ℂ) * z).im
  simpa [Complex.mul_im] using
    (mul_pos (show (0 : ℝ) < 8 by norm_num) hzIm)

/-- Genuine INFINITE eta-product nonvanishing at every point of the
upper half-plane, directly consuming Mathlib's actual eta theorem. -/
theorem cmLevel32EtaAnalyticExpression_ne_zero
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    cmLevel32EtaAnalyticExpression z ≠ 0 := by
  unfold cmLevel32EtaAnalyticExpression
  exact mul_ne_zero
    (pow_ne_zero 2 (ModularForm.eta_ne_zero
      (cmUpperHalfPlane_scale_four hz)))
    (pow_ne_zero 2 (ModularForm.eta_ne_zero
      (cmUpperHalfPlane_scale_eight hz)))

end Synthesis.Millennium.BSD
