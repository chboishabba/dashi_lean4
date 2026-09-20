import Synthesis.RiemannNormalizedProjectiveHorizontalFarDecay
import Zeta23Bridge.LiteralWeilOffOrdinateTail

/-!
# Actual zeta strip bound on normalized horizontal height

For every nontrivial zeta zero,

  a_rho = Re rho - 1/2

lies in [-1/2,1/2].  The normalized projective horizontal coordinate is

  alpha_rho = a_rho / t.

Thus for t>0,

  |alpha_rho| <= 1/(2t),

and in the canonical high region t>=18,

  |alpha_rho| <= 1/36.

This attaches the exact horizontal quadratic/far-decay machinery to a uniformly
small alpha-strip on the actual zero carrier.
-/

noncomputable section

open Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail

/-- The imaginary part of gammaOf is minus horizontal height. -/
theorem gammaOf_im_eq_neg_heightOf
    (rho : Zeros) :
    (gammaOf (rho : ℂ)).im = - heightOf rho := by
  unfold gammaOf heightOf
  simp
  ring

/-- Every literal nontrivial zeta zero has horizontal displacement at most 1/2. -/
theorem abs_heightOf_le_half
    (rho : Zeros) :
    |heightOf rho| ≤ 1 / 2 := by
  have h := abs_im_gammaOf_le rho
  rw [gammaOf_im_eq_neg_heightOf, abs_neg] at h
  exact h

/-- Actual normalized horizontal coordinate is bounded by 1/(2t). -/
theorem abs_normalizedHorizontalHeight_le
    {t : ℝ} (ht : 0 < t)
    (rho : Zeros) :
    |normalizedHorizontalHeight t rho|
      ≤ 1 / (2 * t) := by
  unfold normalizedHorizontalHeight
  rw [abs_div, abs_of_pos ht]
  have h := abs_heightOf_le_half rho
  have ht0 : 0 < 2 * t := by positivity
  rw [div_le_iff₀ ht, div_eq_div_iff (by positivity : (2:ℝ) ≠ 0) (ne_of_gt ht)]
  nlinarith

/-- Uniform small-alpha strip in the canonical high region. -/
theorem abs_normalizedHorizontalHeight_le_one_div_36
    {t : ℝ} (ht : 18 ≤ t)
    (rho : Zeros) :
    |normalizedHorizontalHeight t rho| ≤ 1 / 36 := by
  have ht0 : 0 < t := by linarith
  have h := abs_normalizedHorizontalHeight_le ht0 rho
  have hscale : 1 / (2 * t) ≤ (1 / 36 : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*t)]
    norm_num
    linarith
  exact h.trans hscale

end Synthesis
