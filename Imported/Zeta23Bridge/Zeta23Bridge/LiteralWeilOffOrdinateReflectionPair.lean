/-
# Signed off-ordinate reflection pairs before absolute majorization

The absolute off-ordinate envelope loses the functional-equation pairing before it
estimates the zero tail.  This module keeps that pairing exact.

For a zero of horizontal height `a` and ordinate gap `δ = b - t`, the two-sample
cone kernel is

  2 g(u) [cosh(a u) cos(δ u) + sinh(a u) sin(δ u)].

Its functional-equation reflection has height `-a` and the same ordinate, hence
the same gap `δ`.  Adding the two kernels cancels the odd-height term exactly:

  K(a,δ;u) + K(-a,δ;u) = 4 g(u) cosh(a u) cos(δ u).

Thus a reflection pair is controlled by a signed oscillatory cosine kernel rather
than by the positive scalar weight used by the old `W(t)` majorant.  This is the
literal structural input needed by the next tail estimate.
-/
import Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilOffOrdinateReflectionPair

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail

/-- The signed kernel of a functional-equation reflection pair. -/
def reflectionPairWeight (g : ℝ → ℝ) (a δ : ℝ) : ℝ → ℝ :=
  fun u => 4 * g u * Real.cosh (a * u) * Real.cos (δ * u)

/-- Pointwise, reflection pairing cancels the `sinh(a u) sin(δ u)` term exactly. -/
theorem zeroChannelWeight_add_reflect (g : ℝ → ℝ) (a δ u : ℝ) :
    zeroChannelWeight g a δ u + zeroChannelWeight g (-a) δ u
      = reflectionPairWeight g a δ u := by
  unfold zeroChannelWeight reflectionPairWeight
  rw [show -a * u = -(a * u) by ring, Real.cosh_neg, Real.sinh_neg]
  ring

/-- The two-sample response of a reflection pair is a pure cosine transform in the
ordinate gap.  No absolute value has been taken. -/
theorem coneResp_add_reflect_eq_integral {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (a δ s : ℝ) :
    coneResp g a δ s + coneResp g (-a) δ s
      = ∫ u : ℝ, reflectionPairWeight g a δ u * Real.cos (s * u) := by
  rw [coneResp_eq_integral hg hgc a δ s, coneResp_eq_integral hg hgc (-a) δ s]
  have h1 : Integrable (fun u : ℝ => zeroChannelWeight g a δ u * Real.cos (s * u)) :=
    Continuous.integrable_of_hasCompactSupport
      ((zeroChannelWeight_continuous hg a δ).mul (by fun_prop))
      (zeroChannelWeight_hasCompactSupport hgc a δ).mul_right
  have h2 : Integrable (fun u : ℝ => zeroChannelWeight g (-a) δ u * Real.cos (s * u)) :=
    Continuous.integrable_of_hasCompactSupport
      ((zeroChannelWeight_continuous hg (-a) δ).mul (by fun_prop))
      (zeroChannelWeight_hasCompactSupport hgc (-a) δ).mul_right
  rw [← integral_add h1 h2]
  congr 1
  funext u
  rw [← add_mul, zeroChannelWeight_add_reflect]

/-- At sampling radius zero the paired response is exactly the signed oscillatory
integral `4 ∫ g cosh(a·) cos(δ·)`. -/
theorem coneResp_add_reflect_zero {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (a δ : ℝ) :
    coneResp g a δ 0 + coneResp g (-a) δ 0
      = ∫ u : ℝ, reflectionPairWeight g a δ u := by
  rw [coneResp_add_reflect_eq_integral hg hgc a δ 0]
  simp

/-- The same identity after the exact projective taper.  This is the paired
projective-defect kernel used by the high-ordinate tail problem. -/
theorem projTaper_coneResp_add_reflect_zero {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (a δ r : ℝ) :
    coneResp (projTaper g r) a δ 0 + coneResp (projTaper g r) (-a) δ 0
      = ∫ u : ℝ, reflectionPairWeight (projTaper g r) a δ u := by
  exact coneResp_add_reflect_zero (projTaper_continuous hg r)
    (projTaper_hasCompactSupport hgc r) a δ

/-- Reflection negates horizontal height. -/
theorem heightOf_reflectZero (ρ : Zeros) :
    heightOf (reflectZero ρ) = -heightOf ρ := by
  unfold heightOf reflectZero
  simp only [Zeta23.reflect_re]
  ring

/-- Reflection preserves the ordinate, hence also preserves the target-relative
ordinate gap. -/
theorem im_reflectZero (ρ : Zeros) :
    ((reflectZero ρ : Zeros) : ℂ).im = (ρ : ℂ).im := by
  exact Zeta23.reflect_im (ρ : ℂ)

/-- The literal two-sample cone values of an actual zero and its reflection pair
collapse to the signed paired kernel, with the genuine common multiplicity. -/
theorem zeroConeValue_add_reflect {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t s : ℝ) (ρ : Zeros) :
    zeroConeValue g t s ρ + zeroConeValue g t s (reflectZero ρ)
      = ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
          * (coneResp g (heightOf ρ) ((ρ : ℂ).im - t) s
            + coneResp g (-heightOf ρ) ((ρ : ℂ).im - t) s) := by
  rw [zeroConeValue_eq_coneResp hg hgc heven t s ρ,
    zeroConeValue_eq_coneResp hg hgc heven t s (reflectZero ρ),
    reflectZero_mult, heightOf_reflectZero, im_reflectZero]
  ring

/-- Fully expanded literal pair response: multiplicity times the signed oscillatory
cosine transform. -/
theorem zeroConeValue_add_reflect_eq_integral {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t s : ℝ) (ρ : Zeros) :
    zeroConeValue g t s ρ + zeroConeValue g t s (reflectZero ρ)
      = ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
          * ∫ u : ℝ, reflectionPairWeight g (heightOf ρ) ((ρ : ℂ).im - t) u
              * Real.cos (s * u) := by
  rw [zeroConeValue_add_reflect hg hgc heven t s ρ,
    coneResp_add_reflect_eq_integral hg hgc (heightOf ρ) ((ρ : ℂ).im - t) s]

end LiteralWeilOffOrdinateReflectionPair
end Zeta23Bridge
