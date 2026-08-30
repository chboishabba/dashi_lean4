/-
# The literal reflection-pair response decays quadratically in the ordinate gap

`LiteralWeilOffOrdinateReflectionPair` collapses a functional-equation pair of
zeros to the signed kernel

    reflectionPairWeight g a δ u = 4 g(u) cosh(a u) cos(δ u),

and `OscillatoryKernelDecay` proves that a compactly supported `C²` weight
integrated against `cos(δ·)` is `O(δ⁻²)`.  This module puts the two together on
the literal zeta carrier: the response of an actual reflection pair at ordinate
gap `δ = Im ρ − t` is bounded by

    m_ρ · ‖(4 g cosh(a ·))''‖₁ / δ²,

with no absolute value taken inside the oscillation.  This is the per-zero decay
the signed tail estimate needs; the positive scalar majorant `W(t)` provides no
such decay.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
import Zeta23Bridge.OscillatoryKernelDecay

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace ReflectionPairKernelDecay

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.OscillatoryKernelDecay

/-- The even weight carried by a reflection pair of horizontal height `a`. -/
def pairWeight (g : ℝ → ℝ) (a : ℝ) : ℝ → ℝ := fun u => 4 * g u * Real.cosh (a * u)

/-- The total variation of its second derivative — the constant in the decay
estimate. -/
def pairWeightCurvature (g : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ u : ℝ, |deriv (deriv (pairWeight g a)) u|

theorem pairWeight_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (a : ℝ) :
    ContDiff ℝ 2 (pairWeight g a) := by
  unfold pairWeight
  exact (contDiff_const.mul hg).mul (by fun_prop)

theorem pairWeight_hasCompactSupport {g : ℝ → ℝ} (hgc : HasCompactSupport g) (a : ℝ) :
    HasCompactSupport (pairWeight g a) := by
  unfold pairWeight
  exact HasCompactSupport.mul_right (HasCompactSupport.mul_left hgc)

theorem reflectionPairWeight_eq_pairWeight_mul_cos (g : ℝ → ℝ) (a δ u : ℝ) :
    reflectionPairWeight g a δ u = pairWeight g a u * Real.cos (δ * u) := by
  unfold reflectionPairWeight pairWeight
  ring

/-- **Quadratic decay of the signed reflection-pair kernel.** -/
theorem abs_integral_reflectionPairWeight_le {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (a : ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    |∫ u : ℝ, reflectionPairWeight g a δ u| ≤ pairWeightCurvature g a / δ ^ 2 := by
  have hrw : (∫ u : ℝ, reflectionPairWeight g a δ u)
      = ∫ u : ℝ, pairWeight g a u * Real.cos (δ * u) := by
    simp only [reflectionPairWeight_eq_pairWeight_mul_cos]
  rw [hrw]
  exact abs_integral_mul_cos_le (pairWeight_contDiff hg a) (pairWeight_hasCompactSupport hgc a) hδ

/-- **The literal per-pair bound on the zeta carrier.**  The two-sample cone
response of an actual zero together with its functional-equation reflection is
bounded by the multiplicity times an explicit curvature constant divided by the
square of the ordinate gap. -/
theorem abs_zeroConeValue_add_reflect_le {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (t : ℝ) (ρ : Zeros) (hδ : ((ρ : ℂ).im - t) ≠ 0) :
    |zeroConeValue g t 0 ρ + zeroConeValue g t 0 (reflectZero ρ)|
      ≤ ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
          * (pairWeightCurvature g (heightOf ρ) / ((ρ : ℂ).im - t) ^ 2) := by
  have hpair := zeroConeValue_add_reflect_eq_integral hg.continuous hgc heven t 0 ρ
  simp only [zero_mul, Real.cos_zero, mul_one] at hpair
  rw [hpair, abs_mul]
  have hmult : |((Zeta23.zetaZeroConfig).mult ρ : ℝ)| = ((Zeta23.zetaZeroConfig).mult ρ : ℝ) :=
    abs_of_nonneg (by positivity)
  rw [hmult]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact abs_integral_reflectionPairWeight_le hg hgc (heightOf ρ) hδ

end ReflectionPairKernelDecay
end Zeta23Bridge
