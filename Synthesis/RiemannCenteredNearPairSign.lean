import Synthesis.RiemannFinalLiteralComplementCenteredExact
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sign of centered reflection pairs inside the cosine window

For a nonpositive centered taper h and support |u| <= Lambda, a reflection pair
with ordinate gap delta satisfying |delta| Lambda <= pi/2 has nonpositive
radius-zero response.

This is the exact signed theorem available before the oscillation turns over.
It upgrades the finite near core from an arbitrary signed sum to a one-sided sum
whenever the chosen cutoff lies inside the cosine window.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

theorem cos_gap_nonneg_on_support
    {delta Lambda u : ℝ}
    (hLambda : 0 <= Lambda)
    (hu : |u| <= Lambda)
    (hwindow : |delta| * Lambda <= Real.pi / 2) :
    0 <= Real.cos (delta * u) := by
  have habs : |delta * u| <= Real.pi / 2 := by
    rw [abs_mul]
    exact le_trans
      (mul_le_mul_of_nonneg_left hu (abs_nonneg delta))
      hwindow
  apply Real.cos_nonneg_of_mem_Icc
  exact ⟨by linarith [abs_le.mp habs |>.1],
    by linarith [abs_le.mp habs |>.2]⟩

theorem reflectionPairWeight_nonpos_inside_window
    {h : ℝ -> ℝ} {a delta Lambda u : ℝ}
    (hh : ∀ x, h x <= 0)
    (hsupp : h u != 0 -> |u| <= Lambda)
    (hLambda : 0 <= Lambda)
    (hwindow : |delta| * Lambda <= Real.pi / 2) :
    reflectionPairWeight h a delta u <= 0 := by
  by_cases hu0 : h u = 0
  · simp [reflectionPairWeight, hu0]
  · have hcos : 0 <= Real.cos (delta * u) :=
      cos_gap_nonneg_on_support hLambda (hsupp hu0) hwindow
    unfold reflectionPairWeight
    have hch : 0 < Real.cosh (a * u) := Real.cosh_pos _
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0:ℝ) <= 4) (hh u))
        hch.le)
      hcos

theorem integral_reflectionPairWeight_nonpos_inside_window
    {h : ℝ -> ℝ} {a delta Lambda : ℝ}
    (hhc : Continuous h)
    (hhcs : HasCompactSupport h)
    (hh : ∀ x, h x <= 0)
    (hsupp : ∀ u, h u != 0 -> |u| <= Lambda)
    (hLambda : 0 <= Lambda)
    (hwindow : |delta| * Lambda <= Real.pi / 2) :
    (∫ u : ℝ, reflectionPairWeight h a delta u) <= 0 := by
  have hint : Integrable (fun u : ℝ => reflectionPairWeight h a delta u) :=
    Continuous.integrable_of_hasCompactSupport
      (by
        unfold reflectionPairWeight
        fun_prop)
      (by
        unfold reflectionPairWeight
        exact HasCompactSupport.mul_right
          (HasCompactSupport.mul_right
            (HasCompactSupport.mul_left hhcs)))
  have hzero : Integrable (fun _ : ℝ => (0 : ℝ)) := integrable_zero
  have hmono :
      ∀ u, reflectionPairWeight h a delta u <= 0 :=
    fun u => reflectionPairWeight_nonpos_inside_window
      hh (hsupp u) hLambda hwindow
  exact integral_nonpos_of_ae
    (Filter.Eventually.of_forall hmono)

theorem centeredPairTerm_nonpos_inside_window
    {g : ℝ -> ℝ} {Lambda t r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hnn : ∀ u, 0 <= g u)
    (hsupp : ∀ u, g u != 0 -> |u| <= Lambda)
    (hLambda : 0 <= Lambda)
    (rho : Zeros)
    (hwindow : |((rho : ℂ).im - t)| * Lambda <= Real.pi / 2) :
    zeroConeValue (gammaCenteredTaper g r) t 0 rho
      + zeroConeValue (gammaCenteredTaper g r) t 0 (reflectZero rho) <= 0 := by
  have hh2 := gammaCenteredTaper_contDiff hgs r
  have hhc := gammaCenteredTaper_hasCompactSupport hgc r
  have hhe := gammaCenteredTaper_even heven r
  have hhsupp : ∀ u, gammaCenteredTaper g r u != 0 -> |u| <= Lambda := by
    intro u hu
    apply hsupp u
    intro hgu
    apply hu
    simp [gammaCenteredTaper, hgu]
  have hpair :=
    zeroConeValue_add_reflect_eq_integral
      hh2.continuous hhc hhe t 0 rho
  simp only [zero_mul, Real.cos_zero, mul_one] at hpair
  rw [hpair]
  have hInt :=
    integral_reflectionPairWeight_nonpos_inside_window
      hh2.continuous hhc
      (gammaCenteredTaper_nonpos hnn r)
      hhsupp hLambda hwindow
      (a := heightOf rho)
      (delta := ((rho : ℂ).im - t))
  have hm : 0 <= ((Zeta23.zetaZeroConfig).mult rho : ℝ) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos hm hInt

end Synthesis
