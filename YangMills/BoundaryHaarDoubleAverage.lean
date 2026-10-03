import Mathlib
import Mathlib.MeasureTheory.Group.Integral

/-!
# Independent Haar pair collapses to one relative boundary variable

For a probability Haar law, either relative variable `g⁻¹ * h` or `g * h⁻¹`
is Haar whenever `g` and `h` are independent Haar variables and the matching
left/right invariance is available.  This is the exact change of variables
needed by the finite Wilson gauge-projection route: the augmented positive
quadratic form naturally carries independent boundary copies on its two half
spaces, while the literal projected Wilson kernel is written with one shared
boundary field.

The theorems are purely measure-theoretic.  They neither assume nor prove Wilson
reflection positivity; the remaining Block-A work is the same-object lattice
readback identifying the literal crossing features with a function of this
relative boundary variable.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Two independent Haar variables reduce to `g⁻¹ * h` under left invariance. -/
theorem haar_double_integral_relative_eq_single
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]
    (k : G → ℝ) :
    (∫ g, ∫ h, k (g⁻¹ * h) ∂μ ∂μ) = ∫ u, k u ∂μ := by
  have hInner : ∀ g : G, (∫ h, k (g⁻¹ * h) ∂μ) = ∫ u, k u ∂μ := by
    intro g
    exact integral_mul_left_eq_self k g⁻¹
  simp_rw [hInner]
  simp

/-- Two independent Haar variables reduce to `g * h⁻¹` under right invariance. -/
theorem haar_double_integral_mul_inv_eq_single
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulRightInvariant μ]
    (k : G → ℝ) :
    (∫ g, ∫ h, k (g * h⁻¹) ∂μ ∂μ) = ∫ u, k u ∂μ := by
  have hInner : ∀ h : G, (∫ g, k (g * h⁻¹) ∂μ) = ∫ u, k u ∂μ := by
    intro h
    exact integral_mul_right_eq_self k h⁻¹
  simp_rw [hInner]
  simp

end RequestProject.YangMills
