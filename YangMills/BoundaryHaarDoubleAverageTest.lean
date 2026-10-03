import Mathlib
import YangMills.BoundaryHaarDoubleAverage

open MeasureTheory

namespace RequestProject.YangMills

example
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulLeftInvariant μ]
    (k : G → ℝ) :
    (∫ g, ∫ h, k (g⁻¹ * h) ∂μ ∂μ) = ∫ u, k u ∂μ :=
  haar_double_integral_relative_eq_single μ k

example
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [IsProbabilityMeasure μ] [Measure.IsMulRightInvariant μ]
    (k : G → ℝ) :
    (∫ g, ∫ h, k (g * h⁻¹) ∂μ ∂μ) = ∫ u, k u ∂μ :=
  haar_double_integral_mul_inv_eq_single μ k

end RequestProject.YangMills
