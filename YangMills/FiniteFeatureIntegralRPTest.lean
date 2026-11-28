import Mathlib
import YangMills.FiniteFeatureIntegralRP

namespace RequestProject.YangMills

example
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    (terms : Finset I)
    (weight : I → ℝ)
    (feature : I → X → ℝ)
    (f : X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hInt : ∀ i ∈ terms,
      MeasureTheory.Integrable (fun x => f x * feature i x) μ) :
    0 ≤ ∫ x, ∫ y,
      f x * finiteCrossPlaneFeatures terms weight feature x y * f y ∂μ ∂μ :=
  finite_cross_plane_feature_integral_rp
    μ terms weight feature f hweight hInt

end RequestProject.YangMills
