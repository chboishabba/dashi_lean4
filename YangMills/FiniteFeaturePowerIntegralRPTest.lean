import Mathlib
import YangMills.FiniteFeaturePowerIntegralRP

namespace RequestProject.YangMills

example
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    (terms : Finset I)
    (weight : I → ℝ)
    (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (n : ℕ)
    (f : X → ℝ)
    (hInt : ∀ choice : Fin n → ActiveFiniteFeature terms,
      MeasureTheory.Integrable
        (fun x => f x * finiteFeaturePowerFeature feature choice x) μ) :
    0 ≤ ∫ x, ∫ y,
      f x * (finiteCrossPlaneFeatures terms weight feature x y) ^ n * f y ∂μ ∂μ :=
  finite_cross_plane_feature_pow_integral_rp
    μ terms weight feature hweight n f hInt

end RequestProject.YangMills
