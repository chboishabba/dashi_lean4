import Mathlib
import YangMills.FiniteFeatureExponentialIntegralRP

namespace RequestProject.YangMills

example
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.SFinite μ]
    (terms : Finset I)
    (weight : I → ℝ)
    (feature : I → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hFeatureMeas : ∀ i ∈ terms, Measurable (feature i))
    (hFeatureBound : ∀ i ∈ terms, ∀ x, |feature i x| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β)
    (f : X → ℝ)
    (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f μ) :
    0 ≤ ∫ x, ∫ y,
      f x * Real.exp
        (β * finiteCrossPlaneFeatures terms weight feature x y) * f y ∂μ ∂μ :=
  finite_cross_plane_feature_exponential_integral_rp
    μ terms weight feature hweight hFeatureMeas hFeatureBound
    β hβ f hfMeas hfInt

end RequestProject.YangMills
