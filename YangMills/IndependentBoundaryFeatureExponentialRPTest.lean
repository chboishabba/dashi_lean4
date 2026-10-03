import Mathlib
import YangMills.IndependentBoundaryFeatureExponentialRP

namespace RequestProject.YangMills

example
    {B X I : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (boundaryHaar : MeasureTheory.Measure B) [MeasureTheory.IsFiniteMeasure boundaryHaar]
    (positiveHaar : MeasureTheory.Measure X) [MeasureTheory.SFinite positiveHaar]
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → B → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hMeas : ∀ i ∈ terms, Measurable (Function.uncurry (feature i)))
    (hBound : ∀ i ∈ terms, ∀ b x, |feature i b x| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β)
    (f : X → ℝ) (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f positiveHaar) :
    0 ≤ independentBoundaryFeatureExponentialQuadratic
      boundaryHaar positiveHaar terms weight feature β f :=
  independent_boundary_feature_exponential_rp
    boundaryHaar positiveHaar terms weight feature hweight hMeas hBound
    β hβ f hfMeas hfInt

end RequestProject.YangMills
