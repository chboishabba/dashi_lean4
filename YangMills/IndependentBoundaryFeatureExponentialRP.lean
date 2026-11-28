import Mathlib
import YangMills.FiniteFeatureExponentialIntegralRP

/-!
# Independent boundary averaging preserves finite-feature exponential RP

The last analytic part of the finite Wilson boundary-projection route is most
naturally stated on the product carrier `B × X`: a boundary Haar variable and
a positive-interior configuration are treated as one augmented half-space
variable.  If every crossing feature after the boundary gauge action remains a
measurable unit-bounded real feature, the existing exponential finite-feature
RP theorem applies verbatim to this augmented carrier.

This is exactly the positivity behind independent boundary averaging.  A later
same-object/Fubini weld only has to identify the literal projected Wilson
quadratic form with this augmented product-space quadratic form.
-/

namespace RequestProject.YangMills

/-- Crossing feature after adjoining an independent boundary variable. -/
def independentBoundaryFeature
    {B X I : Type*}
    (feature : I → B → X → ℝ)
    (i : I) : B × X → ℝ :=
  fun z => feature i z.1 z.2

/-- Lift a positive-half test function to the augmented boundary/configuration carrier. -/
def independentBoundaryTest
    {B X : Type*}
    (f : X → ℝ) : B × X → ℝ :=
  fun z => f z.2

/--
The augmented quadratic form.  Integrating out the two boundary coordinates by
Fubini yields the ordinary quadratic form of the independently boundary-averaged
kernel.
-/
def independentBoundaryFeatureExponentialQuadratic
    {B X I : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (boundaryHaar : MeasureTheory.Measure B)
    (positiveHaar : MeasureTheory.Measure X)
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → B → X → ℝ)
    (β : ℝ) (f : X → ℝ) : ℝ :=
  ∫ z : B × X, ∫ w : B × X,
    independentBoundaryTest f z *
      Real.exp
        (β * finiteCrossPlaneFeatures terms weight
          (independentBoundaryFeature feature) z w) *
      independentBoundaryTest f w
    ∂(boundaryHaar.prod positiveHaar)
  ∂(boundaryHaar.prod positiveHaar)

/-- A positive-half L1 test remains L1 after adjoining a finite boundary law. -/
theorem independent_boundary_test_integrable
    {B X : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (boundaryHaar : MeasureTheory.Measure B)
    [MeasureTheory.IsFiniteMeasure boundaryHaar]
    (positiveHaar : MeasureTheory.Measure X)
    (f : X → ℝ)
    (hfInt : MeasureTheory.Integrable f positiveHaar) :
    MeasureTheory.Integrable (independentBoundaryTest (B := B) f)
      (boundaryHaar.prod positiveHaar) := by
  have hOne : MeasureTheory.Integrable (fun _ : B => (1 : ℝ)) boundaryHaar := by
    exact MeasureTheory.integrable_const _
  have hProd := hOne.mul_prod hfInt
  simpa [independentBoundaryTest] using hProd

/--
Independent boundary variables preserve positivity of a finite-feature
exponential crossing kernel.  This is the analytic Haar-averaging half of the
surviving Block-A producer.
-/
theorem independent_boundary_feature_exponential_rp
    {B X I : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (boundaryHaar : MeasureTheory.Measure B)
    [MeasureTheory.IsFiniteMeasure boundaryHaar]
    (positiveHaar : MeasureTheory.Measure X)
    [MeasureTheory.SFinite positiveHaar]
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → B → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hMeas : ∀ i ∈ terms, Measurable (Function.uncurry (feature i)))
    (hBound : ∀ i ∈ terms, ∀ b x, |feature i b x| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β)
    (f : X → ℝ) (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f positiveHaar) :
    0 ≤ independentBoundaryFeatureExponentialQuadratic
      boundaryHaar positiveHaar terms weight feature β f := by
  have hFeatureMeas :
      ∀ i ∈ terms,
        Measurable (independentBoundaryFeature feature i) := by
    intro i hi
    simpa [independentBoundaryFeature, Function.uncurry] using hMeas i hi
  have hFeatureBound :
      ∀ i ∈ terms, ∀ z : B × X,
        |independentBoundaryFeature feature i z| ≤ 1 := by
    intro i hi z
    exact hBound i hi z.1 z.2
  have hTestMeas :
      Measurable (independentBoundaryTest (B := B) f) := by
    exact hfMeas.comp measurable_snd
  have hTestInt :
      MeasureTheory.Integrable (independentBoundaryTest (B := B) f)
        (boundaryHaar.prod positiveHaar) :=
    independent_boundary_test_integrable
      boundaryHaar positiveHaar f hfInt
  unfold independentBoundaryFeatureExponentialQuadratic
  exact finite_cross_plane_feature_exponential_integral_rp
    (boundaryHaar.prod positiveHaar)
    terms weight (independentBoundaryFeature feature)
    hweight hFeatureMeas hFeatureBound β hβ
    (independentBoundaryTest (B := B) f) hTestMeas hTestInt

end RequestProject.YangMills
