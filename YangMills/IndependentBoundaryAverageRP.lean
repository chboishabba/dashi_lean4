import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
import YangMills.IndependentBoundaryFeatureExponentialRP

/-!
# Fubini compiler for independently boundary-averaged RP kernels

The augmented reflection-positive carrier is `B × X`, while the physical
kernel is normally written on `X` after integrating two independent copies of
`B`.  This file pays that change of integration order once.

No Yang--Mills-specific input appears here.  The only analytic hypotheses are
those already used by the finite-feature exponential RP theorem: finite
boundary measure, an L1 test on `X`, measurable unit-bounded features and
nonnegative feature weights.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- Reorder two augmented variables from `((b,x),(c,y))` to `((x,y),(b,c))`. -/
def independentBoundaryPairReorder
    {B X : Type*} [MeasurableSpace B] [MeasurableSpace X] :
    ((B × X) × (B × X)) ≃ᵐ ((X × X) × (B × B)) where
  toFun z := ((z.1.2, z.2.2), (z.1.1, z.2.1))
  invFun z := ((z.2.1, z.1.1), (z.2.2, z.1.2))
  left_inv := by
    rintro ⟨⟨b, x⟩, ⟨c, y⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨x, y⟩, ⟨b, c⟩⟩
    rfl
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

@[simp] theorem independent_boundary_pair_reorder_apply
    {B X : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (b c : B) (x y : X) :
    independentBoundaryPairReorder ((b, x), (c, y)) = ((x, y), (b, c)) := rfl

/-- The four-coordinate reorder preserves the corresponding product law. -/
theorem independent_boundary_pair_reorder_measurePreserving
    {B X : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (boundary : Measure B) (positive : Measure X)
    [SFinite boundary] [SFinite positive] :
    MeasurePreserving
      (independentBoundaryPairReorder (B := B) (X := X))
      ((boundary.prod positive).prod (boundary.prod positive))
      ((positive.prod positive).prod (boundary.prod boundary)) := by
  have h0 :
      MeasurePreserving (Prod.map Prod.swap Prod.swap)
        ((boundary.prod positive).prod (boundary.prod positive))
        ((positive.prod boundary).prod (positive.prod boundary)) :=
    MeasurePreserving.prod
      (MeasureTheory.measurePreserving_swap (μ := boundary) (ν := positive))
      (MeasureTheory.measurePreserving_swap (μ := boundary) (ν := positive))
  have h1 :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          ((X × B) × (X × B)) ≃ᵐ (X × (B × (X × B))))
        ((positive.prod boundary).prod (positive.prod boundary))
        (positive.prod (boundary.prod (positive.prod boundary))) :=
    MeasureTheory.measurePreserving_prodAssoc
      positive boundary (positive.prod boundary)
  have h2inner :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          (B × (X × B)) ≃ᵐ ((B × X) × B))
        (boundary.prod (positive.prod boundary))
        ((boundary.prod positive).prod boundary) :=
    (MeasureTheory.measurePreserving_prodAssoc boundary positive boundary).symm
      MeasurableEquiv.prodAssoc
  have h2 :
      MeasurePreserving
        (Prod.map id
          (MeasurableEquiv.prodAssoc.symm :
            (B × (X × B)) ≃ᵐ ((B × X) × B)))
        (positive.prod (boundary.prod (positive.prod boundary)))
        (positive.prod ((boundary.prod positive).prod boundary)) :=
    MeasurePreserving.prod (MeasurePreserving.id positive) h2inner
  have h3inner :
      MeasurePreserving (Prod.map Prod.swap id)
        ((boundary.prod positive).prod boundary)
        ((positive.prod boundary).prod boundary) :=
    MeasurePreserving.prod
      (MeasureTheory.measurePreserving_swap (μ := boundary) (ν := positive))
      (MeasurePreserving.id boundary)
  have h3 :
      MeasurePreserving (Prod.map id (Prod.map Prod.swap id))
        (positive.prod ((boundary.prod positive).prod boundary))
        (positive.prod ((positive.prod boundary).prod boundary)) :=
    MeasurePreserving.prod (MeasurePreserving.id positive) h3inner
  have h4inner :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc :
          ((X × B) × B) ≃ᵐ (X × (B × B)))
        ((positive.prod boundary).prod boundary)
        (positive.prod (boundary.prod boundary)) :=
    MeasureTheory.measurePreserving_prodAssoc positive boundary boundary
  have h4 :
      MeasurePreserving
        (Prod.map id
          (MeasurableEquiv.prodAssoc :
            ((X × B) × B) ≃ᵐ (X × (B × B))))
        (positive.prod ((positive.prod boundary).prod boundary))
        (positive.prod (positive.prod (boundary.prod boundary))) :=
    MeasurePreserving.prod (MeasurePreserving.id positive) h4inner
  have h5 :
      MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          (X × (X × (B × B))) ≃ᵐ ((X × X) × (B × B)))
        (positive.prod (positive.prod (boundary.prod boundary)))
        ((positive.prod positive).prod (boundary.prod boundary)) :=
    (MeasureTheory.measurePreserving_prodAssoc
      positive positive (boundary.prod boundary)).symm
        MeasurableEquiv.prodAssoc
  have h := h5.comp (h4.comp (h3.comp (h2.comp (h1.comp h0))))
  simpa [independentBoundaryPairReorder, Function.comp_def] using h

/-- Boundary-average of a finite-feature exponential kernel. -/
noncomputable def independentBoundaryAveragedFeatureExponentialKernel
    {B X I : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (boundary : Measure B)
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → B → X → ℝ)
    (β : ℝ) (x y : X) : ℝ :=
  ∫ b : B, ∫ c : B,
    Real.exp
      (β * finiteCrossPlaneFeatures terms weight
        (independentBoundaryFeature feature) (b, x) (c, y))
    ∂boundary ∂boundary

/-- The full augmented pair integrand is integrable under the standard feature hypotheses. -/
theorem independent_boundary_feature_exponential_pair_integrable
    {B X I : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (boundary : Measure B) [IsFiniteMeasure boundary]
    (positive : Measure X) [SFinite positive]
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → B → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hMeas : ∀ i ∈ terms, Measurable (Function.uncurry (feature i)))
    (hBound : ∀ i ∈ terms, ∀ b x, |feature i b x| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β)
    (f : X → ℝ)
    (hfInt : Integrable f positive) :
    Integrable
      (fun zw : (B × X) × (B × X) =>
        independentBoundaryTest f zw.1 *
          Real.exp
            (β * finiteCrossPlaneFeatures terms weight
              (independentBoundaryFeature feature) zw.1 zw.2) *
          independentBoundaryTest f zw.2)
      ((boundary.prod positive).prod (boundary.prod positive)) := by
  classical
  have hFeatureMeas :
      ∀ i ∈ terms, Measurable (independentBoundaryFeature feature i) := by
    intro i hi
    simpa [independentBoundaryFeature, Function.uncurry] using hMeas i hi
  have hFeatureBound :
      ∀ i ∈ terms, ∀ z : B × X,
        |independentBoundaryFeature feature i z| ≤ 1 := by
    intro i hi z
    exact hBound i hi z.1 z.2
  have hTestInt :
      Integrable (independentBoundaryTest (B := B) f)
        (boundary.prod positive) :=
    independent_boundary_test_integrable boundary positive f hfInt
  have hBase :
      Integrable
        (fun zw : (B × X) × (B × X) =>
          independentBoundaryTest f zw.1 * independentBoundaryTest f zw.2)
        ((boundary.prod positive).prod (boundary.prod positive)) :=
    hTestInt.mul_prod hTestInt
  let budget := finiteFeatureWeightBudget terms weight
  have hKernelMeas :
      Measurable
        (fun zw : (B × X) × (B × X) =>
          Real.exp
            (β * finiteCrossPlaneFeatures terms weight
              (independentBoundaryFeature feature) zw.1 zw.2)) := by
    unfold finiteCrossPlaneFeatures
    fun_prop (disch := aesop)
  have hKernelBound :
      ∀ zw : (B × X) × (B × X),
        ‖Real.exp
            (β * finiteCrossPlaneFeatures terms weight
              (independentBoundaryFeature feature) zw.1 zw.2)‖ ≤
          Real.exp (β * budget) := by
    intro zw
    rw [Real.norm_eq_abs, abs_exp]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hβ
    exact (le_abs_self _).trans
      (finite_cross_plane_features_abs_le_budget
        terms weight (independentBoundaryFeature feature)
        hweight hFeatureBound zw.1 zw.2)
  have h := hBase.bdd_mul hKernelMeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hKernelBound)
  simpa [independentBoundaryTest, mul_assoc, mul_comm, mul_left_comm] using h

/--
Fubini compiler: positivity on the augmented carrier is exactly positivity of
the independently boundary-averaged kernel on the original positive carrier.
-/
theorem independent_boundary_feature_exponential_average_rp
    {B X I : Type*} [MeasurableSpace B] [MeasurableSpace X]
    (boundary : Measure B) [IsFiniteMeasure boundary]
    (positive : Measure X) [SFinite positive]
    (terms : Finset I) (weight : I → ℝ)
    (feature : I → B → X → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (hMeas : ∀ i ∈ terms, Measurable (Function.uncurry (feature i)))
    (hBound : ∀ i ∈ terms, ∀ b x, |feature i b x| ≤ 1)
    (β : ℝ) (hβ : 0 ≤ β)
    (f : X → ℝ) (hfMeas : Measurable f)
    (hfInt : Integrable f positive) :
    0 ≤ ∫ x : X, ∫ y : X,
      f x *
        independentBoundaryAveragedFeatureExponentialKernel
          boundary terms weight feature β x y *
        f y
      ∂positive ∂positive := by
  classical
  let G : ((B × X) × (B × X)) → ℝ := fun zw =>
    independentBoundaryTest f zw.1 *
      Real.exp
        (β * finiteCrossPlaneFeatures terms weight
          (independentBoundaryFeature feature) zw.1 zw.2) *
      independentBoundaryTest f zw.2
  let H : ((X × X) × (B × B)) → ℝ := fun q =>
    f q.1.1 *
      Real.exp
        (β * finiteCrossPlaneFeatures terms weight
          (independentBoundaryFeature feature)
          (q.2.1, q.1.1) (q.2.2, q.1.2)) *
      f q.1.2
  have hGInt : Integrable G
      ((boundary.prod positive).prod (boundary.prod positive)) := by
    simpa [G] using
      independent_boundary_feature_exponential_pair_integrable
        boundary positive terms weight feature hweight hMeas hBound
        β hβ f hfInt
  have hReorder := independent_boundary_pair_reorder_measurePreserving
    boundary positive
  have hHInt : Integrable H
      ((positive.prod positive).prod (boundary.prod boundary)) := by
    have hiff := hReorder.integrable_comp_emb
      (independentBoundaryPairReorder (B := B) (X := X)).measurableEmbedding
      (g := H)
    apply hiff.mp
    simpa [G, H, Function.comp_def, independentBoundaryTest] using hGInt
  have hAug :
      0 ≤ ∫ zw, G zw
        ∂((boundary.prod positive).prod (boundary.prod positive)) := by
    have hRP := independent_boundary_feature_exponential_rp
      boundary positive terms weight feature hweight hMeas hBound
      β hβ f hfMeas hfInt
    rw [show
      independentBoundaryFeatureExponentialQuadratic
          boundary positive terms weight feature β f =
        ∫ zw, G zw
          ∂((boundary.prod positive).prod (boundary.prod positive)) by
      unfold independentBoundaryFeatureExponentialQuadratic
      rw [← integral_prod G hGInt]
      rfl] at hRP
    exact hRP
  have hMap :
      (∫ zw, G zw
        ∂((boundary.prod positive).prod (boundary.prod positive))) =
      ∫ q, H q
        ∂((positive.prod positive).prod (boundary.prod boundary)) := by
    have h := hReorder.integral_comp'
      (f := independentBoundaryPairReorder (B := B) (X := X)) H
    simpa [G, H, Function.comp_def, independentBoundaryTest] using h
  have hJInt : Integrable
      (fun xy : X × X =>
        ∫ bc : B × B, H (xy, bc) ∂(boundary.prod boundary))
      (positive.prod positive) :=
    hHInt.integral_prod_left
  have hSection :
      ∀ᵐ xy ∂(positive.prod positive),
        Integrable (fun bc : B × B => H (xy, bc))
          (boundary.prod boundary) :=
    hHInt.prod_right_ae
  have hAverageAE :
      ∀ᵐ xy ∂(positive.prod positive),
        (∫ bc : B × B, H (xy, bc) ∂(boundary.prod boundary)) =
          f xy.1 *
            independentBoundaryAveragedFeatureExponentialKernel
              boundary terms weight feature β xy.1 xy.2 *
            f xy.2 := by
    filter_upwards [hSection] with xy hxy
    rw [integral_prod _ hxy]
    unfold H independentBoundaryAveragedFeatureExponentialKernel
    simp only
    simp_rw [← integral_const_mul, ← integral_mul_const]
    ring
  have hAverageInt : Integrable
      (fun xy : X × X =>
        f xy.1 *
          independentBoundaryAveragedFeatureExponentialKernel
            boundary terms weight feature β xy.1 xy.2 *
          f xy.2)
      (positive.prod positive) :=
    hJInt.congr hAverageAE
  have hTargetEq :
      (∫ q, H q
        ∂((positive.prod positive).prod (boundary.prod boundary))) =
      ∫ x : X, ∫ y : X,
        f x *
          independentBoundaryAveragedFeatureExponentialKernel
            boundary terms weight feature β x y *
          f y
        ∂positive ∂positive := by
    calc
      (∫ q, H q
        ∂((positive.prod positive).prod (boundary.prod boundary))) =
          ∫ xy : X × X,
            ∫ bc : B × B, H (xy, bc) ∂(boundary.prod boundary)
            ∂(positive.prod positive) :=
        integral_prod H hHInt
      _ = ∫ xy : X × X,
          f xy.1 *
            independentBoundaryAveragedFeatureExponentialKernel
              boundary terms weight feature β xy.1 xy.2 *
            f xy.2
          ∂(positive.prod positive) :=
        integral_congr_ae hAverageAE
      _ = ∫ x : X, ∫ y : X,
          f x *
            independentBoundaryAveragedFeatureExponentialKernel
              boundary terms weight feature β x y *
            f y
          ∂positive ∂positive :=
        integral_prod _ hAverageInt
  rw [hMap, hTargetEq] at hAug
  exact hAug

end RequestProject.YangMills
