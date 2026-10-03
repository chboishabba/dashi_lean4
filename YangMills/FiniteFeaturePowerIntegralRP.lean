import Mathlib
import YangMills.FiniteFeatureIntegralRP

/-!
# Integral positivity for Hadamard powers of finite feature kernels

The Wilson exponential Taylor series needs integral positivity of K^n, where
K is already a finite positive-feature kernel.  Rather than carrying abstract
Schur-product integrability hypotheses, this file expands K^n into the honest
finite feature family indexed by n-tuples of active features.

Every resulting coefficient is a product of nonnegative original weights, so
the exact integral sum-of-squares theorem applies immediately.
-/

namespace RequestProject.YangMills

/-- Active feature indices, with membership in the selected finite feature set built in. -/
abbrev ActiveFiniteFeature {I : Type*} (terms : Finset I) :=
  {i : I // i ∈ terms}

/-- Product weight attached to an n-tuple of active features. -/
def finiteFeaturePowerWeight
    {I : Type*} {terms : Finset I}
    (weight : I → ℝ) {n : ℕ}
    (choice : Fin n → ActiveFiniteFeature terms) : ℝ :=
  ∏ k, weight (choice k).1

/-- Product feature attached to an n-tuple of active features. -/
def finiteFeaturePowerFeature
    {X I : Type*} {terms : Finset I}
    (feature : I → X → ℝ) {n : ℕ}
    (choice : Fin n → ActiveFiniteFeature terms)
    (x : X) : ℝ :=
  ∏ k, feature (choice k).1 x

/-- The original finite feature sum can be written as a Fintype sum over its active subtype. -/
theorem finite_cross_plane_features_eq_active_sum
    {X I : Type*}
    (terms : Finset I)
    (weight : I → ℝ)
    (feature : I → X → ℝ)
    (x y : X) :
    finiteCrossPlaneFeatures terms weight feature x y =
      ∑ i : ActiveFiniteFeature terms,
        weight i.1 * feature i.1 x * feature i.1 y := by
  classical
  unfold finiteCrossPlaneFeatures
  rw [← Finset.sum_attach]
  simp

/-- Exact n-tuple positive-feature presentation of the Hadamard power K^n. -/
theorem finite_cross_plane_feature_pow_eq_power_features
    {X I : Type*}
    (terms : Finset I)
    (weight : I → ℝ)
    (feature : I → X → ℝ)
    (n : ℕ) (x y : X) :
    (finiteCrossPlaneFeatures terms weight feature x y) ^ n =
      finiteCrossPlaneFeatures
        (Finset.univ : Finset (Fin n → ActiveFiniteFeature terms))
        (finiteFeaturePowerWeight weight)
        (finiteFeaturePowerFeature feature)
        x y := by
  classical
  rw [finite_cross_plane_features_eq_active_sum terms weight feature x y]
  rw [← Fin.prod_const]
  rw [Fintype.prod_sum]
  unfold finiteCrossPlaneFeatures finiteFeaturePowerWeight finiteFeaturePowerFeature
  simp only [Finset.mem_univ, true_and]
  apply Finset.sum_congr rfl
  intro choice hchoice
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_mul_distrib]
  ring

/-- Product weights remain nonnegative when the source feature weights are nonnegative. -/
theorem finite_feature_power_weight_nonnegative
    {I : Type*}
    (terms : Finset I)
    (weight : I → ℝ)
    (hweight : ∀ i ∈ terms, 0 ≤ weight i)
    (n : ℕ)
    (choice : Fin n → ActiveFiniteFeature terms) :
    0 ≤ finiteFeaturePowerWeight weight choice := by
  unfold finiteFeaturePowerWeight
  exact Finset.prod_nonneg fun k hk => hweight (choice k).1 (choice k).2

/--
Every Hadamard power of a positive finite feature kernel remains OS-positive
after integration.  The only analytic premise is integrability of the finitely
many power-feature-weighted test functions actually used by this power.
-/
theorem finite_cross_plane_feature_pow_integral_rp
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
      f x * (finiteCrossPlaneFeatures terms weight feature x y) ^ n * f y ∂μ ∂μ := by
  rw [show
    (fun x y =>
      (finiteCrossPlaneFeatures terms weight feature x y) ^ n) =
      finiteCrossPlaneFeatures
        (Finset.univ : Finset (Fin n → ActiveFiniteFeature terms))
        (finiteFeaturePowerWeight weight)
        (finiteFeaturePowerFeature feature) by
      funext x y
      exact finite_cross_plane_feature_pow_eq_power_features
        terms weight feature n x y]
  exact finite_cross_plane_feature_integral_rp
    μ
    (Finset.univ : Finset (Fin n → ActiveFiniteFeature terms))
    (finiteFeaturePowerWeight weight)
    (finiteFeaturePowerFeature feature)
    f
    (by
      intro choice hchoice
      exact finite_feature_power_weight_nonnegative
        terms weight hweight n choice)
    (by
      intro choice hchoice
      exact hInt choice)

end RequestProject.YangMills
