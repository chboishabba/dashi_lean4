import Mathlib
import YangMills.FiniteCrossPlaneFeatureRP

/-!
# Integral reflection positivity for finite positive-feature kernels

The finite-Gram theorem is algebraic.  The finite-lattice OS theorem also
needs its continuous-product-measure analogue.  For an honest finite feature
kernel this requires no approximation argument:

  K(x,y) = sum_i w_i phi_i(x) phi_i(y)

implies exactly

  int int f(x) K(x,y) f(y) dmu(y) dmu(x)
    = sum_i w_i (int f phi_i dmu)^2.

This is the measure-theoretic bridge used by the Wilson Taylor truncations.
Only the individual feature-weighted test functions need to be integrable.
-/

namespace RequestProject.YangMills

/-- Exact finite-feature double-integral square identity. -/
theorem finite_cross_plane_feature_integral_eq_sum_sq
    {X I : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    (terms : Finset I)
    (weight : I → ℝ)
    (feature : I → X → ℝ)
    (f : X → ℝ)
    (hInt : ∀ i ∈ terms,
      MeasureTheory.Integrable (fun x => f x * feature i x) μ) :
    (∫ x, ∫ y,
      f x * finiteCrossPlaneFeatures terms weight feature x y * f y ∂μ ∂μ)
      =
    ∑ i ∈ terms,
      weight i * (∫ x, f x * feature i x ∂μ) ^ 2 := by
  classical
  have hInner (x : X) :
      (∫ y,
        f x * finiteCrossPlaneFeatures terms weight feature x y * f y ∂μ)
      =
      ∑ i ∈ terms,
        (weight i * (f x * feature i x)) *
          (∫ y, f y * feature i y ∂μ) := by
    calc
      (∫ y,
        f x * finiteCrossPlaneFeatures terms weight feature x y * f y ∂μ)
        = ∫ y, ∑ i ∈ terms,
            (weight i * (f x * feature i x)) *
              (f y * feature i y) ∂μ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with y
              simp only [finiteCrossPlaneFeatures]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = ∑ i ∈ terms,
            ∫ y,
              (weight i * (f x * feature i x)) *
                (f y * feature i y) ∂μ := by
              rw [MeasureTheory.integral_finsetSum]
              intro i hi
              exact (hInt i hi).const_mul _
      _ = ∑ i ∈ terms,
            (weight i * (f x * feature i x)) *
              (∫ y, f y * feature i y ∂μ) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [MeasureTheory.integral_const_mul]
  rw [show
      (fun x => ∫ y,
        f x * finiteCrossPlaneFeatures terms weight feature x y * f y ∂μ)
      =
      (fun x => ∑ i ∈ terms,
        (weight i * (f x * feature i x)) *
          (∫ y, f y * feature i y ∂μ)) by
        funext x
        exact hInner x]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    have hgi := hInt i hi
    let Ii : ℝ := ∫ y, f y * feature i y ∂μ
    calc
      (∫ x,
        (weight i * (f x * feature i x)) * Ii ∂μ)
        = ∫ x, (weight i * Ii) * (f x * feature i x) ∂μ := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with x
            ring
      _ = (weight i * Ii) *
            (∫ x, f x * feature i x ∂μ) := by
            rw [MeasureTheory.integral_const_mul]
      _ = weight i *
            (∫ x, f x * feature i x ∂μ) ^ 2 := by
            dsimp [Ii]
            ring
  · intro i hi
    have hgi := hInt i hi
    let Ii : ℝ := ∫ y, f y * feature i y ∂μ
    have : MeasureTheory.Integrable
        (fun x => (weight i * Ii) * (f x * feature i x)) μ :=
      hgi.const_mul _
    exact this.congr (Filter.Eventually.of_forall (fun x => by ring))

/-- Every nonnegative finite feature kernel is OS-positive after integration. -/
theorem finite_cross_plane_feature_integral_rp
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
      f x * finiteCrossPlaneFeatures terms weight feature x y * f y ∂μ ∂μ := by
  rw [finite_cross_plane_feature_integral_eq_sum_sq
    μ terms weight feature f hInt]
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hweight i hi) (sq_nonneg _)

end RequestProject.YangMills
