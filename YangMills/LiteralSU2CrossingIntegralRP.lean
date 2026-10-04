import Mathlib
import YangMills.LiteralSU2WilsonReflectionPlane
import YangMills.FiniteFeatureExponentialIntegralRP

/-!
# Continuous integral reflection positivity of the literal SU(2) crossing plane

The existing Wilson crossing theorem proves finite Gram positivity.  This file
uses the stronger explicit quaternion feature presentation to prove the actual
double-integral quadratic form is nonnegative for every L1 real test function.

The feature set is exactly (crossing plaquette, quaternion coordinate), every
weight is one, every coordinate is measurable and bounded in absolute value by
one, and the harmless Wilson scalar exp(-beta |C|) is positive.
-/

namespace RequestProject.YangMills

/-- Every literal unit-quaternion coordinate is measurable. -/
theorem su2_quaternion_coordinate_measurable
    (i : Fin 4) :
    Measurable (su2QuaternionCoordinate i) := by
  fin_cases i <;>
    simp [su2QuaternionCoordinate,
      su2_a_measurable, su2_b_measurable,
      su2_c_measurable, su2_d_measurable]

/-- Every literal unit-quaternion coordinate lies in [-1,1]. -/
theorem su2_quaternion_coordinate_abs_le_one
    (i : Fin 4) (U : SU2PlaquetteHolonomy) :
    |su2QuaternionCoordinate i U| ≤ 1 := by
  fin_cases i
  · simp only [su2QuaternionCoordinate, if_pos rfl]
    have h := U.unit_quaternion
    have ha : U.a ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg U.b, sq_nonneg U.c, sq_nonneg U.d]
    nlinarith [sq_abs U.a]
  · simp only [su2QuaternionCoordinate, Fin.mk.injEq, OfNat.ofNat,
      OfNat.ofNat, if_false, if_pos rfl]
    have h := U.unit_quaternion
    have hb : U.b ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg U.a, sq_nonneg U.c, sq_nonneg U.d]
    nlinarith [sq_abs U.b]
  · simp only [su2QuaternionCoordinate, Fin.mk.injEq, OfNat.ofNat,
      OfNat.ofNat, if_false, if_pos rfl]
    have h := U.unit_quaternion
    have hc : U.c ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg U.a, sq_nonneg U.b, sq_nonneg U.d]
    nlinarith [sq_abs U.c]
  · simp only [su2QuaternionCoordinate, Fin.mk.injEq, OfNat.ofNat,
      OfNat.ofNat, if_false]
    have h := U.unit_quaternion
    have hd : U.d ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg U.a, sq_nonneg U.b, sq_nonneg U.c]
    nlinarith [sq_abs U.d]

/-- Flatten the multi-plaquette trace kernel into one ordinary finite feature family. -/
theorem su2_crossing_trace_sum_eq_flat_features
    {P : Type*} [DecidableEq P]
    (crossings : Finset P) :
    su2CrossingTraceSum crossings =
      finiteCrossPlaneFeatures
        (crossings.product (Finset.univ : Finset (Fin 4)))
        (fun _ : P × Fin 4 => (1 : ℝ))
        (fun pi boundary =>
          su2QuaternionCoordinate pi.2 (boundary pi.1)) := by
  funext left right
  unfold su2CrossingTraceSum finiteCrossPlaneFeatures
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  rw [su2_relative_trace_eq_quaternion_dot]
  simp

/-- The flattened physical crossing features are measurable. -/
theorem su2_crossing_flat_feature_measurable
    {P : Type*} [DecidableEq P]
    (pi : P × Fin 4) :
    Measurable
      (fun boundary : SU2CrossingBoundary P =>
        su2QuaternionCoordinate pi.2 (boundary pi.1)) := by
  exact (su2_quaternion_coordinate_measurable pi.2).comp
    (measurable_pi_apply pi.1)

/-- The flattened physical crossing features are uniformly unit bounded. -/
theorem su2_crossing_flat_feature_abs_le_one
    {P : Type*}
    (pi : P × Fin 4)
    (boundary : SU2CrossingBoundary P) :
    |su2QuaternionCoordinate pi.2 (boundary pi.1)| ≤ 1 :=
  su2_quaternion_coordinate_abs_le_one pi.2 (boundary pi.1)

/--
Continuous integral RP for the complete finite Wilson crossing plane.
This is stronger than the finite-sample Gram theorem and is the exact analytic
kernel fact consumed by the final finite-Haar/Fubini OS2 assembly.
-/
theorem su2_wilson_crossing_plane_integral_rp
    {P : Type*} [DecidableEq P]
    (crossings : Finset P)
    (β : ℝ) (hβ : 0 ≤ β)
    (μ : MeasureTheory.Measure (SU2CrossingBoundary P))
    [MeasureTheory.SFinite μ]
    (f : SU2CrossingBoundary P → ℝ)
    (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f μ) :
    0 ≤ ∫ left, ∫ right,
      f left * su2WilsonCrossingPlaneKernel crossings β left right * f right ∂μ ∂μ := by
  let terms : Finset (P × Fin 4) :=
    crossings.product (Finset.univ : Finset (Fin 4))
  let feature : P × Fin 4 → SU2CrossingBoundary P → ℝ :=
    fun pi boundary => su2QuaternionCoordinate pi.2 (boundary pi.1)
  have hExp :
      0 ≤ ∫ left, ∫ right,
        f left *
          Real.exp
            (β * finiteCrossPlaneFeatures terms
              (fun _ => (1 : ℝ)) feature left right) *
          f right ∂μ ∂μ := by
    exact finite_cross_plane_feature_exponential_integral_rp
      μ terms (fun _ => (1 : ℝ)) feature
      (by intro i hi; norm_num)
      (by
        intro pi hpi
        exact su2_crossing_flat_feature_measurable pi)
      (by
        intro pi hpi boundary
        exact su2_crossing_flat_feature_abs_le_one pi boundary)
      β hβ f hfMeas hfInt
  have hKernel :
      (fun left right =>
        Real.exp
          (β * finiteCrossPlaneFeatures terms
            (fun _ => (1 : ℝ)) feature left right)) =
      (fun left right =>
        Real.exp (β * su2CrossingTraceSum crossings left right)) := by
    funext left right
    rw [su2_crossing_trace_sum_eq_flat_features crossings]
    rfl
  rw [hKernel] at hExp
  unfold su2WilsonCrossingPlaneKernel
  have hscalar : 0 ≤ Real.exp (-(β * (crossings.card : ℝ))) :=
    (Real.exp_pos _).le
  calc
    0 ≤ Real.exp (-(β * (crossings.card : ℝ))) *
        (∫ left, ∫ right,
          f left * Real.exp (β * su2CrossingTraceSum crossings left right) * f right ∂μ ∂μ) :=
      mul_nonneg hscalar hExp
    _ = ∫ left, ∫ right,
        f left *
          (Real.exp (-(β * (crossings.card : ℝ))) *
            Real.exp (β * su2CrossingTraceSum crossings left right)) *
          f right ∂μ ∂μ := by
      simp_rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with left
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with right
      ring

end RequestProject.YangMills
