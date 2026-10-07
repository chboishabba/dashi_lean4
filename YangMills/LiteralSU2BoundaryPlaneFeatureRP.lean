import Mathlib
import YangMills.LiteralSU2BoundaryPlaneDoubleGauge
import YangMills.LiteralSU2CrossingIntegralRP
import YangMills.IndependentBoundaryFeatureExponentialRP

/-!
# Augmented positive-feature presentation of both literal crossing slabs

The upper and lower crossing slabs are already written as relative traces of
independently boundary-gauged positive spatial edges.  Since the normalized
SU(2) relative trace is the Euclidean dot product of the four quaternion
coordinates, the sum of both slabs is one finite positive-feature kernel on the
augmented half-space carrier

  (upper boundary, lower boundary) × positive-interior links.

This is the analytic RP producer for the crossing-only middle kernel.
-/

namespace RequestProject.YangMills

abbrev SU2BoundaryPlaneCrossingFeatureIndex
    (n : ℕ) [NeZero n] :=
  Sum
    (((su2UpperCrossingPlaquettes n).attach) × Fin 4)
    (((su2LowerCrossingPlaquettes n).attach) × Fin 4)

/-- One quaternion coordinate of one upper/lower gauged crossing edge. -/
def su2BoundaryPlaneCrossingFeature
    (n : ℕ) [NeZero n]
    (i : SU2BoundaryPlaneCrossingFeatureIndex n)
    (planes : SU2BoundaryPlaneFields n)
    (field : SU2PositiveInteriorLinks n) : ℝ :=
  match i with
  | Sum.inl pi =>
      su2QuaternionCoordinate pi.2
        (su2UpperPlaneGaugedPositiveEdge n planes.1 field pi.1)
  | Sum.inr pi =>
      su2QuaternionCoordinate pi.2
        (su2LowerPlaneGaugedPositiveEdge n planes.2 field pi.1)

/-- Every augmented crossing feature is measurable on boundary-plane × field space. -/
theorem su2_boundary_plane_crossing_feature_measurable
    (n : ℕ) [NeZero n]
    (i : SU2BoundaryPlaneCrossingFeatureIndex n) :
    Measurable
      (Function.uncurry (su2BoundaryPlaneCrossingFeature n i)) := by
  rcases i with pi | pi
  · exact (su2_quaternion_coordinate_measurable pi.2).comp (by
      unfold Function.uncurry su2BoundaryPlaneCrossingFeature
        su2UpperPlaneGaugedPositiveEdge su2BoundaryGaugeTransformEdge
      fun_prop)
  · exact (su2_quaternion_coordinate_measurable pi.2).comp (by
      unfold Function.uncurry su2BoundaryPlaneCrossingFeature
        su2LowerPlaneGaugedPositiveEdge su2BoundaryGaugeTransformEdge
      fun_prop)

/-- Every augmented crossing feature remains unit bounded. -/
theorem su2_boundary_plane_crossing_feature_abs_le_one
    (n : ℕ) [NeZero n]
    (i : SU2BoundaryPlaneCrossingFeatureIndex n)
    (planes : SU2BoundaryPlaneFields n)
    (field : SU2PositiveInteriorLinks n) :
    |su2BoundaryPlaneCrossingFeature n i planes field| ≤ 1 := by
  rcases i with pi | pi
  · exact su2_quaternion_coordinate_abs_le_one pi.2 _
  · exact su2_quaternion_coordinate_abs_le_one pi.2 _

/--
The complete upper+lower independently gauged crossing trace is exactly one
finite positive-feature Gram kernel on the augmented carrier.
-/
theorem su2_boundary_plane_double_gauged_trace_eq_features
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryPlaneFields n) :
    su2UpperPlaneDoubleGaugedCrossingTraceSum n left right b.1 c.1 +
      su2LowerPlaneDoubleGaugedCrossingTraceSum n left right b.2 c.2 =
    finiteCrossPlaneFeatures
      (Finset.univ : Finset (SU2BoundaryPlaneCrossingFeatureIndex n))
      (fun _ => (1 : ℝ))
      (independentBoundaryFeature (su2BoundaryPlaneCrossingFeature n))
      (b, left) (c, right) := by
  classical
  unfold su2UpperPlaneDoubleGaugedCrossingTraceSum
    su2LowerPlaneDoubleGaugedCrossingTraceSum
    finiteCrossPlaneFeatures independentBoundaryFeature
  simp [su2BoundaryPlaneCrossingFeature,
    su2_relative_trace_eq_quaternion_dot]

/--
The augmented upper+lower crossing exponential has a nonnegative quadratic form
for every L1 test on the positive-interior Haar law.
-/
theorem su2_boundary_plane_augmented_crossing_exponential_rp
    (n : ℕ) [NeZero n]
    (β : ℝ) (hβ : 0 ≤ β)
    (f : SU2PositiveInteriorLinks n → ℝ)
    (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f (literalSU2PositiveInteriorHaar n)) :
    0 ≤ independentBoundaryFeatureExponentialQuadratic
      (literalSU2BoundaryPlaneHaar n)
      (literalSU2PositiveInteriorHaar n)
      (Finset.univ : Finset (SU2BoundaryPlaneCrossingFeatureIndex n))
      (fun _ => (1 : ℝ))
      (su2BoundaryPlaneCrossingFeature n)
      β f := by
  exact independent_boundary_feature_exponential_rp
    (literalSU2BoundaryPlaneHaar n)
    (literalSU2PositiveInteriorHaar n)
    (Finset.univ : Finset (SU2BoundaryPlaneCrossingFeatureIndex n))
    (fun _ => (1 : ℝ))
    (su2BoundaryPlaneCrossingFeature n)
    (by intro i hi; norm_num)
    (by intro i hi; exact su2_boundary_plane_crossing_feature_measurable n i)
    (by intro i hi planes field;
      exact su2_boundary_plane_crossing_feature_abs_le_one n i planes field)
    β hβ f hfMeas hfInt

end RequestProject.YangMills
