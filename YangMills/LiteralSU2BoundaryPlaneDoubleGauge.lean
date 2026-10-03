import Mathlib
import YangMills.LiteralSU2BoundaryGaugeProjectionAlgebra
import YangMills.LiteralSU2CrossingGaugePlaneLocality
import YangMills.LiteralSU2CrossingPositiveIndexCoincidence

/-!
# Double-gauge crossing sums reduce to the physical single relative gauge

The augmented feature-kernel proof uses independent boundary gauges on the two
positive half-space variables.  On each crossing slab their relative trace
reduces exactly to the physical single-gauge trace.  The upper slab produces
`b * c⁻¹`; the lower slab produces `c * b⁻¹`, matching its opposite orientation.
-/

namespace RequestProject.YangMills

/-- Upper crossing spatial edge after its upper-plane endpoint gauge action. -/
def su2UpperPlaneGaugedPositiveEdge
    (n : ℕ) [NeZero n]
    (upper : SU2UpperBoundaryTemporalLinks n)
    (field : SU2PositiveInteriorLinks n)
    (p : (su2UpperCrossingPlaquettes n).attach) :
    SU2PlaquetteHolonomy :=
  su2BoundaryGaugeTransformEdge
    (upper (su2UpperCrossingSourceUpperBoundaryIndex n p.1 p.2))
    (upper (su2UpperCrossingTargetUpperBoundaryIndex n p.1 p.2))
    (field (su2UpperCrossingLeftPositiveIndex n p.1 p.2))

/-- Lower crossing spatial edge after its lower-plane endpoint gauge action. -/
def su2LowerPlaneGaugedPositiveEdge
    (n : ℕ) [NeZero n]
    (lower : SU2LowerBoundaryTemporalLinks n)
    (field : SU2PositiveInteriorLinks n)
    (p : (su2LowerCrossingPlaquettes n).attach) :
    SU2PlaquetteHolonomy :=
  su2BoundaryGaugeTransformEdge
    (lower (su2LowerCrossingSourceLowerBoundaryIndex n p.1 p.2))
    (lower (su2LowerCrossingTargetLowerBoundaryIndex n p.1 p.2))
    (field (su2LowerCrossingLeftPositiveIndex n p.1 p.2))

/-- Upper trace sum with independent gauges on both positive copies. -/
def su2UpperPlaneDoubleGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2UpperBoundaryTemporalLinks n) : ℝ :=
  ∑ p : (su2UpperCrossingPlaquettes n).attach,
    su2RelativeFundamentalTrace
      (su2UpperPlaneGaugedPositiveEdge n b left p)
      (su2UpperPlaneGaugedPositiveEdge n c right p)

/-- Lower trace sum with independent gauges on both positive copies. -/
def su2LowerPlaneDoubleGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2LowerBoundaryTemporalLinks n) : ℝ :=
  ∑ p : (su2LowerCrossingPlaquettes n).attach,
    su2RelativeFundamentalTrace
      (su2LowerPlaneGaugedPositiveEdge n b left p)
      (su2LowerPlaneGaugedPositiveEdge n c right p)

/-- Upper double gauge reduces to the physical upper sum at relative gauge `b*c⁻¹`. -/
theorem su2_upper_plane_double_gauge_reduce
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2UpperBoundaryTemporalLinks n) :
    su2UpperPlaneDoubleGaugedCrossingTraceSum n left right b c =
      su2UpperPlaneGaugedCrossingTraceSum n left right
        (su2BoundaryRelativeGauge b c) := by
  classical
  unfold su2UpperPlaneDoubleGaugedCrossingTraceSum
    su2UpperPlaneGaugedCrossingTraceSum
    su2UpperPlaneGaugedPositiveEdge
  rw [show
    (∑ p : (su2UpperCrossingPlaquettes n).attach,
      su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge
          (b (su2UpperCrossingSourceUpperBoundaryIndex n p.1 p.2))
          (b (su2UpperCrossingTargetUpperBoundaryIndex n p.1 p.2))
          (left (su2UpperCrossingLeftPositiveIndex n p.1 p.2)))
        (su2BoundaryGaugeTransformEdge
          (c (su2UpperCrossingSourceUpperBoundaryIndex n p.1 p.2))
          (c (su2UpperCrossingTargetUpperBoundaryIndex n p.1 p.2))
          (right (su2UpperCrossingLeftPositiveIndex n p.1 p.2)))) =
      ∑ p ∈ (su2UpperCrossingPlaquettes n).attach,
        su2RelativeFundamentalTrace
          (right (su2UpperCrossingRightPositiveIndex n p.1 p.2))
          (su2BoundaryGaugeTransformEdge
            ((su2BoundaryRelativeGauge b c)
              (su2UpperCrossingSourceUpperBoundaryIndex n p.1 p.2))
            ((su2BoundaryRelativeGauge b c)
              (su2UpperCrossingTargetUpperBoundaryIndex n p.1 p.2))
            (left (su2UpperCrossingLeftPositiveIndex n p.1 p.2))) by
    rw [Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← su2_upper_crossing_positive_index_coincides n p hp]
    rw [su2RelativeFundamentalTrace_comm]
    exact su2_relative_trace_two_boundary_gauges_reduce
      (b (su2UpperCrossingSourceUpperBoundaryIndex n p hp))
      (b (su2UpperCrossingTargetUpperBoundaryIndex n p hp))
      (c (su2UpperCrossingSourceUpperBoundaryIndex n p hp))
      (c (su2UpperCrossingTargetUpperBoundaryIndex n p hp))
      (left (su2UpperCrossingLeftPositiveIndex n p hp))
      (right (su2UpperCrossingRightPositiveIndex n p hp))]
  rfl

/-- Lower double gauge reduces to the physical lower sum at relative gauge `c*b⁻¹`. -/
theorem su2_lower_plane_double_gauge_reduce
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2LowerBoundaryTemporalLinks n) :
    su2LowerPlaneDoubleGaugedCrossingTraceSum n left right b c =
      su2LowerPlaneGaugedCrossingTraceSum n left right
        (su2BoundaryRelativeGauge c b) := by
  classical
  unfold su2LowerPlaneDoubleGaugedCrossingTraceSum
    su2LowerPlaneGaugedCrossingTraceSum
    su2LowerPlaneGaugedPositiveEdge
  rw [show
    (∑ p : (su2LowerCrossingPlaquettes n).attach,
      su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge
          (b (su2LowerCrossingSourceLowerBoundaryIndex n p.1 p.2))
          (b (su2LowerCrossingTargetLowerBoundaryIndex n p.1 p.2))
          (left (su2LowerCrossingLeftPositiveIndex n p.1 p.2)))
        (su2BoundaryGaugeTransformEdge
          (c (su2LowerCrossingSourceLowerBoundaryIndex n p.1 p.2))
          (c (su2LowerCrossingTargetLowerBoundaryIndex n p.1 p.2))
          (right (su2LowerCrossingLeftPositiveIndex n p.1 p.2)))) =
      ∑ p ∈ (su2LowerCrossingPlaquettes n).attach,
        su2RelativeFundamentalTrace
          (left (su2LowerCrossingLeftPositiveIndex n p.1 p.2))
          (su2BoundaryGaugeTransformEdge
            ((su2BoundaryRelativeGauge c b)
              (su2LowerCrossingSourceLowerBoundaryIndex n p.1 p.2))
            ((su2BoundaryRelativeGauge c b)
              (su2LowerCrossingTargetLowerBoundaryIndex n p.1 p.2))
            (right (su2LowerCrossingRightPositiveIndex n p.1 p.2))) by
    rw [Finset.sum_attach]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← su2_lower_crossing_positive_index_coincides n p hp]
    exact su2_relative_trace_two_boundary_gauges_reduce
      (c (su2LowerCrossingSourceLowerBoundaryIndex n p hp))
      (c (su2LowerCrossingTargetLowerBoundaryIndex n p hp))
      (b (su2LowerCrossingSourceLowerBoundaryIndex n p hp))
      (b (su2LowerCrossingTargetLowerBoundaryIndex n p hp))
      (right (su2LowerCrossingRightPositiveIndex n p hp))
      (left (su2LowerCrossingLeftPositiveIndex n p hp))]
  rfl

end RequestProject.YangMills
