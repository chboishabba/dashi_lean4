import Mathlib
import YangMills.LiteralSU2CrossingHalfPathGaugeReadback
import YangMills.LiteralSU2CrossingSlabGeometry
import YangMills.LiteralSU2WilsonReflectionPlane

/-!
# Complete crossing-plane gauge-sum readback

The pointwise upper/lower half-path identities are lifted here to the exact
crossing trace sum and hence to the literal crossing Wilson kernel.

The gauged sums use `Finset.attach` so every summand carries the literal
membership proof needed by the dependent edge-index readback.  No positivity
or averaging is introduced: this is purely a same-object rewrite of the
crossing factor appearing in `su2_literal_full_wilson_os_factorization`.
-/

namespace RequestProject.YangMills

/-- Upper-slab crossing trace written entirely on positive-copy edges plus boundary gauges. -/
def su2UpperGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) : ℝ :=
  ∑ p ∈ (su2UpperCrossingPlaquettes n).attach,
    su2RelativeFundamentalTrace
      (right (su2UpperCrossingRightPositiveIndex n p.1 p.2))
      (su2BoundaryGaugeTransformEdge
        (boundary (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
        (boundary (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
        (left (su2UpperCrossingLeftPositiveIndex n p.1 p.2)))

/-- Lower-slab crossing trace written entirely on positive-copy edges plus boundary gauges. -/
def su2LowerGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) : ℝ :=
  ∑ p ∈ (su2LowerCrossingPlaquettes n).attach,
    su2RelativeFundamentalTrace
      (left (su2LowerCrossingLeftPositiveIndex n p.1 p.2))
      (su2BoundaryGaugeTransformEdge
        (boundary (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
        (boundary (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
        (right (su2LowerCrossingRightPositiveIndex n p.1 p.2)))

/-- Exact upper-slab trace-sum readback. -/
theorem su2_upper_crossing_trace_sum_gauge_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2CrossingTraceSum (su2UpperCrossingPlaquettes n)
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right))
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right)) =
    su2UpperGaugedCrossingTraceSum n left right boundary := by
  unfold su2CrossingTraceSum su2UpperGaugedCrossingTraceSum
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro p hp
  exact su2_upper_crossing_half_path_trace_gauge_readback
    n left right boundary p.1 p.2

/-- Exact lower-slab trace-sum readback. -/
theorem su2_lower_crossing_trace_sum_gauge_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2CrossingTraceSum (su2LowerCrossingPlaquettes n)
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right))
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right)) =
    su2LowerGaugedCrossingTraceSum n left right boundary := by
  unfold su2CrossingTraceSum su2LowerGaugedCrossingTraceSum
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro p hp
  exact su2_lower_crossing_half_path_trace_gauge_readback
    n left right boundary p.1 p.2

/-- The full crossing trace is exactly upper gauged plus lower gauged. -/
theorem su2_full_crossing_trace_sum_gauge_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2CrossingTraceSum (su2EvenTimeCrossingPlaquettes n)
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right))
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right)) =
    su2UpperGaugedCrossingTraceSum n left right boundary +
      su2LowerGaugedCrossingTraceSum n left right boundary := by
  rw [← su2_crossing_slabs_partition n]
  unfold su2CrossingTraceSum
  rw [Finset.sum_union (su2_crossing_slabs_disjoint n)]
  rw [su2_upper_crossing_trace_sum_gauge_readback n left right boundary,
    su2_lower_crossing_trace_sum_gauge_readback n left right boundary]

/--
The exact literal crossing Wilson kernel is the exponential of the upper/lower
boundary-gauge sums.  This is the final same-object crossing-kernel formula
needed by the boundary-Haar positivity calculation.
-/
theorem su2_literal_crossing_kernel_gauge_sum_readback
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2WilsonCrossingPlaneKernel
      (su2EvenTimeCrossingPlaquettes n) β
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right))
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right)) =
    Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ))) *
      Real.exp (β *
        (su2UpperGaugedCrossingTraceSum n left right boundary +
         su2LowerGaugedCrossingTraceSum n left right boundary)) := by
  unfold su2WilsonCrossingPlaneKernel
  rw [su2_full_crossing_trace_sum_gauge_readback]

end RequestProject.YangMills
