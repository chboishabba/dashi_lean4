import Mathlib
import YangMills.LiteralSU2BoundaryGaugeRelative
import YangMills.LiteralSU2CrossingGaugeSumReadback

/-!
# Full crossing trace with two independent boundary gauges

The augmented RP representation naturally gauges the positive-copy edge on each
side with an independent temporal-boundary field.  Pointwise SU(2) algebra says
the pair depends only on the relative field `b * c⁻¹`.  This file lifts that
local statement through the exact upper/lower crossing sums.
-/

namespace RequestProject.YangMills

/-- Pointwise relative temporal-boundary field. -/
def su2RelativeBoundaryField
    {n : ℕ} [NeZero n]
    (b c : SU2BoundaryTemporalLinks n) : SU2BoundaryTemporalLinks n :=
  fun p => b p * (c p)⁻¹

/-- Upper crossing sum with independently gauged left and right copies. -/
def su2UpperDoubleGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) : ℝ :=
  ∑ p ∈ (su2UpperCrossingPlaquettes n).attach,
    su2RelativeFundamentalTrace
      (su2BoundaryGaugeTransformEdge
        (b (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
        (b (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
        (left (su2UpperCrossingLeftPositiveIndex n p.1 p.2)))
      (su2BoundaryGaugeTransformEdge
        (c (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
        (c (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
        (right (su2UpperCrossingRightPositiveIndex n p.1 p.2)))

/-- Lower crossing sum uses the opposite positive-copy orientation. -/
def su2LowerDoubleGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) : ℝ :=
  ∑ p ∈ (su2LowerCrossingPlaquettes n).attach,
    su2RelativeFundamentalTrace
      (su2BoundaryGaugeTransformEdge
        (b (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
        (b (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
        (right (su2LowerCrossingRightPositiveIndex n p.1 p.2)))
      (su2BoundaryGaugeTransformEdge
        (c (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
        (c (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
        (left (su2LowerCrossingLeftPositiveIndex n p.1 p.2)))

/-- Complete independently gauged crossing trace. -/
def su2DoubleGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) : ℝ :=
  su2UpperDoubleGaugedCrossingTraceSum n left right b c +
    su2LowerDoubleGaugedCrossingTraceSum n left right b c

/-- Upper double-gauged trace is the existing upper trace at the relative field. -/
theorem su2_upper_double_gauged_crossing_trace_sum_relative
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) :
    su2UpperDoubleGaugedCrossingTraceSum n left right b c =
      su2UpperGaugedCrossingTraceSum n left right
        (su2RelativeBoundaryField b c) := by
  classical
  unfold su2UpperDoubleGaugedCrossingTraceSum
    su2UpperGaugedCrossingTraceSum
  apply Finset.sum_congr rfl
  intro p hp
  unfold su2RelativeBoundaryField
  exact su2_relative_trace_two_boundary_gauges_relative_swapped
    (b (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
    (b (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
    (c (su2UpperCrossingSourceBoundaryIndex n p.1 p.2))
    (c (su2UpperCrossingTargetBoundaryIndex n p.1 p.2))
    (left (su2UpperCrossingLeftPositiveIndex n p.1 p.2))
    (right (su2UpperCrossingRightPositiveIndex n p.1 p.2))

/-- Lower double-gauged trace is the existing lower trace at the same relative field. -/
theorem su2_lower_double_gauged_crossing_trace_sum_relative
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) :
    su2LowerDoubleGaugedCrossingTraceSum n left right b c =
      su2LowerGaugedCrossingTraceSum n left right
        (su2RelativeBoundaryField b c) := by
  classical
  unfold su2LowerDoubleGaugedCrossingTraceSum
    su2LowerGaugedCrossingTraceSum
  apply Finset.sum_congr rfl
  intro p hp
  unfold su2RelativeBoundaryField
  exact su2_relative_trace_two_boundary_gauges_relative_swapped
    (b (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
    (b (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
    (c (su2LowerCrossingSourceBoundaryIndex n p.1 p.2))
    (c (su2LowerCrossingTargetBoundaryIndex n p.1 p.2))
    (right (su2LowerCrossingRightPositiveIndex n p.1 p.2))
    (left (su2LowerCrossingLeftPositiveIndex n p.1 p.2))

/-- Whole crossing reduction to one relative temporal-boundary field. -/
theorem su2_double_gauged_crossing_trace_sum_relative
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) :
    su2DoubleGaugedCrossingTraceSum n left right b c =
      su2UpperGaugedCrossingTraceSum n left right
        (su2RelativeBoundaryField b c) +
      su2LowerGaugedCrossingTraceSum n left right
        (su2RelativeBoundaryField b c) := by
  unfold su2DoubleGaugedCrossingTraceSum
  rw [su2_upper_double_gauged_crossing_trace_sum_relative,
    su2_lower_double_gauged_crossing_trace_sum_relative]

end RequestProject.YangMills
