import Mathlib
import YangMills.LiteralSU2CrossingHalfPathGaugeReadback

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2RelativeFundamentalTrace
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right) p)
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right) p) =
    su2RelativeFundamentalTrace
      (right (su2UpperCrossingRightPositiveIndex n p hp))
      (su2BoundaryGaugeTransformEdge
        (boundary (su2UpperCrossingSourceBoundaryIndex n p hp))
        (boundary (su2UpperCrossingTargetBoundaryIndex n p hp))
        (left (su2UpperCrossingLeftPositiveIndex n p hp))) :=
  su2_upper_crossing_half_path_trace_gauge_readback n left right boundary p hp

example
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2RelativeFundamentalTrace
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right) p)
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right) p) =
    su2RelativeFundamentalTrace
      (left (su2LowerCrossingLeftPositiveIndex n p hp))
      (su2BoundaryGaugeTransformEdge
        (boundary (su2LowerCrossingSourceBoundaryIndex n p hp))
        (boundary (su2LowerCrossingTargetBoundaryIndex n p hp))
        (right (su2LowerCrossingRightPositiveIndex n p hp))) :=
  su2_lower_crossing_half_path_trace_gauge_readback n left right boundary p hp

end RequestProject.YangMills
