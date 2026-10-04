import Mathlib
import YangMills.LiteralSU2CrossingGaugePlaneLocality

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (planes : SU2BoundaryPlaneFields n) :
    su2UpperGaugedCrossingTraceSum n left right
      (su2BoundaryTemporalPlaneAssemble n planes) =
    su2UpperPlaneGaugedCrossingTraceSum n left right planes.1 :=
  su2_upper_gauged_crossing_sum_plane_readback n left right planes

example
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (planes : SU2BoundaryPlaneFields n) :
    su2LowerGaugedCrossingTraceSum n left right
      (su2BoundaryTemporalPlaneAssemble n planes) =
    su2LowerPlaneGaugedCrossingTraceSum n left right planes.2 :=
  su2_lower_gauged_crossing_sum_plane_readback n left right planes

end RequestProject.YangMills
