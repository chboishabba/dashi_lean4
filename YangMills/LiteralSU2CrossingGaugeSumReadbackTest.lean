import Mathlib
import YangMills.LiteralSU2CrossingGaugeSumReadback

namespace RequestProject.YangMills

example
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
         su2LowerGaugedCrossingTraceSum n left right boundary)) :=
  su2_literal_crossing_kernel_gauge_sum_readback n β left right boundary

end RequestProject.YangMills
