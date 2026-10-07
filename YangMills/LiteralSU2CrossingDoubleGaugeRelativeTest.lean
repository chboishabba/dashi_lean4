import Mathlib
import YangMills.LiteralSU2CrossingDoubleGaugeRelative

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2BoundaryTemporalLinks n) :
    su2DoubleGaugedCrossingTraceSum n left right b c =
      su2UpperGaugedCrossingTraceSum n left right
        (su2RelativeBoundaryField b c) +
      su2LowerGaugedCrossingTraceSum n left right
        (su2RelativeBoundaryField b c) :=
  su2_double_gauged_crossing_trace_sum_relative n left right b c

end RequestProject.YangMills
