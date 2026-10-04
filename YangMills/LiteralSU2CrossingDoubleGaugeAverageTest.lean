import Mathlib
import YangMills.LiteralSU2CrossingDoubleGaugeAverage

open MeasureTheory

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    (∫ b, ∫ c,
      su2DoubleGaugedCrossingKernel n β left right b c
      ∂(literalSU2BoundaryTemporalHaar n)
      ∂(literalSU2BoundaryTemporalHaar n)) =
      ∫ u,
        su2WilsonCrossingPlaneKernel
          (su2EvenTimeCrossingPlaquettes n) β
          (su2LiteralCrossingFirstBoundary
            (su2AssembleReflectedPair n left u right))
          (su2LiteralCrossingSecondBoundary
            (su2AssembleReflectedPair n left u right))
        ∂(literalSU2BoundaryTemporalHaar n) :=
  su2_double_gauged_crossing_average_eq_literal n β left right

end RequestProject.YangMills
