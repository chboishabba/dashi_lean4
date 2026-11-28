import YangMills.LiteralSU2BoundaryPlaneDoubleGauge

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2UpperBoundaryTemporalLinks n) :
    su2UpperPlaneDoubleGaugedCrossingTraceSum n left right b c =
      su2UpperPlaneGaugedCrossingTraceSum n left right
        (su2BoundaryRelativeGauge b c) :=
  su2_upper_plane_double_gauge_reduce n left right b c

example
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (b c : SU2LowerBoundaryTemporalLinks n) :
    su2LowerPlaneDoubleGaugedCrossingTraceSum n left right b c =
      su2LowerPlaneGaugedCrossingTraceSum n left right
        (su2BoundaryRelativeGauge c b) :=
  su2_lower_plane_double_gauge_reduce n left right b c

end RequestProject.YangMills
