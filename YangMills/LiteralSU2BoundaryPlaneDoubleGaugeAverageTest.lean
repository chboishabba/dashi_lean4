import YangMills.LiteralSU2BoundaryPlaneDoubleGaugeAverage

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryPlaneAveragedDoubleGaugedCrossingKernel n β left right =
      literalSU2BoundaryAveragedCrossingKernel n β left right :=
  literal_su2_boundary_plane_double_gauge_average_eq_literal n β left right

end RequestProject.YangMills
