import YangMills.LiteralSU2BoundaryProjectedRPReduction

namespace RequestProject.YangMills

example
    (hCross : LiteralSU2BoundaryAveragedCrossingRPExact) :
    LiteralSU2BoundaryGaugeProjectionRPExact :=
  literal_su2_boundary_gauge_projection_rp_of_averaged_crossing_rp hCross

end RequestProject.YangMills
