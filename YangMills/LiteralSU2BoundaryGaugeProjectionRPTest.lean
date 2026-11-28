import Mathlib
import YangMills.LiteralSU2BoundaryGaugeProjectionRP

namespace RequestProject.YangMills

example
    (producer : LiteralSU2BoundaryGaugeProjectionProducer) :
    LiteralSU2BoundaryGaugeProjectionRPExact :=
  literal_su2_boundary_gauge_projection_rp_of_producer producer

end RequestProject.YangMills
