import Mathlib
import YangMills.LiteralSU2BoundaryGaugeRelative

namespace RequestProject.YangMills

example
    (bs bt cs ct left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge bs bt left)
        (su2BoundaryGaugeTransformEdge cs ct right) =
      su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge
          (bs * cs⁻¹) (bt * ct⁻¹) left)
        right :=
  su2_relative_trace_two_boundary_gauges_relative
    bs bt cs ct left right

example
    (bs bt cs ct left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge bs bt left)
        (su2BoundaryGaugeTransformEdge cs ct right) =
      su2RelativeFundamentalTrace
        right
        (su2BoundaryGaugeTransformEdge
          (bs * cs⁻¹) (bt * ct⁻¹) left) :=
  su2_relative_trace_two_boundary_gauges_relative_swapped
    bs bt cs ct left right

end RequestProject.YangMills
