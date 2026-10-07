import Mathlib
import YangMills.LiteralSU2BoundaryGaugeTrace

namespace RequestProject.YangMills

example
    (g h Q P : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace (g * Q) (P * h) =
      su2RelativeFundamentalTrace Q (g⁻¹ * P * h) :=
  su2_relative_trace_absorb_endpoint_gauge g h Q P

example
    (g Q P : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace (g * Q) P =
      su2RelativeFundamentalTrace Q (g⁻¹ * P) := by
  simpa using su2_relative_trace_absorb_left_gauge g Q P

end RequestProject.YangMills
