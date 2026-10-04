import YangMills.LiteralSU2BoundaryGaugeProjectionAlgebra

namespace RequestProject.YangMills

example
    (b₀ b₁ c₀ c₁ left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
      (su2BoundaryGaugeTransformEdge c₀ c₁ right)
      (su2BoundaryGaugeTransformEdge b₀ b₁ left) =
    su2RelativeFundamentalTrace right
      (su2BoundaryGaugeTransformEdge
        (b₀ * c₀⁻¹) (b₁ * c₁⁻¹) left) :=
  su2_relative_trace_two_boundary_gauges_reduce b₀ b₁ c₀ c₁ left right

end RequestProject.YangMills
