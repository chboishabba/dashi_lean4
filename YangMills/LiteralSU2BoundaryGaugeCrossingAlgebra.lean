import Mathlib
import YangMills.LiteralSU2BoundaryGaugeTrace

/-!
# Local crossing algebra for the two boundary Haar slabs

After splitting the temporal boundary into the two independent reflection
slabs, every temporal-spatial crossing plaquette has one of two local forms.
Writing `b₀,b₁` for the temporal boundary holonomies at the two spatial
endpoints and `L,R` for the two positive-copy spatial edge values, the upper
slab contributes

  q(b₀ R, L b₁),

while the periodic lower slab contributes

  q(b₀ L, R b₁).

Both are exactly ordinary relative-trace kernels after a vertex gauge action

  G_b(U) = b₀⁻¹ U b₁

on one positive copy.  These identities are the algebraic core of the
boundary-gauge-projection proof; the separate lattice file must still identify
the literal crossing half paths with these four same-object edge values.
-/

namespace RequestProject.YangMills

/-- Gauge transform of one oriented spatial edge by its endpoint variables. -/
def su2BoundaryGaugeTransformEdge
    (source target edge : SU2PlaquetteHolonomy) : SU2PlaquetteHolonomy :=
  source⁻¹ * edge * target

/-- Upper reflection slab: the boundary field gauges the left positive copy. -/
theorem su2_upper_crossing_trace_is_gauged_left
    (source target left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
        (source * right) (left * target) =
      su2RelativeFundamentalTrace
        right (su2BoundaryGaugeTransformEdge source target left) := by
  simpa [su2BoundaryGaugeTransformEdge] using
    su2_relative_trace_absorb_endpoint_gauge
      source target right left

/-- Periodic lower slab: the boundary field gauges the right positive copy. -/
theorem su2_lower_crossing_trace_is_gauged_right
    (source target left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
        (source * left) (right * target) =
      su2RelativeFundamentalTrace
        left (su2BoundaryGaugeTransformEdge source target right) := by
  simpa [su2BoundaryGaugeTransformEdge] using
    su2_relative_trace_absorb_endpoint_gauge
      source target left right

/-- Unit boundary values recover the un-gauged edge exactly. -/
@[simp] theorem su2_boundary_gauge_transform_edge_one
    (edge : SU2PlaquetteHolonomy) :
    su2BoundaryGaugeTransformEdge
      (1 : SU2PlaquetteHolonomy) (1 : SU2PlaquetteHolonomy) edge = edge := by
  simp [su2BoundaryGaugeTransformEdge]

end RequestProject.YangMills
