import Mathlib
import YangMills.LiteralSU2BoundaryProjectedKernelPlaneSplit

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryGaugeProjectedWilsonKernel n β left right =
      ∫ planes : SU2BoundaryPlaneFields n,
        literalSU2ReflectedPairWilsonDensity n β left
          (su2BoundaryTemporalPlaneAssemble n planes) right
        ∂(literalSU2BoundaryPlaneHaar n) :=
  literal_su2_boundary_projected_kernel_plane_split n β left right

end RequestProject.YangMills
