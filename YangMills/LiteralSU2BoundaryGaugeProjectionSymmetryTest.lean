import Mathlib
import YangMills.LiteralSU2BoundaryGaugeProjectionSymmetry

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (links : SU2TorusLinks (2 * n)) :
    su2LiteralWilsonProduct
        (su2FourDimensionalPlaquettes (2 * n))
        (su2EvenTimeReflectLinks links) β =
      su2LiteralWilsonProduct
        (su2FourDimensionalPlaquettes (2 * n))
        links β :=
  su2_literal_full_wilson_reflection_invariant n links β

example
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2EvenTimeReflectLinks
        (su2AssembleReflectedPair n left boundary right) =
      su2AssembleReflectedPair n right
        (su2BoundaryTemporalInvert boundary) left :=
  su2_reflect_assembled_pair n left boundary right

example
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryGaugeProjectedWilsonKernel n β left right =
      literalSU2BoundaryGaugeProjectedWilsonKernel n β right left :=
  literal_su2_boundary_gauge_projected_kernel_symmetric
    n β left right

end RequestProject.YangMills
