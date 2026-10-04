import Mathlib
import YangMills.LiteralSU2FixedBoundaryNoGo

namespace RequestProject.YangMills

example :
    fixedBoundaryFirstOrderTwoPointQuadratic
      su2BoundaryWitnessOne su2BoundaryWitnessMinusOne = -4 :=
  fixed_boundary_first_order_two_point_negative

example :
    ¬ (0 ≤ fixedBoundaryFirstOrderTwoPointQuadratic
      su2BoundaryWitnessOne su2BoundaryWitnessMinusOne) :=
  fixed_boundary_first_order_not_rp

end RequestProject.YangMills
