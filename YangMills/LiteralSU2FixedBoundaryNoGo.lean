import Mathlib
import YangMills.LiteralSU2BoundaryWilsonRP

/-!
# Fixed temporal-boundary conditioning is not reflection-positive

The final finite-Haar OS2 proof must integrate the temporal boundary links.
It is NOT valid to condition on an arbitrary fixed boundary field and invoke
the positive kernel theorem there.

Already for one first-order crossing plaquette, choose the two fixed temporal
boundary holonomies g=1 and h=-1.  The side kernel is

  K(Q,P) = 1 + q(g Q, P h) = 1 - q(Q,P).

On the exact Q8 points Q,P in {1,-1}, its 2x2 matrix is [[0,2],[2,0]],
and the quadratic form on (1,-1) is -4.

Thus the remaining Wilson OS2 theorem genuinely needs the Haar-averaged
boundary/gauge-projection argument; ordinary conditional Fubini is ruled out.
-/

namespace RequestProject.YangMills

/-- Literal +1 unit quaternion. -/
def su2BoundaryWitnessOne : SU2PlaquetteHolonomy :=
  (1 : SU2PlaquetteHolonomy)

/-- Literal -1 unit quaternion. -/
def su2BoundaryWitnessMinusOne : SU2PlaquetteHolonomy :=
  ⟨-1, 0, 0, 0, by norm_num⟩

/-- First-order crossing kernel after fixing left/right boundary holonomies. -/
def fixedBoundaryFirstOrderKernel
    (g h Q P : SU2PlaquetteHolonomy) : ℝ :=
  su2FirstOrderCrossingWilsonKernel 1 (g * Q) (P * h)

/-- The two-point quadratic form for coefficients (+1,-1). -/
def fixedBoundaryFirstOrderTwoPointQuadratic
    (g h : SU2PlaquetteHolonomy) : ℝ :=
  fixedBoundaryFirstOrderKernel g h
      su2BoundaryWitnessOne su2BoundaryWitnessOne
    - fixedBoundaryFirstOrderKernel g h
      su2BoundaryWitnessOne su2BoundaryWitnessMinusOne
    - fixedBoundaryFirstOrderKernel g h
      su2BoundaryWitnessMinusOne su2BoundaryWitnessOne
    + fixedBoundaryFirstOrderKernel g h
      su2BoundaryWitnessMinusOne su2BoundaryWitnessMinusOne

@[simp] theorem fixed_boundary_witness_minus_one_mul_self :
    su2BoundaryWitnessMinusOne * su2BoundaryWitnessMinusOne =
      su2BoundaryWitnessOne := by
  apply su2_holonomy_ext <;>
    simp [su2BoundaryWitnessMinusOne, su2BoundaryWitnessOne,
      Mul.mul, su2Mul]

@[simp] theorem fixed_boundary_witness_one_mul_minus_one :
    su2BoundaryWitnessOne * su2BoundaryWitnessMinusOne =
      su2BoundaryWitnessMinusOne := by
  simp [su2BoundaryWitnessOne]

@[simp] theorem fixed_boundary_witness_minus_one_mul_one :
    su2BoundaryWitnessMinusOne * su2BoundaryWitnessOne =
      su2BoundaryWitnessMinusOne := by
  simp [su2BoundaryWitnessOne]

@[simp] theorem fixed_boundary_relative_trace_same_one :
    su2RelativeFundamentalTrace
      su2BoundaryWitnessOne su2BoundaryWitnessMinusOne = -1 := by
  simp [su2RelativeFundamentalTrace,
    su2BoundaryWitnessOne, su2BoundaryWitnessMinusOne,
    Mul.mul, Inv.inv, su2Mul, su2Inv]

@[simp] theorem fixed_boundary_relative_trace_same_minus :
    su2RelativeFundamentalTrace
      su2BoundaryWitnessMinusOne su2BoundaryWitnessOne = -1 := by
  simp [su2RelativeFundamentalTrace,
    su2BoundaryWitnessOne, su2BoundaryWitnessMinusOne,
    Mul.mul, Inv.inv, su2Mul, su2Inv]

/-- Exact negative two-point direction. -/
theorem fixed_boundary_first_order_two_point_negative :
    fixedBoundaryFirstOrderTwoPointQuadratic
      su2BoundaryWitnessOne su2BoundaryWitnessMinusOne = -4 := by
  norm_num [fixedBoundaryFirstOrderTwoPointQuadratic,
    fixedBoundaryFirstOrderKernel,
    su2FirstOrderCrossingWilsonKernel,
    su2RelativeFundamentalTrace,
    su2BoundaryWitnessOne, su2BoundaryWitnessMinusOne,
    Mul.mul, Inv.inv, su2Mul, su2Inv]

/-- Hence fixed-boundary conditioning cannot be the missing OS2 proof. -/
theorem fixed_boundary_first_order_not_rp :
    ¬ (0 ≤ fixedBoundaryFirstOrderTwoPointQuadratic
      su2BoundaryWitnessOne su2BoundaryWitnessMinusOne) := by
  rw [fixed_boundary_first_order_two_point_negative]
  norm_num

end RequestProject.YangMills
