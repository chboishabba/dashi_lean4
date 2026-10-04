import Mathlib
import YangMills.LiteralSU2BoundaryGaugeCrossingAlgebra

/-!
# Two boundary gauges reduce to one relative gauge

The augmented reflection-positive kernel uses an independently gauged copy on
each half space.  For the literal SU(2) relative trace, two endpoint gauge
fields `b` and `c` combine without commutation into the single relative field

  u = b * c⁻¹.

This is the local noncommutative algebraic weld needed before the independent
boundary Haar pair can be collapsed to the one shared boundary field appearing
in the literal projected Wilson kernel.
-/

namespace RequestProject.YangMills

/-- The literal relative-trace kernel is symmetric. -/
theorem su2_relative_fundamental_trace_symmetric
    (U V : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace U V =
      su2RelativeFundamentalTrace V U := by
  rw [su2_relative_trace_eq_quaternion_dot,
    su2_relative_trace_eq_quaternion_dot]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/--
Two independently endpoint-gauged edges depend only on the relative boundary
`b * c⁻¹`.  The ordering is exact for the noncommutative SU(2) group.
-/
theorem su2_relative_trace_two_boundary_gauges_relative
    (bs bt cs ct left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge bs bt left)
        (su2BoundaryGaugeTransformEdge cs ct right) =
      su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge
          (bs * cs⁻¹) (bt * ct⁻¹) left)
        right := by
  unfold su2RelativeFundamentalTrace su2BoundaryGaugeTransformEdge
  have hcyclic :
      (((bs⁻¹ * left * bt) * (cs⁻¹ * right * ct)⁻¹).a) =
        ((cs * (bs⁻¹ * left * bt * ct⁻¹ * right⁻¹)).a) := by
    calc
      (((bs⁻¹ * left * bt) * (cs⁻¹ * right * ct)⁻¹).a) =
          (((bs⁻¹ * left * bt * ct⁻¹ * right⁻¹) * cs).a) := by
            congr 1
            group
      _ = ((cs * (bs⁻¹ * left * bt * ct⁻¹ * right⁻¹)).a) :=
        (su2_real_trace_cyclic cs
          (bs⁻¹ * left * bt * ct⁻¹ * right⁻¹)).symm
  rw [hcyclic]
  congr 1
  group

/-- Same relative-gauge identity in the orientation used by the upper slab readback. -/
theorem su2_relative_trace_two_boundary_gauges_relative_swapped
    (bs bt cs ct left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
        (su2BoundaryGaugeTransformEdge bs bt left)
        (su2BoundaryGaugeTransformEdge cs ct right) =
      su2RelativeFundamentalTrace
        right
        (su2BoundaryGaugeTransformEdge
          (bs * cs⁻¹) (bt * ct⁻¹) left) := by
  rw [su2_relative_trace_two_boundary_gauges_relative
    bs bt cs ct left right]
  exact su2_relative_fundamental_trace_symmetric _ _

end RequestProject.YangMills
