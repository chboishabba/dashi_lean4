import Mathlib
import YangMills.LiteralSU2BoundaryHaarTranslation
import YangMills.LiteralSU2BoundaryGaugeCrossingAlgebra

/-!
# Algebra behind the boundary-Haar gauge projector

A crossing trace with independent endpoint gauges on both positive halves can
be reduced to a single relative gauge field.  The relative field is exactly the
pointwise quotient `b * c⁻¹`, which is distributed as Haar when `b` is Haar and
`c` is fixed.  This identity is the local algebraic engine for replacing the
single physical boundary average by a double independent gauge average.
-/

namespace RequestProject.YangMills

/-- The normalized SU(2) relative trace is symmetric. -/
theorem su2_relative_fundamental_trace_symmetric
    (left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace left right =
      su2RelativeFundamentalTrace right left := by
  rw [su2_relative_trace_eq_quaternion_dot,
    su2_relative_trace_eq_quaternion_dot]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/--
Two independently gauged edges reduce to one relative boundary gauge.

  q(G_c R, G_b L) = q(R, G_{b c⁻¹} L).
-/
theorem su2_relative_trace_two_boundary_gauges_reduce
    (b₀ b₁ c₀ c₁ left right : SU2PlaquetteHolonomy) :
    su2RelativeFundamentalTrace
      (su2BoundaryGaugeTransformEdge c₀ c₁ right)
      (su2BoundaryGaugeTransformEdge b₀ b₁ left) =
    su2RelativeFundamentalTrace right
      (su2BoundaryGaugeTransformEdge
        (b₀ * c₀⁻¹) (b₁ * c₁⁻¹) left) := by
  unfold su2RelativeFundamentalTrace su2BoundaryGaugeTransformEdge
  have hcyclic :
      (c₀⁻¹ * right * c₁ * (b₀⁻¹ * left * b₁)⁻¹).a =
        (right * c₁ * (b₀⁻¹ * left * b₁)⁻¹ * c₀⁻¹).a := by
    calc
      (c₀⁻¹ * right * c₁ * (b₀⁻¹ * left * b₁)⁻¹).a =
          (c₀⁻¹ * (right * c₁ * (b₀⁻¹ * left * b₁)⁻¹)).a := by
            congr 1
            group
      _ = ((right * c₁ * (b₀⁻¹ * left * b₁)⁻¹) * c₀⁻¹).a :=
        su2_real_trace_cyclic c₀⁻¹
          (right * c₁ * (b₀⁻¹ * left * b₁)⁻¹)
  rw [hcyclic]
  congr 1
  group

/-- Pointwise relative quotient of two boundary gauge fields. -/
def su2BoundaryRelativeGauge
    {I : Type*}
    (b c : I → SU2PlaquetteHolonomy) : I → SU2PlaquetteHolonomy :=
  fun i => b i * (c i)⁻¹

@[simp] theorem su2_boundary_relative_gauge_apply
    {I : Type*}
    (b c : I → SU2PlaquetteHolonomy) (i : I) :
    su2BoundaryRelativeGauge b c i = b i * (c i)⁻¹ := rfl

/-- For fixed `c`, relative-gauge formation is measurable in `b`. -/
theorem su2_boundary_relative_gauge_measurable
    {I : Type*}
    (c : I → SU2PlaquetteHolonomy) :
    Measurable (fun b : I → SU2PlaquetteHolonomy =>
      su2BoundaryRelativeGauge b c) := by
  apply measurable_pi_lambda
  intro i
  fun_prop

end RequestProject.YangMills
