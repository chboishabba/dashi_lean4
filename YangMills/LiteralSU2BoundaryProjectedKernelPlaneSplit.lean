import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
import YangMills.LiteralSU2BoundaryGaugeProjectionCut
import YangMills.LiteralSU2BoundaryPlaneHaarSplit

/-!
# Exact two-plane readback of the projected Wilson kernel

The selected projected kernel was originally written as one integral over the
full temporal-boundary product Haar law.  The boundary-plane theorem already
proves that this law is exactly the pushforward of the independent upper/lower
slab product Haar law.

This file performs that readback on the SAME reflected-pair Wilson density.
It introduces no replacement kernel and no RP assumption.  The remaining
Block-A same-object theorem can now work directly with the actual upper and
lower slab variables.
-/

namespace RequestProject.YangMills

/-- The reflected-pair density is measurable as a function of the boundary field. -/
theorem literal_su2_reflected_pair_density_boundary_measurable
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    Measurable
      (fun boundary : SU2BoundaryTemporalLinks n =>
        literalSU2ReflectedPairWilsonDensity n β left boundary right) := by
  unfold literalSU2ReflectedPairWilsonDensity
  fun_prop

/--
The actual projected kernel is exactly the same Wilson density integrated over
the independent upper/lower boundary-plane carrier.
-/
theorem literal_su2_boundary_projected_kernel_plane_split
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryGaugeProjectedWilsonKernel n β left right =
      ∫ planes : SU2BoundaryPlaneFields n,
        literalSU2ReflectedPairWilsonDensity n β left
          (su2BoundaryTemporalPlaneAssemble n planes) right
        ∂(literalSU2BoundaryPlaneHaar n) := by
  unfold literalSU2BoundaryGaugeProjectedWilsonKernel
  rw [← literal_su2_boundary_temporal_haar_plane_split n]
  rw [MeasureTheory.integral_map
    (su2_boundary_temporal_plane_assemble_measurable n).aemeasurable]
  exact
    (literal_su2_reflected_pair_density_boundary_measurable n β left right).aestronglyMeasurable

/--
Fubini form of the exact same projected kernel.  Integrability is kept explicit
here; it is a property of the literal finite Wilson density rather than an
abstract projection assumption.
-/
theorem literal_su2_boundary_projected_kernel_iterated_planes
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (hInt : MeasureTheory.Integrable
      (fun planes : SU2BoundaryPlaneFields n =>
        literalSU2ReflectedPairWilsonDensity n β left
          (su2BoundaryTemporalPlaneAssemble n planes) right)
      (literalSU2BoundaryPlaneHaar n)) :
    literalSU2BoundaryGaugeProjectedWilsonKernel n β left right =
      ∫ upper : SU2UpperBoundaryTemporalLinks n,
        ∫ lower : SU2LowerBoundaryTemporalLinks n,
          literalSU2ReflectedPairWilsonDensity n β left
            (su2BoundaryTemporalPlaneAssemble n (upper, lower)) right
          ∂(literalSU2LowerBoundaryTemporalHaar n)
        ∂(literalSU2UpperBoundaryTemporalHaar n) := by
  rw [literal_su2_boundary_projected_kernel_plane_split n β left right]
  unfold literalSU2BoundaryPlaneHaar
  exact MeasureTheory.integral_prod _ hInt

end RequestProject.YangMills
