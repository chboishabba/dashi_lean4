import Mathlib
import YangMills.LiteralSU2BoundaryGaugeProjectionCut
import YangMills.LiteralSU2PlaquetteIndexReflection

/-!
# Reflection symmetry of the boundary-gauge-projected Wilson kernel

Before proving positivity of the exact surviving finite-Wilson kernel, isolate
its involutive symmetry on the SAME literal objects.

This file first proves two unconditional facts needed by the final projection
argument:

* the full physical plaquette set is invariant under the selected plaquette
  index reflection, hence the complete literal Wilson product is invariant
  under link reflection;
* pointwise inversion preserves the product Haar law on the temporal boundary
  links.

The remaining same-object step is to identify reflection of the assembled
(left,boundary,reflected-right) field with the assembled
(right,boundary^{-1},reflected-left) field.  Once that identity is paid, kernel
symmetry follows by the boundary-Haar change of variables.  No positivity is
claimed from symmetry alone.
-/

namespace RequestProject.YangMills

/-- Reflection preserves membership in the complete physical plaquette set. -/
theorem su2_reflected_plaquette_index_physical_iff
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n)) :
    su2EvenTimeReflectPlaquetteIndex p ∈
        su2FourDimensionalPlaquettes (2 * n) ↔
      p ∈ su2FourDimensionalPlaquettes (2 * n) := by
  simp only [su2FourDimensionalPlaquettes,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [su2_even_time_reflect_plaquette_index_directions]

/-- The selected plaquette reflection permutes the full physical set exactly. -/
theorem su2_full_plaquette_set_reflection_image
    (n : ℕ) [NeZero n] :
    (su2FourDimensionalPlaquettes (2 * n)).image
        su2EvenTimeReflectPlaquetteIndex =
      su2FourDimensionalPlaquettes (2 * n) := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, hqp⟩
    rw [← hqp]
    exact (su2_reflected_plaquette_index_physical_iff n q).2 hq
  · intro hp
    refine Finset.mem_image.mpr
      ⟨su2EvenTimeReflectPlaquetteIndex p, ?_, ?_⟩
    · exact (su2_reflected_plaquette_index_physical_iff n
        (su2EvenTimeReflectPlaquetteIndex p)).1 (by
          simpa [su2_even_time_reflect_plaquette_index_involutive] using hp)
    · exact su2_even_time_reflect_plaquette_index_involutive p

/--
The entire literal Wilson density is invariant under the selected link
reflection.  This is stronger than the already-owned positive/negative-half
transport and uses no boundary conditioning.
-/
theorem su2_literal_full_wilson_reflection_invariant
    (n : ℕ) [NeZero n]
    (links : SU2TorusLinks (2 * n))
    (β : ℝ) :
    su2LiteralWilsonProduct
        (su2FourDimensionalPlaquettes (2 * n))
        (su2EvenTimeReflectLinks links) β =
      su2LiteralWilsonProduct
        (su2FourDimensionalPlaquettes (2 * n))
        links β := by
  rw [su2_literal_wilson_product_reflection_transport]
  · rw [su2_full_plaquette_set_reflection_image]
  · intro p hp
    exact hp

/-- Pointwise inversion of the shared temporal boundary field. -/
def su2BoundaryTemporalInvert
    {n : ℕ} [NeZero n]
    (boundary : SU2BoundaryTemporalLinks n) :
    SU2BoundaryTemporalLinks n :=
  fun p => (boundary p)⁻¹

/-- Boundary inversion is measurable coordinatewise. -/
theorem su2_boundary_temporal_invert_measurable
    (n : ℕ) [NeZero n] :
    Measurable (@su2BoundaryTemporalInvert n _) := by
  apply measurable_pi_lambda
  intro p
  exact literal_su2_inv_measurable.comp (measurable_apply p)

/--
The actual boundary product Haar law is invariant under simultaneous
pointwise inversion of every temporal boundary link.
-/
theorem literal_su2_boundary_temporal_haar_inversion_invariant
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@su2BoundaryTemporalInvert n _)
      (literalSU2BoundaryTemporalHaar n) =
      literalSU2BoundaryTemporalHaar n := by
  let μ : MeasureTheory.Measure SU2PlaquetteHolonomy :=
    ((literalSU2OneLinkHaar :
      MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
      MeasureTheory.Measure SU2PlaquetteHolonomy)
  change MeasureTheory.Measure.map
      (fun boundary p => (boundary p)⁻¹)
      (MeasureTheory.Measure.pi
        (fun _ : SU2BoundaryTemporalLinkIndex n => μ)) =
    MeasureTheory.Measure.pi
      (fun _ : SU2BoundaryTemporalLinkIndex n => μ)
  rw [MeasureTheory.Measure.pi_map_pi]
  · congr with p
    simpa [μ] using literal_su2_one_link_haar_inversion_invariant
  · intro p
    exact literal_su2_inv_measurable.aemeasurable

end RequestProject.YangMills
