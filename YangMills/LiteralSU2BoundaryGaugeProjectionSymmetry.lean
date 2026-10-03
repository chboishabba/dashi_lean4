import Mathlib
import YangMills.LiteralSU2BoundaryGaugeProjectionCut
import YangMills.LiteralSU2PlaquetteIndexReflection

/-!
# Reflection symmetry of the boundary-gauge-projected Wilson kernel

Before proving positivity of the exact surviving finite-Wilson kernel, isolate
its involutive symmetry on the SAME literal objects.

This file proves the same-object geometry needed by the final projection
argument:

* the full physical plaquette set is invariant under the selected plaquette
  index reflection, hence the complete literal Wilson product is invariant
  under link reflection;
* pointwise inversion preserves the product Haar law on the temporal boundary
  links;
* reflecting the assembled (left,boundary,reflected-right) field swaps the two
  positive interiors and inverts the fixed temporal boundary.

Kernel symmetry is then only the boundary-Haar change-of-variables step.  No
positivity is claimed from symmetry alone.
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

------------------------------------------------------------------------
-- Exact readback from the three physical link sectors.
------------------------------------------------------------------------

@[simp] theorem su2_literal_sector_assemble_positive
    (n : ℕ) [NeZero n]
    (fields : SU2LinkSectorFields n)
    (p : SU2PositiveInteriorLinkIndex n) :
    su2LiteralSectorAssemble n fields p.1 = fields.1 p := by
  have hsymm :
      (su2LinkSectorSumEquiv n).symm p.1 = Sum.inl p := by
    apply (su2LinkSectorSumEquiv n).injective
    simp [su2LinkSectorSumEquiv]
  simp [su2LiteralSectorAssemble, hsymm]

@[simp] theorem su2_literal_sector_assemble_boundary
    (n : ℕ) [NeZero n]
    (fields : SU2LinkSectorFields n)
    (p : SU2BoundaryTemporalLinkIndex n) :
    su2LiteralSectorAssemble n fields p.1 = fields.2.1 p := by
  have hsymm :
      (su2LinkSectorSumEquiv n).symm p.1 = Sum.inr (Sum.inl p) := by
    apply (su2LinkSectorSumEquiv n).injective
    simp [su2LinkSectorSumEquiv]
  simp [su2LiteralSectorAssemble, hsymm]

@[simp] theorem su2_literal_sector_assemble_negative
    (n : ℕ) [NeZero n]
    (fields : SU2LinkSectorFields n)
    (p : SU2NegativeInteriorLinkIndex n) :
    su2LiteralSectorAssemble n fields p.1 = fields.2.2 p := by
  have hsymm :
      (su2LinkSectorSumEquiv n).symm p.1 = Sum.inr (Sum.inr p) := by
    apply (su2LinkSectorSumEquiv n).injective
    simp [su2LinkSectorSumEquiv]
  simp [su2LiteralSectorAssemble, hsymm]

/-- Positive-to-negative reflection really reads back the originating positive field. -/
theorem su2_reflected_positive_field_readback
    (n : ℕ) [NeZero n]
    (positive : SU2PositiveInteriorLinks n)
    (p : SU2PositiveInteriorLinkIndex n) :
    su2PositiveFieldReflectedToNegative n positive
      ((su2PositiveNegativeLinkReflectionEquiv n) p) =
      if p.1.2 = su2TimeDirection then (positive p)⁻¹ else positive p := by
  unfold su2PositiveFieldReflectedToNegative
  simp

/--
Reflecting the literal reflected-pair assembly exchanges its two positive
interior fields and pointwise inverts the fixed temporal boundary field.
This is the same physical reflection used by the full Wilson density theorem.
-/
theorem su2_reflect_assembled_pair
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2EvenTimeReflectLinks
        (su2AssembleReflectedPair n left boundary right) =
      su2AssembleReflectedPair n right
        (su2BoundaryTemporalInvert boundary) left := by
  classical
  funext x direction
  let p : FourDimensionalLinkIndex (2 * n) := (x, direction)
  have hreflect := four_dimensional_even_time_reflect_links_flattened
    (su2AssembleReflectedPair n left boundary right) p
  change
    su2EvenTimeReflectLinks
        (su2AssembleReflectedPair n left boundary right) x direction =
      su2AssembleReflectedPair n right
        (su2BoundaryTemporalInvert boundary) left x direction
  rw [← show
      fourDimensionalFlattenLinks
        (su2EvenTimeReflectLinks
          (su2AssembleReflectedPair n left boundary right)) p =
      su2EvenTimeReflectLinks
        (su2AssembleReflectedPair n left boundary right) x direction by rfl]
  rw [hreflect]
  rcases su2_even_time_link_cut_exhaustive n p with hp | hn | hb
  · let pp : SU2PositiveInteriorLinkIndex n := ⟨p, hp⟩
    let qn : SU2NegativeInteriorLinkIndex n :=
      (su2PositiveNegativeLinkReflectionEquiv n) pp
    have hq : qn.1 = fourDimensionalEvenTimeReflectLinkIndex p := rfl
    have hold :
        fourDimensionalFlattenLinks
          (su2AssembleReflectedPair n left boundary right)
          (fourDimensionalEvenTimeReflectLinkIndex p) =
        if direction = su2TimeDirection then (right pp)⁻¹ else right pp := by
      change su2LiteralSectorAssemble n
          (left, boundary, su2PositiveFieldReflectedToNegative n right)
          (fourDimensionalEvenTimeReflectLinkIndex p) = _
      rw [← hq, su2_literal_sector_assemble_negative]
      simpa [pp, p] using
        su2_reflected_positive_field_readback n right pp
    have hnew :
        su2AssembleReflectedPair n right
          (su2BoundaryTemporalInvert boundary) left x direction = right pp := by
      change su2LiteralSectorAssemble n
          (right, su2BoundaryTemporalInvert boundary,
            su2PositiveFieldReflectedToNegative n left) p = right pp
      simpa [pp] using
        su2_literal_sector_assemble_positive n
          (right, su2BoundaryTemporalInvert boundary,
            su2PositiveFieldReflectedToNegative n left) pp
    rw [hold, hnew]
    by_cases hTime : direction = su2TimeDirection
    · simp [hTime]
    · simp [hTime]
  · let pn : SU2NegativeInteriorLinkIndex n := ⟨p, hn⟩
    let qp : SU2PositiveInteriorLinkIndex n :=
      (su2PositiveNegativeLinkReflectionEquiv n).symm pn
    have hq : qp.1 = fourDimensionalEvenTimeReflectLinkIndex p := rfl
    have hold :
        fourDimensionalFlattenLinks
          (su2AssembleReflectedPair n left boundary right)
          (fourDimensionalEvenTimeReflectLinkIndex p) = left qp := by
      change su2LiteralSectorAssemble n
          (left, boundary, su2PositiveFieldReflectedToNegative n right)
          (fourDimensionalEvenTimeReflectLinkIndex p) = left qp
      rw [← hq, su2_literal_sector_assemble_positive]
    have hpn :
        su2PositiveFieldReflectedToNegative n left pn =
          if direction = su2TimeDirection then (left qp)⁻¹ else left qp := by
      unfold su2PositiveFieldReflectedToNegative
      change (if pn.1.2 = su2TimeDirection then
        (left ((su2PositiveNegativeLinkReflectionEquiv n).symm pn))⁻¹
        else left ((su2PositiveNegativeLinkReflectionEquiv n).symm pn)) = _
      rfl
    have hnew :
        su2AssembleReflectedPair n right
          (su2BoundaryTemporalInvert boundary) left x direction =
          su2PositiveFieldReflectedToNegative n left pn := by
      change su2LiteralSectorAssemble n
          (right, su2BoundaryTemporalInvert boundary,
            su2PositiveFieldReflectedToNegative n left) p = _
      simpa [pn] using
        su2_literal_sector_assemble_negative n
          (right, su2BoundaryTemporalInvert boundary,
            su2PositiveFieldReflectedToNegative n left) pn
    rw [hold, hnew, hpn]
  · let pb : SU2BoundaryTemporalLinkIndex n := ⟨p, hb⟩
    have htime : direction = su2TimeDirection := hb.1
    have hfix : fourDimensionalEvenTimeReflectLinkIndex p = p :=
      su2_boundary_temporal_link_index_fixed n p hb
    have hold :
        fourDimensionalFlattenLinks
          (su2AssembleReflectedPair n left boundary right)
          (fourDimensionalEvenTimeReflectLinkIndex p) = boundary pb := by
      change su2LiteralSectorAssemble n
          (left, boundary, su2PositiveFieldReflectedToNegative n right)
          (fourDimensionalEvenTimeReflectLinkIndex p) = boundary pb
      rw [hfix]
      simpa [pb] using
        su2_literal_sector_assemble_boundary n
          (left, boundary, su2PositiveFieldReflectedToNegative n right) pb
    have hnew :
        su2AssembleReflectedPair n right
          (su2BoundaryTemporalInvert boundary) left x direction =
          (boundary pb)⁻¹ := by
      change su2LiteralSectorAssemble n
          (right, su2BoundaryTemporalInvert boundary,
            su2PositiveFieldReflectedToNegative n left) p = _
      rw [show p = pb.1 by rfl,
        su2_literal_sector_assemble_boundary]
      rfl
    rw [hold, hnew]
    simp [htime]

end RequestProject.YangMills
