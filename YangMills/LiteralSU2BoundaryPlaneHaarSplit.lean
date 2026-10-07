import Mathlib
import Mathlib.MeasureTheory.Constructions.Pi
import YangMills.LiteralSU2LinkSectorHaarSplit

/-!
# Split the temporal reflection boundary into its two periodic slabs

For the even torus of period `2*n`, the selected OS cut has two temporal
boundary slabs:

* the ordinary slab starting at time `n-1`;
* the periodic wraparound slab starting at time `2*n-1`.

The existing boundary temporal link carrier is exactly the disjoint sum of
those two finite index sets.  Since its reference law is homogeneous product
Haar, the boundary Haar law is therefore the product of the two independent
slab Haar laws.

This is the measure-theoretic factorization needed by the gauge-projection RP
route.  No Wilson positivity is asserted here.
-/

namespace RequestProject.YangMills

abbrev SU2UpperBoundaryTemporalLinkIndex
    (n : ℕ) [NeZero n] :=
  { p : SU2BoundaryTemporalLinkIndex n //
      (p.1.1 su2TimeDirection).val = n - 1 }

abbrev SU2LowerBoundaryTemporalLinkIndex
    (n : ℕ) [NeZero n] :=
  { p : SU2BoundaryTemporalLinkIndex n //
      (p.1.1 su2TimeDirection).val = 2 * n - 1 }

/-- The selected temporal boundary index is exactly the sum of its two slabs. -/
def su2BoundaryTemporalPlaneEquiv
    (n : ℕ) [NeZero n] :
    SU2BoundaryTemporalLinkIndex n ≃
      SU2UpperBoundaryTemporalLinkIndex n ⊕
        SU2LowerBoundaryTemporalLinkIndex n := by
  classical
  refine
    { toFun := fun p =>
        if h : (p.1.1 su2TimeDirection).val = n - 1 then
          Sum.inl ⟨p, h⟩
        else
          Sum.inr ⟨p, ?_⟩
      invFun := fun q =>
        match q with
        | Sum.inl p => p.1
        | Sum.inr p => p.1
      left_inv := ?_
      right_inv := ?_ }
  · rcases p.2.2 with hUpper | hLower
    · exact False.elim (h hUpper)
    · exact hLower
  · intro p
    by_cases hUpper : (p.1.1 su2TimeDirection).val = n - 1
    · simp [hUpper]
    · simp [hUpper]
  · intro q
    rcases q with p | p
    · simp [p.2]
    · have hNotUpper :
          (p.1.1.1 su2TimeDirection).val ≠ n - 1 := by
        intro hUpper
        have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
        omega
      simp [hNotUpper]

abbrev SU2UpperBoundaryTemporalLinks
    (n : ℕ) [NeZero n] :=
  SU2UpperBoundaryTemporalLinkIndex n → SU2PlaquetteHolonomy

abbrev SU2LowerBoundaryTemporalLinks
    (n : ℕ) [NeZero n] :=
  SU2LowerBoundaryTemporalLinkIndex n → SU2PlaquetteHolonomy

abbrev SU2BoundaryPlaneFields
    (n : ℕ) [NeZero n] :=
  SU2UpperBoundaryTemporalLinks n × SU2LowerBoundaryTemporalLinks n

private noncomputable def literalBoundaryPlaneOneLinkHaar :
    MeasureTheory.Measure SU2PlaquetteHolonomy :=
  ((literalSU2OneLinkHaar :
    MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
    MeasureTheory.Measure SU2PlaquetteHolonomy)

noncomputable def literalSU2UpperBoundaryTemporalHaar
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure (SU2UpperBoundaryTemporalLinks n) :=
  MeasureTheory.Measure.pi
    (fun _ : SU2UpperBoundaryTemporalLinkIndex n =>
      literalBoundaryPlaneOneLinkHaar)

noncomputable def literalSU2LowerBoundaryTemporalHaar
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure (SU2LowerBoundaryTemporalLinks n) :=
  MeasureTheory.Measure.pi
    (fun _ : SU2LowerBoundaryTemporalLinkIndex n =>
      literalBoundaryPlaneOneLinkHaar)

/-- Independent Haar law on the two temporal reflection slabs. -/
noncomputable def literalSU2BoundaryPlaneHaar
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure (SU2BoundaryPlaneFields n) :=
  (literalSU2UpperBoundaryTemporalHaar n).prod
    (literalSU2LowerBoundaryTemporalHaar n)

/-- Reassemble the two slab fields into the existing temporal-boundary field. -/
def su2BoundaryTemporalPlaneAssemble
    (n : ℕ) [NeZero n] :
    SU2BoundaryPlaneFields n → SU2BoundaryTemporalLinks n :=
  fun fields p =>
    match su2BoundaryTemporalPlaneEquiv n p with
    | Sum.inl q => fields.1 q
    | Sum.inr q => fields.2 q

theorem su2_boundary_temporal_plane_assemble_measurable
    (n : ℕ) [NeZero n] :
    Measurable (su2BoundaryTemporalPlaneAssemble n) := by
  apply measurable_pi_lambda
  intro p
  unfold su2BoundaryTemporalPlaneAssemble
  split <;> fun_prop

/--
The two-plane product Haar pushes forward exactly to the previously selected
full temporal-boundary product Haar.  This is independence by product-measure
identity, not an assumption.
-/
theorem literal_su2_boundary_temporal_haar_plane_split
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (su2BoundaryTemporalPlaneAssemble n)
      (literalSU2BoundaryPlaneHaar n) =
      literalSU2BoundaryTemporalHaar n := by
  let μ : MeasureTheory.Measure SU2PlaquetteHolonomy :=
    literalBoundaryPlaneOneLinkHaar
  let U := SU2UpperBoundaryTemporalLinkIndex n
  let L := SU2LowerBoundaryTemporalLinkIndex n
  let B := SU2BoundaryTemporalLinkIndex n

  let join :
      (U → SU2PlaquetteHolonomy) × (L → SU2PlaquetteHolonomy) ≃ᵐ
        ((U ⊕ L) → SU2PlaquetteHolonomy) :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : U ⊕ L => SU2PlaquetteHolonomy)).symm
  let reindex :
      ((U ⊕ L) → SU2PlaquetteHolonomy) ≃ᵐ
        (B → SU2PlaquetteHolonomy) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : B => SU2PlaquetteHolonomy)
      (su2BoundaryTemporalPlaneEquiv n)

  have hJoin : MeasureTheory.MeasurePreserving join
      (literalSU2BoundaryPlaneHaar n)
      (MeasureTheory.Measure.pi (fun _ : U ⊕ L => μ)) := by
    simpa [join, U, L, μ,
      literalSU2BoundaryPlaneHaar,
      literalSU2UpperBoundaryTemporalHaar,
      literalSU2LowerBoundaryTemporalHaar,
      literalBoundaryPlaneOneLinkHaar] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
        (fun _ : U ⊕ L => μ))

  have hReindex : MeasureTheory.MeasurePreserving reindex
      (MeasureTheory.Measure.pi (fun _ : U ⊕ L => μ))
      (MeasureTheory.Measure.pi (fun _ : B => μ)) := by
    simpa [reindex, U, L, B] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : B => μ)
        (su2BoundaryTemporalPlaneEquiv n))

  have hAll := hReindex.comp hJoin
  have hfun :
      (fun fields : SU2BoundaryPlaneFields n =>
        reindex (join fields)) =
      su2BoundaryTemporalPlaneAssemble n := by
    funext fields p
    rfl
  rw [← hfun, ← hAll.map_eq]
  simp [literalSU2BoundaryTemporalHaar, μ,
    literalBoundaryPlaneOneLinkHaar]

end RequestProject.YangMills
