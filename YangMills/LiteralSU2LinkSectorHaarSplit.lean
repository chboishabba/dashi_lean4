import Mathlib
import Mathlib.MeasureTheory.Constructions.Pi
import YangMills.LiteralSU2LinkSectorProductSplit
import YangMills.LiteralSU2LinkHaarReflection

/-!
# Literal product-Haar split into OS link sectors

The finite physical link index is already partitioned exactly into positive
interior, reflection-boundary temporal, and negative interior coordinates.
This file transports the literal product Haar through that exact finite index
partition and obtains the genuine three-factor product measure used by Fubini.

No independence assumption is introduced: independence is a theorem because
the reference law is the homogeneous finite product Haar.
-/

namespace RequestProject.YangMills

abbrev SU2PositiveInteriorLinks (n : ℕ) [NeZero n] :=
  SU2PositiveInteriorLinkIndex n → SU2PlaquetteHolonomy

abbrev SU2BoundaryTemporalLinks (n : ℕ) [NeZero n] :=
  SU2BoundaryTemporalLinkIndex n → SU2PlaquetteHolonomy

abbrev SU2NegativeInteriorLinks (n : ℕ) [NeZero n] :=
  SU2NegativeInteriorLinkIndex n → SU2PlaquetteHolonomy

abbrev SU2LinkSectorFields (n : ℕ) [NeZero n] :=
  SU2PositiveInteriorLinks n ×
    (SU2BoundaryTemporalLinks n × SU2NegativeInteriorLinks n)

private noncomputable def literalOneLinkHaarMeasure :
    MeasureTheory.Measure SU2PlaquetteHolonomy :=
  ((literalSU2OneLinkHaar :
    MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
    MeasureTheory.Measure SU2PlaquetteHolonomy)

noncomputable def literalSU2PositiveInteriorHaar
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure (SU2PositiveInteriorLinks n) :=
  MeasureTheory.Measure.pi
    (fun _ : SU2PositiveInteriorLinkIndex n => literalOneLinkHaarMeasure)

noncomputable def literalSU2BoundaryTemporalHaar
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure (SU2BoundaryTemporalLinks n) :=
  MeasureTheory.Measure.pi
    (fun _ : SU2BoundaryTemporalLinkIndex n => literalOneLinkHaarMeasure)

noncomputable def literalSU2NegativeInteriorHaar
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure (SU2NegativeInteriorLinks n) :=
  MeasureTheory.Measure.pi
    (fun _ : SU2NegativeInteriorLinkIndex n => literalOneLinkHaarMeasure)

/-- Genuine three-sector reference Haar law. -/
noncomputable def literalSU2LinkSectorHaar
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure (SU2LinkSectorFields n) :=
  (literalSU2PositiveInteriorHaar n).prod
    ((literalSU2BoundaryTemporalHaar n).prod
      (literalSU2NegativeInteriorHaar n))

/-- Assemble the three actual OS link sectors back into one flat physical link field. -/
def su2LiteralSectorAssemble
    (n : ℕ) [NeZero n] :
    SU2LinkSectorFields n →
      (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy) :=
  fun fields p =>
    match (su2LinkSectorSumEquiv n).symm p with
    | Sum.inl q => fields.1 q
    | Sum.inr (Sum.inl q) => fields.2.1 q
    | Sum.inr (Sum.inr q) => fields.2.2 q

/-- Sector assembly is measurable coordinatewise. -/
theorem su2_literal_sector_assemble_measurable
    (n : ℕ) [NeZero n] :
    Measurable (su2LiteralSectorAssemble n) := by
  apply measurable_pi_lambda
  intro p
  unfold su2LiteralSectorAssemble
  split
  · fun_prop
  · split <;> fun_prop

/--
The three-sector law maps exactly to the selected flat literal product Haar.
This is the finite Fubini/independence theorem required by Wilson OS2.
-/
theorem literal_su2_link_sector_haar_split
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (su2LiteralSectorAssemble n)
      (literalSU2LinkSectorHaar n)
    =
      (((literalSU2FlatLinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) := by
  letI : NeZero (2 * n) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  let μ : MeasureTheory.Measure SU2PlaquetteHolonomy := literalOneLinkHaarMeasure
  let P := SU2PositiveInteriorLinkIndex n
  let B := SU2BoundaryTemporalLinkIndex n
  let N := SU2NegativeInteriorLinkIndex n

  let inner :
      (B → SU2PlaquetteHolonomy) × (N → SU2PlaquetteHolonomy) ≃ᵐ
        ((B ⊕ N) → SU2PlaquetteHolonomy) :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : B ⊕ N => SU2PlaquetteHolonomy)).symm
  let outer :
      (P → SU2PlaquetteHolonomy) × ((B ⊕ N) → SU2PlaquetteHolonomy) ≃ᵐ
        ((P ⊕ (B ⊕ N)) → SU2PlaquetteHolonomy) :=
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : P ⊕ (B ⊕ N) => SU2PlaquetteHolonomy)).symm
  let reindex :
      ((P ⊕ (B ⊕ N)) → SU2PlaquetteHolonomy) ≃ᵐ
        (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : FourDimensionalLinkIndex (2 * n) => SU2PlaquetteHolonomy)
      (su2LinkSectorSumEquiv n)

  have hInner : MeasureTheory.MeasurePreserving inner
      ((literalSU2BoundaryTemporalHaar n).prod
        (literalSU2NegativeInteriorHaar n))
      (MeasureTheory.Measure.pi
        (fun _ : B ⊕ N => μ)) := by
    simpa [inner, B, N, μ,
      literalSU2BoundaryTemporalHaar,
      literalSU2NegativeInteriorHaar,
      literalOneLinkHaarMeasure] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
        (fun _ : B ⊕ N => μ))

  have hPosInner : MeasureTheory.MeasurePreserving
      (fun fields : SU2LinkSectorFields n => (fields.1, inner fields.2))
      (literalSU2LinkSectorHaar n)
      ((literalSU2PositiveInteriorHaar n).prod
        (MeasureTheory.Measure.pi (fun _ : B ⊕ N => μ))) := by
    exact MeasureTheory.MeasurePreserving.prod
      (MeasureTheory.MeasurePreserving.id (literalSU2PositiveInteriorHaar n))
      hInner

  have hOuter : MeasureTheory.MeasurePreserving outer
      ((literalSU2PositiveInteriorHaar n).prod
        (MeasureTheory.Measure.pi (fun _ : B ⊕ N => μ)))
      (MeasureTheory.Measure.pi
        (fun _ : P ⊕ (B ⊕ N) => μ)) := by
    simpa [outer, P, B, N, μ,
      literalSU2PositiveInteriorHaar,
      literalOneLinkHaarMeasure] using
      (MeasureTheory.measurePreserving_sumPiEquivProdPi_symm
        (fun _ : P ⊕ (B ⊕ N) => μ))

  have hReindex : MeasureTheory.MeasurePreserving reindex
      (MeasureTheory.Measure.pi
        (fun _ : P ⊕ (B ⊕ N) => μ))
      (MeasureTheory.Measure.pi
        (fun _ : FourDimensionalLinkIndex (2 * n) => μ)) := by
    simpa [reindex, P, B, N] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : FourDimensionalLinkIndex (2 * n) => μ)
        (su2LinkSectorSumEquiv n))

  have hAll := hReindex.comp (hOuter.comp hPosInner)
  have hfun :
      (fun fields : SU2LinkSectorFields n =>
        reindex (outer (fields.1, inner fields.2))) =
      su2LiteralSectorAssemble n := by
    funext fields p
    rfl
  rw [← hfun]
  rw [← hAll.map_eq]
  simp [literalSU2FlatLinkHaar, μ, literalOneLinkHaarMeasure]

end RequestProject.YangMills
