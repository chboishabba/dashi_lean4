import Mathlib
import YangMills.LiteralSU2CompactQuaternionHaar
import YangMills.FourDimensionalNativeHaarReflectionTransport

/-!
# Literal SU(2) link-product Haar and selected reflection invariance

This file attaches the one-link Haar measure from
`LiteralSU2CompactQuaternionHaar` directly to the exact link carrier used by
the literal Wilson action.  No topological-group instance is imposed on the
old coordinate carrier itself: the one-link law has already been transported
from the compact unit-quaternion group, and the finite lattice law is its
literal product.

The selected OS reflection is then handled exactly as in the generic compact-
group proof: flatten the physical link index, reindex by the finite reflection
involution, and invert only temporal coordinates.  Reindexing preserves the
homogeneous product, and temporal inversion uses the literal one-link Haar
inversion theorem.
-/

namespace RequestProject.YangMills

/-- Actual normalized product Haar on the literal four-dimensional SU(2) links. -/
noncomputable def literalSU2LinkHaar
    (L : ℕ) [NeZero L] :
    MeasureTheory.ProbabilityMeasure (SU2TorusLinks L) :=
  MeasureTheory.ProbabilityMeasure.pi
    (fun _ : SU2TorusSite L =>
      MeasureTheory.ProbabilityMeasure.pi
        (fun _ : Fin 4 => literalSU2OneLinkHaar))

/-- The same homogeneous product law on the flattened physical link index. -/
noncomputable def literalSU2FlatLinkHaar
    (L : ℕ) [NeZero L] :
    MeasureTheory.ProbabilityMeasure
      (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy) :=
  MeasureTheory.ProbabilityMeasure.pi
    (fun _ : FourDimensionalLinkIndex L => literalSU2OneLinkHaar)

/-- Nested site/direction Haar pushes forward to the flat physical-link product. -/
theorem literal_su2_link_haar_map_flatten
    (L : ℕ) [NeZero L] :
    MeasureTheory.Measure.map
      (@fourDimensionalFlattenLinks SU2PlaquetteHolonomy L)
      (((literalSU2LinkHaar L :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L)))
    =
      (((literalSU2FlatLinkHaar L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy)) := by
  let μ : MeasureTheory.Measure SU2PlaquetteHolonomy :=
    ((literalSU2OneLinkHaar :
      MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
      MeasureTheory.Measure SU2PlaquetteHolonomy)
  have h := MeasureTheory.Measure.infinitePi_map_curry_symm
    (fun (_ : SU2TorusSite L) (_ : Fin 4) => μ)
  simpa [literalSU2LinkHaar, literalSU2FlatLinkHaar,
    fourDimensionalFlattenLinks,
    MeasureTheory.Measure.infinitePi_eq_pi, μ] using h

/-- Flat literal Haar pushes back to the nested link carrier. -/
theorem literal_su2_flat_link_haar_map_unflatten
    (L : ℕ) [NeZero L] :
    MeasureTheory.Measure.map
      (@fourDimensionalUnflattenLinks SU2PlaquetteHolonomy L)
      (((literalSU2FlatLinkHaar L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy))
    =
      (((literalSU2LinkHaar L :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L)) := by
  let μ : MeasureTheory.Measure SU2PlaquetteHolonomy :=
    ((literalSU2OneLinkHaar :
      MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
      MeasureTheory.Measure SU2PlaquetteHolonomy)
  have h := MeasureTheory.Measure.infinitePi_map_curry
    (fun (_ : SU2TorusSite L) (_ : Fin 4) => μ)
  simpa [literalSU2LinkHaar, literalSU2FlatLinkHaar,
    fourDimensionalUnflattenLinks,
    MeasureTheory.Measure.infinitePi_eq_pi, μ] using h

/-- Homogeneous literal flat Haar is invariant under the exact link-index reflection. -/
theorem literal_su2_flat_link_haar_reindex_invariant
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@fourDimensionalFlatReflectReindex SU2PlaquetteHolonomy n)
      (((literalSU2FlatLinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy))
    =
      (((literalSU2FlatLinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) := by
  letI : NeZero (2 * n) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  let μ : MeasureTheory.Measure SU2PlaquetteHolonomy :=
    ((literalSU2OneLinkHaar :
      MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
      MeasureTheory.Measure SU2PlaquetteHolonomy)
  simpa [literalSU2FlatLinkHaar,
    fourDimensionalFlatReflectReindex, μ] using
    (MeasureTheory.Measure.pi_map_piCongrLeft
      (fourDimensionalEvenTimeReflectLinkIndexEquiv n)
      (fun _ : FourDimensionalLinkIndex (2 * n) => μ))

/-- Temporal-coordinate inversion preserves literal flat product Haar. -/
theorem literal_su2_flat_link_haar_temporal_invert_invariant
    (L : ℕ) [NeZero L] :
    MeasureTheory.Measure.map
      (@fourDimensionalFlatTemporalInvert SU2PlaquetteHolonomy _ L)
      (((literalSU2FlatLinkHaar L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy))
    =
      (((literalSU2FlatLinkHaar L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex L → SU2PlaquetteHolonomy)) := by
  let μ : MeasureTheory.Measure SU2PlaquetteHolonomy :=
    ((literalSU2OneLinkHaar :
      MeasureTheory.ProbabilityMeasure SU2PlaquetteHolonomy) :
      MeasureTheory.Measure SU2PlaquetteHolonomy)
  change MeasureTheory.Measure.map
      (fun links p =>
        if p.2 = su2TimeDirection then (links p)⁻¹ else links p)
      (MeasureTheory.Measure.pi
        (fun _ : FourDimensionalLinkIndex L => μ))
    = MeasureTheory.Measure.pi
        (fun _ : FourDimensionalLinkIndex L => μ)
  rw [MeasureTheory.Measure.pi_map_pi]
  · congr with p
    by_cases hTime : p.2 = su2TimeDirection
    · simpa [hTime, μ] using
        literal_su2_one_link_haar_inversion_invariant
    · simp [hTime, μ]
  · intro p
    by_cases hTime : p.2 = su2TimeDirection
    · simpa [hTime] using literal_su2_inv_measurable.aemeasurable
    · simpa [hTime] using
        (measurable_id : Measurable fun x : SU2PlaquetteHolonomy => x).aemeasurable

/-- The complete flat selected reflection preserves literal flat Haar. -/
theorem literal_su2_flat_link_haar_reflection_invariant
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@fourDimensionalFlatEvenTimeReflectLinks SU2PlaquetteHolonomy _ n)
      (((literalSU2FlatLinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy))
    =
      (((literalSU2FlatLinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :
        MeasureTheory.Measure
          (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) := by
  letI : NeZero (2 * n) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  rw [show
      (@fourDimensionalFlatEvenTimeReflectLinks SU2PlaquetteHolonomy _ n) =
        (@fourDimensionalFlatTemporalInvert SU2PlaquetteHolonomy _ (2 * n)) ∘
          (@fourDimensionalFlatReflectReindex SU2PlaquetteHolonomy n) by rfl]
  rw [MeasureTheory.Measure.map_map]
  · rw [literal_su2_flat_link_haar_reindex_invariant n]
    exact literal_su2_flat_link_haar_temporal_invert_invariant (2 * n)
  · fun_prop
  · fun_prop

/--
The selected literal SU(2) link reflection preserves the ACTUAL product Haar
law built from the literal quaternion links used by the Wilson action.
-/
theorem literal_su2_link_haar_reflection_invariant
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@su2EvenTimeReflectLinks n)
      (((literalSU2LinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        MeasureTheory.Measure (SU2TorusLinks (2 * n))))
    =
      (((literalSU2LinkHaar (2 * n) :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
        MeasureTheory.Measure (SU2TorusLinks (2 * n))) := by
  letI : NeZero (2 * n) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  let nested : MeasureTheory.Measure (SU2TorusLinks (2 * n)) :=
    ((literalSU2LinkHaar (2 * n) :
      MeasureTheory.ProbabilityMeasure (SU2TorusLinks (2 * n))) :
      MeasureTheory.Measure (SU2TorusLinks (2 * n)))
  let flat : MeasureTheory.Measure
      (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy) :=
    ((literalSU2FlatLinkHaar (2 * n) :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy)) :
      MeasureTheory.Measure
        (FourDimensionalLinkIndex (2 * n) → SU2PlaquetteHolonomy))
  have hFlatten : MeasureTheory.Measure.map
      (@fourDimensionalFlattenLinks SU2PlaquetteHolonomy (2 * n)) nested = flat := by
    simpa [nested, flat] using literal_su2_link_haar_map_flatten (2 * n)
  have hUnflatten : MeasureTheory.Measure.map
      (@fourDimensionalUnflattenLinks SU2PlaquetteHolonomy (2 * n)) flat = nested := by
    simpa [nested, flat] using literal_su2_flat_link_haar_map_unflatten (2 * n)
  have hFlat : MeasureTheory.Measure.map
      (@fourDimensionalFlatEvenTimeReflectLinks SU2PlaquetteHolonomy _ n) flat = flat := by
    simpa [flat] using literal_su2_flat_link_haar_reflection_invariant n
  calc
    MeasureTheory.Measure.map (@su2EvenTimeReflectLinks n) nested
      = MeasureTheory.Measure.map
          (@fourDimensionalUnflattenLinks SU2PlaquetteHolonomy (2 * n))
          (MeasureTheory.Measure.map
            (@fourDimensionalFlatEvenTimeReflectLinks SU2PlaquetteHolonomy _ n)
            (MeasureTheory.Measure.map
              (@fourDimensionalFlattenLinks SU2PlaquetteHolonomy (2 * n)) nested)) := by
          rw [MeasureTheory.Measure.map_map, MeasureTheory.Measure.map_map]
          · congr 1
            funext links
            have hsame := four_dimensional_flat_reflection_same_object links
            rw [← su2_even_time_reflect_links_is_generic links]
            exact hsame.symm
          all_goals fun_prop
    _ = MeasureTheory.Measure.map
          (@fourDimensionalUnflattenLinks SU2PlaquetteHolonomy (2 * n))
          (MeasureTheory.Measure.map
            (@fourDimensionalFlatEvenTimeReflectLinks SU2PlaquetteHolonomy _ n) flat) := by
          rw [hFlatten]
    _ = MeasureTheory.Measure.map
          (@fourDimensionalUnflattenLinks SU2PlaquetteHolonomy (2 * n)) flat := by
          rw [hFlat]
    _ = nested := hUnflatten

end RequestProject.YangMills
