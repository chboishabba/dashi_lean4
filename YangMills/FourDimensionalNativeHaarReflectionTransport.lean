import Mathlib
import YangMills.FourDimensionalNativeHaarProductWeld
import YangMills.FourDimensionalFlatHaarReflectionIndex
import YangMills.FourDimensionalNativeHaarReflectionMaxCut

/-!
# Native finite-link Haar is preserved by the selected OS reflection

This file closes Block A's remaining measure-theoretic transport.

The proof is intentionally factored through the flat physical link index
`(x, μ)`.  On that carrier the reflection is exactly:

1. reindex by the finite involution `fourDimensionalEvenTimeReflectLinkIndex`;
2. invert precisely the temporal coordinates.

The flat product Haar law is invariant under (1) by finite-product reindexing
and under (2) by the nonabelian compact-Haar inversion theorem.  The existing
native/product same-object weld then transports the result back to the native
whole-link Haar measure.
-/

namespace RequestProject.YangMills

noncomputable def fourDimensionalFlatProductLinkHaar
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] :
    MeasureTheory.ProbabilityMeasure (FourDimensionalLinkIndex L → G) :=
  MeasureTheory.ProbabilityMeasure.pi
    (fun _ : FourDimensionalLinkIndex L => compactGroupNativeHaar G)

/-- The nested site/direction product is exactly the flat link-index product. -/
theorem four_dimensional_product_link_haar_map_flatten
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] :
    MeasureTheory.Measure.map (@fourDimensionalFlattenLinks G L)
      (((fourDimensionalProductLinkHaar G L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G L)) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G L)))
    =
      (((fourDimensionalFlatProductLinkHaar G L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex L → G)) :
        MeasureTheory.Measure (FourDimensionalLinkIndex L → G)) := by
  let μ : MeasureTheory.Measure G :=
    ((compactGroupNativeHaar G : MeasureTheory.ProbabilityMeasure G) :
      MeasureTheory.Measure G)
  have h := MeasureTheory.Measure.infinitePi_map_curry_symm
    (fun (_ : FourDimensionalTorusSite L) (_ : Fin 4) => μ)
  simpa [fourDimensionalFlattenLinks,
    MeasureTheory.Measure.infinitePi_eq_pi, μ] using h

/-- The inverse flattening map sends the flat product back to the nested one. -/
theorem four_dimensional_flat_product_link_haar_map_unflatten
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] :
    MeasureTheory.Measure.map (@fourDimensionalUnflattenLinks G L)
      (((fourDimensionalFlatProductLinkHaar G L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex L → G)) :
        MeasureTheory.Measure (FourDimensionalLinkIndex L → G)))
    =
      (((fourDimensionalProductLinkHaar G L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G L)) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G L)) := by
  let μ : MeasureTheory.Measure G :=
    ((compactGroupNativeHaar G : MeasureTheory.ProbabilityMeasure G) :
      MeasureTheory.Measure G)
  have h := MeasureTheory.Measure.infinitePi_map_curry
    (fun (_ : FourDimensionalTorusSite L) (_ : Fin 4) => μ)
  simpa [fourDimensionalUnflattenLinks,
    MeasureTheory.Measure.infinitePi_eq_pi, μ] using h

/-- Reindex a flat link field by the exact physical link-index involution. -/
def fourDimensionalFlatReflectReindex
    {G : Type*} {n : ℕ}
    (links : FourDimensionalLinkIndex (2 * n) → G) :
    FourDimensionalLinkIndex (2 * n) → G :=
  (MeasurableEquiv.piCongrLeft
    (fun _ : FourDimensionalLinkIndex (2 * n) => G)
    (fourDimensionalEvenTimeReflectLinkIndexEquiv n)) links

theorem four_dimensional_flat_reflect_reindex_apply
    {G : Type*} {n : ℕ}
    (links : FourDimensionalLinkIndex (2 * n) → G)
    (p : FourDimensionalLinkIndex (2 * n)) :
    fourDimensionalFlatReflectReindex links p =
      links (fourDimensionalEvenTimeReflectLinkIndex p) := by
  rfl

/-- Invert exactly the temporal coordinates of a flat link field. -/
def fourDimensionalFlatTemporalInvert
    {G : Type*} [Group G] {L : ℕ}
    (links : FourDimensionalLinkIndex L → G) :
    FourDimensionalLinkIndex L → G :=
  fun p => if p.2 = su2TimeDirection then (links p)⁻¹ else links p

/-- Flat physical reflection = reindex, then temporal inversion. -/
def fourDimensionalFlatEvenTimeReflectLinks
    {G : Type*} [Group G] {n : ℕ}
    (links : FourDimensionalLinkIndex (2 * n) → G) :
    FourDimensionalLinkIndex (2 * n) → G :=
  fourDimensionalFlatTemporalInvert
    (fourDimensionalFlatReflectReindex links)

theorem four_dimensional_flat_reflection_same_object
    {G : Type*} [Group G] {n : ℕ}
    (links : FourDimensionalGroupLinks G (2 * n)) :
    fourDimensionalUnflattenLinks
      (fourDimensionalFlatEvenTimeReflectLinks
        (fourDimensionalFlattenLinks links))
    = fourDimensionalEvenTimeReflectLinks links := by
  funext x direction
  have h := four_dimensional_even_time_reflect_links_flattened
    links (x, direction)
  simpa [fourDimensionalUnflattenLinks,
    fourDimensionalFlatEvenTimeReflectLinks,
    fourDimensionalFlatTemporalInvert,
    fourDimensionalFlatReflectReindex,
    four_dimensional_flat_reflect_reindex_apply] using h.symm

/-- Homogeneous flat product Haar is invariant under the finite link-index reindexing. -/
theorem four_dimensional_flat_product_haar_reindex_invariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@fourDimensionalFlatReflectReindex G n)
      (((fourDimensionalFlatProductLinkHaar G (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → G)) :
        MeasureTheory.Measure (FourDimensionalLinkIndex (2 * n) → G)))
    =
      (((fourDimensionalFlatProductLinkHaar G (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → G)) :
        MeasureTheory.Measure (FourDimensionalLinkIndex (2 * n) → G)) := by
  letI : NeZero (2 * n) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  let μ : MeasureTheory.Measure G :=
    ((compactGroupNativeHaar G : MeasureTheory.ProbabilityMeasure G) :
      MeasureTheory.Measure G)
  simpa [fourDimensionalFlatProductLinkHaar,
    fourDimensionalFlatReflectReindex, μ] using
    (MeasureTheory.Measure.pi_map_piCongrLeft
      (fourDimensionalEvenTimeReflectLinkIndexEquiv n)
      (fun _ : FourDimensionalLinkIndex (2 * n) => μ))

/-- Homogeneous flat product Haar is invariant under temporal-coordinate inversion. -/
theorem four_dimensional_flat_product_haar_temporal_invert_invariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (L : ℕ) [NeZero L] :
    MeasureTheory.Measure.map
      (@fourDimensionalFlatTemporalInvert G _ L)
      (((fourDimensionalFlatProductLinkHaar G L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex L → G)) :
        MeasureTheory.Measure (FourDimensionalLinkIndex L → G)))
    =
      (((fourDimensionalFlatProductLinkHaar G L :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex L → G)) :
        MeasureTheory.Measure (FourDimensionalLinkIndex L → G)) := by
  let μ : MeasureTheory.Measure G :=
    ((compactGroupNativeHaar G : MeasureTheory.ProbabilityMeasure G) :
      MeasureTheory.Measure G)
  change MeasureTheory.Measure.map
      (fun links p => if p.2 = su2TimeDirection then (links p)⁻¹ else links p)
      (MeasureTheory.Measure.pi
        (fun _ : FourDimensionalLinkIndex L => μ))
    = MeasureTheory.Measure.pi
        (fun _ : FourDimensionalLinkIndex L => μ)
  rw [MeasureTheory.Measure.pi_map_pi]
  · congr with p
    by_cases hTime : p.2 = su2TimeDirection
    · simpa [hTime, μ] using
        (compact_group_native_haar_inversion_invariant G)
    · simp [hTime, μ]
  · intro p
    by_cases hTime : p.2 = su2TimeDirection
    · simpa [hTime] using (measurable_inv : Measurable fun x : G => x⁻¹).aemeasurable
    · simpa [hTime] using (measurable_id : Measurable fun x : G => x).aemeasurable

/-- The complete flat physical reflection preserves flat product Haar. -/
theorem four_dimensional_flat_product_haar_reflection_invariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@fourDimensionalFlatEvenTimeReflectLinks G _ n)
      (((fourDimensionalFlatProductLinkHaar G (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → G)) :
        MeasureTheory.Measure (FourDimensionalLinkIndex (2 * n) → G)))
    =
      (((fourDimensionalFlatProductLinkHaar G (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalLinkIndex (2 * n) → G)) :
        MeasureTheory.Measure (FourDimensionalLinkIndex (2 * n) → G)) := by
  letI : NeZero (2 * n) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  rw [show (@fourDimensionalFlatEvenTimeReflectLinks G _ n) =
      (@fourDimensionalFlatTemporalInvert G _ (2 * n)) ∘
        (@fourDimensionalFlatReflectReindex G n) by rfl]
  rw [MeasureTheory.Measure.map_map]
  · rw [four_dimensional_flat_product_haar_reindex_invariant G n]
    exact four_dimensional_flat_product_haar_temporal_invert_invariant G (2 * n)
  · fun_prop
  · fun_prop

/-- The selected reflection preserves the explicit nested finite product Haar law. -/
theorem four_dimensional_product_link_haar_reflection_invariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (@fourDimensionalEvenTimeReflectLinks G _ n)
      (((fourDimensionalProductLinkHaar G (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G (2 * n))) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G (2 * n))))
    =
      (((fourDimensionalProductLinkHaar G (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G (2 * n))) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G (2 * n))) := by
  letI : NeZero (2 * n) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  let nested : MeasureTheory.Measure (FourDimensionalGroupLinks G (2 * n)) :=
    ((fourDimensionalProductLinkHaar G (2 * n) :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G (2 * n))) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G (2 * n)))
  let flat : MeasureTheory.Measure (FourDimensionalLinkIndex (2 * n) → G) :=
    ((fourDimensionalFlatProductLinkHaar G (2 * n) :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalLinkIndex (2 * n) → G)) :
      MeasureTheory.Measure (FourDimensionalLinkIndex (2 * n) → G))
  have hFlatten : MeasureTheory.Measure.map
      (@fourDimensionalFlattenLinks G (2 * n)) nested = flat := by
    simpa [nested, flat] using
      four_dimensional_product_link_haar_map_flatten G (2 * n)
  have hUnflatten : MeasureTheory.Measure.map
      (@fourDimensionalUnflattenLinks G (2 * n)) flat = nested := by
    simpa [nested, flat] using
      four_dimensional_flat_product_link_haar_map_unflatten G (2 * n)
  have hFlat : MeasureTheory.Measure.map
      (@fourDimensionalFlatEvenTimeReflectLinks G _ n) flat = flat := by
    simpa [flat] using
      four_dimensional_flat_product_haar_reflection_invariant G n
  calc
    MeasureTheory.Measure.map
        (@fourDimensionalEvenTimeReflectLinks G _ n) nested
      = MeasureTheory.Measure.map
          (@fourDimensionalUnflattenLinks G (2 * n))
          (MeasureTheory.Measure.map
            (@fourDimensionalFlatEvenTimeReflectLinks G _ n)
            (MeasureTheory.Measure.map
              (@fourDimensionalFlattenLinks G (2 * n)) nested)) := by
          rw [MeasureTheory.Measure.map_map, MeasureTheory.Measure.map_map]
          · congr 1
            funext links
            exact (four_dimensional_flat_reflection_same_object links).symm
          all_goals fun_prop
    _ = MeasureTheory.Measure.map
          (@fourDimensionalUnflattenLinks G (2 * n))
          (MeasureTheory.Measure.map
            (@fourDimensionalFlatEvenTimeReflectLinks G _ n) flat) := by
          rw [hFlatten]
    _ = MeasureTheory.Measure.map
          (@fourDimensionalUnflattenLinks G (2 * n)) flat := by
          rw [hFlat]
    _ = nested := hUnflatten

/--
Block A's Haar leaf is closed: the literal selected reflection preserves the
repository-native whole-link Haar law.
-/
theorem four_dimensional_native_haar_reflection_invariant_closed
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) [NeZero n] :
    FourDimensionalNativeHaarReflectionInvariant G n := by
  letI : NeZero (2 * n) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne n)⟩
  constructor
  · fun_prop
  · change MeasureTheory.Measure.map
      (@fourDimensionalEvenTimeReflectLinks G _ n)
      (((fourDimensionalNativeLinkHaar G (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G (2 * n))) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G (2 * n))))
      =
      (((fourDimensionalNativeLinkHaar G (2 * n) :
        MeasureTheory.ProbabilityMeasure
          (FourDimensionalGroupLinks G (2 * n))) :
        MeasureTheory.Measure (FourDimensionalGroupLinks G (2 * n)))
    rw [four_dimensional_native_haar_eq_product_haar_closed G (2 * n)]
    exact four_dimensional_product_link_haar_reflection_invariant G n

end RequestProject.YangMills
