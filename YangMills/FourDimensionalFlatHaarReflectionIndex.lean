import Mathlib
import YangMills.FourDimensionalNativeHaarProductWeld
import YangMills.FourDimensionalNativeHaarReflectionMaxCut

/-!
# Flattened finite-link reflection geometry for product Haar

The OS reflection acts on physical link coordinates p=(x,mu). Its source
coordinate depends on mu, so the correct product-measure proof uses the flat
finite link index.

On that index the reflection is exactly a finite coordinate involution followed
by identity on spatial coordinates and inversion on temporal coordinates.

This is the form consumed by finite-product measure reindexing and
coordinatewise Haar invariance. The file proves the exact index involution and
its same-object relation to the existing curried link reflection. It does not
pretend inversion is a nonabelian group automorphism.
-/

namespace RequestProject.YangMills

abbrev FourDimensionalLinkIndex (L : ℕ) :=
  FourDimensionalTorusSite L × Fin 4

def fourDimensionalEvenTimeReflectLinkIndex
    {n : ℕ} (p : FourDimensionalLinkIndex (2 * n)) :
    FourDimensionalLinkIndex (2 * n) :=
  if h : p.2 = su2TimeDirection then
    (su2ShiftBackward
      (su2EvenTimeReflectSite p.1)
      su2TimeDirection,
     su2TimeDirection)
  else
    (su2EvenTimeReflectSite p.1, p.2)

theorem four_dimensional_even_time_reflect_link_index_spatial
    {n : ℕ} (x : FourDimensionalTorusSite (2 * n))
    (direction : Fin 4)
    (hSpatial : direction ≠ su2TimeDirection) :
    fourDimensionalEvenTimeReflectLinkIndex (x, direction) =
      (su2EvenTimeReflectSite x, direction) := by
  simp [fourDimensionalEvenTimeReflectLinkIndex, hSpatial]

theorem four_dimensional_even_time_reflect_link_index_temporal
    {n : ℕ} (x : FourDimensionalTorusSite (2 * n)) :
    fourDimensionalEvenTimeReflectLinkIndex (x, su2TimeDirection) =
      (su2ShiftBackward
        (su2EvenTimeReflectSite x)
        su2TimeDirection,
       su2TimeDirection) := by
  simp [fourDimensionalEvenTimeReflectLinkIndex]

theorem four_dimensional_even_time_reflect_link_index_involutive
    {n : ℕ} (p : FourDimensionalLinkIndex (2 * n)) :
    fourDimensionalEvenTimeReflectLinkIndex
      (fourDimensionalEvenTimeReflectLinkIndex p) = p := by
  rcases p with ⟨x, direction⟩
  by_cases hTime : direction = su2TimeDirection
  · subst direction
    rw [four_dimensional_even_time_reflect_link_index_temporal]
    rw [four_dimensional_even_time_reflect_link_index_temporal]
    simp only [Prod.mk.injEq, and_true]
    rw [su2_even_time_reflect_backward_time_shift]
    rw [su2_even_time_reflect_site_involutive]
    exact su2_shift_backward_forward_cancel _ _
  · rw [four_dimensional_even_time_reflect_link_index_spatial _ _ hTime]
    rw [four_dimensional_even_time_reflect_link_index_spatial _ _ hTime]
    rw [su2_even_time_reflect_site_involutive]

def fourDimensionalEvenTimeReflectLinkIndexEquiv
    (n : ℕ) :
    FourDimensionalLinkIndex (2 * n) ≃
      FourDimensionalLinkIndex (2 * n) where
  toFun := fourDimensionalEvenTimeReflectLinkIndex
  invFun := fourDimensionalEvenTimeReflectLinkIndex
  left_inv := four_dimensional_even_time_reflect_link_index_involutive
  right_inv := four_dimensional_even_time_reflect_link_index_involutive

def fourDimensionalFlattenLinks
    {G : Type*} {L : ℕ}
    (links : FourDimensionalGroupLinks G L) :
    FourDimensionalLinkIndex L → G :=
  fun p => links p.1 p.2

def fourDimensionalUnflattenLinks
    {G : Type*} {L : ℕ}
    (links : FourDimensionalLinkIndex L → G) :
    FourDimensionalGroupLinks G L :=
  fun x direction => links (x, direction)

theorem four_dimensional_unflatten_flatten
    {G : Type*} {L : ℕ}
    (links : FourDimensionalGroupLinks G L) :
    fourDimensionalUnflattenLinks
      (fourDimensionalFlattenLinks links) = links := by
  rfl

theorem four_dimensional_flatten_unflatten
    {G : Type*} {L : ℕ}
    (links : FourDimensionalLinkIndex L → G) :
    fourDimensionalFlattenLinks
      (fourDimensionalUnflattenLinks links) = links := by
  rfl

/--
The actual generic link reflection is exactly flat-index reindexing followed by
temporal inversion.
-/
theorem four_dimensional_even_time_reflect_links_flattened
    {G : Type*} [Group G] {n : ℕ}
    (links : FourDimensionalGroupLinks G (2 * n))
    (p : FourDimensionalLinkIndex (2 * n)) :
    fourDimensionalFlattenLinks
      (fourDimensionalEvenTimeReflectLinks links) p =
      if p.2 = su2TimeDirection then
        (fourDimensionalFlattenLinks links
          (fourDimensionalEvenTimeReflectLinkIndex p))⁻¹
      else
        fourDimensionalFlattenLinks links
          (fourDimensionalEvenTimeReflectLinkIndex p) := by
  rcases p with ⟨x, direction⟩
  by_cases hTime : direction = su2TimeDirection
  · subst direction
    simp [fourDimensionalFlattenLinks,
      fourDimensionalEvenTimeReflectLinks,
      fourDimensionalEvenTimeReflectLinkIndex]
  · simp [fourDimensionalFlattenLinks,
      fourDimensionalEvenTimeReflectLinks,
      fourDimensionalEvenTimeReflectLinkIndex,
      hTime]

/--
Exact one-link inversion leaf needed by the flattened product-Haar proof.
For normalized Haar on a compact group this follows from bi-invariance /
unimodularity. Keeping the proposition explicit prevents importing the
abelian-only inversion instance.
-/
def CompactGroupNormalizedHaarInversionInvariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] : Prop :=
  MeasureTheory.Measure.map (fun x : G => x⁻¹)
    (((compactGroupNativeHaar G :
      MeasureTheory.ProbabilityMeasure G) :
      MeasureTheory.Measure G))
  =
    (((compactGroupNativeHaar G :
      MeasureTheory.ProbabilityMeasure G) :
      MeasureTheory.Measure G))

end RequestProject.YangMills
