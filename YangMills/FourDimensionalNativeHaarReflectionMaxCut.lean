import Mathlib
import YangMills.FourDimensionalCompactGroupHaar
import YangMills.LiteralSU2OrientedLinkReflection

/-!
# Generic compact-group owner for the literal even-time link reflection

The literal SU(2) reflection is not a group automorphism: temporal coordinates
are inverted, and inversion is anti-multiplicative in a nonabelian group.
Therefore Haar invariance must not be justified by the continuous-group-
automorphism theorem.

This file extracts exactly the source-independent geometry that *is* true for
every group on the same finite four-dimensional torus:

* spatial link coordinates are permuted by the site reflection;
* temporal link coordinates are permuted and inverted;
* the resulting full-link transformation is an involution;
* on SU(2), this generic transformation is definitionally the already-selected
  literal reflection.

Consequently the remaining finite-Haar theorem is precisely product-Haar
invariance under a finite coordinate permutation together with inversion on
the selected temporal coordinates.  For compact groups normalized Haar is
unimodular, so this is the correct analytic route; it is deliberately left as
the one measure-theoretic leaf rather than replaced by a false automorphism
argument.
-/

namespace RequestProject.YangMills

def fourDimensionalEvenTimeReflectLinks
    {G : Type*} [Group G] {n : ℕ}
    (links : FourDimensionalGroupLinks G (2 * n)) :
    FourDimensionalGroupLinks G (2 * n) :=
  fun x direction =>
    if h : direction = su2TimeDirection then
      (links
        (su2ShiftBackward
          (su2EvenTimeReflectSite x)
          su2TimeDirection)
        su2TimeDirection)⁻¹
    else
      links (su2EvenTimeReflectSite x) direction

theorem four_dimensional_even_time_reflect_links_spatial
    {G : Type*} [Group G] {n : ℕ}
    (links : FourDimensionalGroupLinks G (2 * n))
    (x : FourDimensionalTorusSite (2 * n))
    (direction : Fin 4)
    (hSpatial : direction ≠ su2TimeDirection) :
    fourDimensionalEvenTimeReflectLinks links x direction =
      links (su2EvenTimeReflectSite x) direction := by
  simp [fourDimensionalEvenTimeReflectLinks, hSpatial]

theorem four_dimensional_even_time_reflect_links_temporal
    {G : Type*} [Group G] {n : ℕ}
    (links : FourDimensionalGroupLinks G (2 * n))
    (x : FourDimensionalTorusSite (2 * n)) :
    fourDimensionalEvenTimeReflectLinks links x su2TimeDirection =
      (links
        (su2ShiftBackward
          (su2EvenTimeReflectSite x)
          su2TimeDirection)
        su2TimeDirection)⁻¹ := by
  simp [fourDimensionalEvenTimeReflectLinks]

theorem four_dimensional_even_time_reflect_links_involutive
    {G : Type*} [Group G] {n : ℕ}
    (links : FourDimensionalGroupLinks G (2 * n)) :
    fourDimensionalEvenTimeReflectLinks
      (fourDimensionalEvenTimeReflectLinks links) = links := by
  classical
  funext x direction
  by_cases hTime : direction = su2TimeDirection
  · subst direction
    simp only [four_dimensional_even_time_reflect_links_temporal]
    rw [su2_even_time_reflect_backward_time_shift]
    rw [su2_even_time_reflect_site_involutive]
    rw [su2_shift_backward_forward_cancel]
    simp
  · rw [four_dimensional_even_time_reflect_links_spatial _ _ _ hTime]
    rw [four_dimensional_even_time_reflect_links_spatial _ _ _ hTime]
    rw [su2_even_time_reflect_site_involutive]

/--
The selected literal SU(2) reflection is not a second map: after unfolding the
generic compact-group owner it is exactly the pre-existing orientation-
sensitive literal reflection.
-/
theorem su2_even_time_reflect_links_is_generic
    {n : ℕ} (links : SU2TorusLinks (2 * n)) :
    su2EvenTimeReflectLinks links =
      fourDimensionalEvenTimeReflectLinks links := by
  rfl

/--
Exact Block-A analytic leaf.

This proposition says that the explicit finite coordinate permutation plus
temporal inversion preserves the native normalized Haar law on the whole
finite link field.  The intended proof is product-Haar permutation invariance
plus inversion invariance of normalized Haar for compact groups.

It is intentionally a proposition, not an assumed field hidden in another
Yang--Mills data record.
-/
def FourDimensionalNativeHaarReflectionInvariant
    (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (n : ℕ) [NeZero n] : Prop :=
  MeasureTheory.MeasurePreserving
    (@fourDimensionalEvenTimeReflectLinks G _ n)
    (((fourDimensionalNativeLinkHaar G (2 * n) :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G (2 * n))) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G (2 * n))))
    (((fourDimensionalNativeLinkHaar G (2 * n) :
      MeasureTheory.ProbabilityMeasure
        (FourDimensionalGroupLinks G (2 * n))) :
      MeasureTheory.Measure (FourDimensionalGroupLinks G (2 * n))))

/--
The reflection is algebraically bijective before any measure theorem is used.
This is the finite-coordinate input needed by the product-Haar proof.
-/
theorem four_dimensional_even_time_reflection_bijective
    {G : Type*} [Group G] {n : ℕ} :
    Function.Bijective
      (@fourDimensionalEvenTimeReflectLinks G _ n) := by
  constructor
  · intro x y h
    have := congrArg
      (@fourDimensionalEvenTimeReflectLinks G _ n) h
    simpa [four_dimensional_even_time_reflect_links_involutive] using this
  · intro y
    refine ⟨fourDimensionalEvenTimeReflectLinks y, ?_⟩
    exact four_dimensional_even_time_reflect_links_involutive y

end RequestProject.YangMills
