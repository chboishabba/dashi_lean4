import Mathlib
import YangMills.FourDimensionalFlatHaarReflectionIndex

/-!
# Literal link-half geometry for the even-time OS cut

The plaquette cut already uses the two site-time halves t<n and n<=t on the
period-2n torus, with temporal crossing slabs beginning at t=n-1 and t=2n-1.
This file puts the *link variables themselves* on exactly that same cut.

Spatial links are assigned to the half containing their base site. Temporal
links beginning on either crossing slab are boundary variables. All other
temporal links are assigned by their base site. The selected oriented-link
reflection exchanges the positive/negative interiors and fixes the two
boundary temporal index sets (the group value is subsequently inverted).
-/

namespace RequestProject.YangMills

def su2ReflectionBoundaryTemporalLink
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n)) : Prop :=
  p.2 = su2TimeDirection ∧
    ((p.1 su2TimeDirection).val = n - 1 ∨
     (p.1 su2TimeDirection).val = 2 * n - 1)

def su2PositiveInteriorLink
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n)) : Prop :=
  ¬ su2ReflectionBoundaryTemporalLink n p ∧
    (p.1 su2TimeDirection).val < n

def su2NegativeInteriorLink
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n)) : Prop :=
  ¬ su2ReflectionBoundaryTemporalLink n p ∧
    n ≤ (p.1 su2TimeDirection).val

theorem su2_even_time_link_cut_exhaustive
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n)) :
    su2PositiveInteriorLink n p ∨
      su2NegativeInteriorLink n p ∨
      su2ReflectionBoundaryTemporalLink n p := by
  by_cases hb : su2ReflectionBoundaryTemporalLink n p
  · exact Or.inr (Or.inr hb)
  · by_cases ht : (p.1 su2TimeDirection).val < n
    · exact Or.inl ⟨hb, ht⟩
    · exact Or.inr (Or.inl ⟨hb, Nat.le_of_not_gt ht⟩)

theorem su2_even_time_link_cut_pairwise_disjoint
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n)) :
    ¬ (su2PositiveInteriorLink n p ∧ su2NegativeInteriorLink n p) ∧
    ¬ (su2PositiveInteriorLink n p ∧ su2ReflectionBoundaryTemporalLink n p) ∧
    ¬ (su2NegativeInteriorLink n p ∧ su2ReflectionBoundaryTemporalLink n p) := by
  constructor
  · rintro ⟨hp, hn⟩
    exact (Nat.not_lt_of_ge hn.2) hp.2
  constructor
  · rintro ⟨hp, hb⟩
    exact hp.1 hb
  · rintro ⟨hn, hb⟩
    exact hn.1 hb

theorem su2_reflected_temporal_link_time_coordinate
    (n : ℕ) [NeZero n]
    (x : FourDimensionalTorusSite (2 * n)) :
    ((fourDimensionalEvenTimeReflectLinkIndex
      (x, su2TimeDirection)).1 su2TimeDirection)
      = -x su2TimeDirection - 2 := by
  rw [four_dimensional_even_time_reflect_link_index_temporal]
  simp [su2ShiftBackward, su2EvenTimeReflectSite]
  ring

theorem su2_reflected_spatial_link_time_coordinate
    (n : ℕ) [NeZero n]
    (x : FourDimensionalTorusSite (2 * n))
    (direction : Fin 4)
    (hSpatial : direction ≠ su2TimeDirection) :
    ((fourDimensionalEvenTimeReflectLinkIndex
      (x, direction)).1 su2TimeDirection)
      = -x su2TimeDirection - 1 := by
  rw [four_dimensional_even_time_reflect_link_index_spatial _ _ hSpatial]
  simp [su2EvenTimeReflectSite]

theorem su2_boundary_temporal_link_index_fixed_left
    (n : ℕ) [NeZero n]
    (x : FourDimensionalTorusSite (2 * n))
    (ht : (x su2TimeDirection).val = n - 1) :
    fourDimensionalEvenTimeReflectLinkIndex
      (x, su2TimeDirection) = (x, su2TimeDirection) := by
  rw [four_dimensional_even_time_reflect_link_index_temporal]
  apply Prod.ext
  · classical
    funext i
    by_cases hi : i = su2TimeDirection
    · subst i
      apply Fin.ext
      have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      simp [su2ShiftBackward, su2EvenTimeReflectSite, ht]
      omega
    · simp [su2ShiftBackward, su2EvenTimeReflectSite,
        Function.update_noteq hi]
  · rfl

theorem su2_boundary_temporal_link_index_fixed_right
    (n : ℕ) [NeZero n]
    (x : FourDimensionalTorusSite (2 * n))
    (ht : (x su2TimeDirection).val = 2 * n - 1) :
    fourDimensionalEvenTimeReflectLinkIndex
      (x, su2TimeDirection) = (x, su2TimeDirection) := by
  rw [four_dimensional_even_time_reflect_link_index_temporal]
  apply Prod.ext
  · classical
    funext i
    by_cases hi : i = su2TimeDirection
    · subst i
      apply Fin.ext
      have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
      simp [su2ShiftBackward, su2EvenTimeReflectSite, ht]
      omega
    · simp [su2ShiftBackward, su2EvenTimeReflectSite,
        Function.update_noteq hi]
  · rfl

theorem su2_boundary_temporal_link_index_fixed
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n))
    (hp : su2ReflectionBoundaryTemporalLink n p) :
    fourDimensionalEvenTimeReflectLinkIndex p = p := by
  rcases p with ⟨x, direction⟩
  rcases hp with ⟨hdir, ht | ht⟩
  · subst direction
    exact su2_boundary_temporal_link_index_fixed_left n x ht
  · subst direction
    exact su2_boundary_temporal_link_index_fixed_right n x ht

theorem su2_boundary_temporal_link_reflects_boundary
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n))
    (hp : su2ReflectionBoundaryTemporalLink n p) :
    su2ReflectionBoundaryTemporalLink n
      (fourDimensionalEvenTimeReflectLinkIndex p) := by
  rw [su2_boundary_temporal_link_index_fixed n p hp]
  exact hp

theorem su2_nonboundary_reflects_nonboundary
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n))
    (hp : ¬ su2ReflectionBoundaryTemporalLink n p) :
    ¬ su2ReflectionBoundaryTemporalLink n
      (fourDimensionalEvenTimeReflectLinkIndex p) := by
  intro hb
  have hfix := su2_boundary_temporal_link_index_fixed n _ hb
  have hinv := four_dimensional_even_time_reflect_link_index_involutive p
  apply hp
  rw [← hinv, hfix]
  exact hb

theorem su2_positive_interior_reflects_negative
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n))
    (hp : su2PositiveInteriorLink n p) :
    su2NegativeInteriorLink n
      (fourDimensionalEvenTimeReflectLinkIndex p) := by
  rcases p with ⟨x, direction⟩
  refine ⟨su2_nonboundary_reflects_nonboundary n (x, direction) hp.1, ?_⟩
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  by_cases hTime : direction = su2TimeDirection
  · subst direction
    have hNotBoundary := hp.1
    have hNotLastPositive : (x su2TimeDirection).val ≠ n - 1 := by
      intro h
      apply hNotBoundary
      exact ⟨rfl, Or.inl h⟩
    have htUpper : (x su2TimeDirection).val < n - 1 := by
      omega
    rw [su2_reflected_temporal_link_time_coordinate]
    have hval :
        ((-x su2TimeDirection - 2 : Fin (2 * n))).val =
          2 * n - 2 - (x su2TimeDirection).val := by
      omega
    rw [hval]
    omega
  · rw [su2_reflected_spatial_link_time_coordinate n x direction hTime]
    have hval :
        ((-x su2TimeDirection - 1 : Fin (2 * n))).val =
          2 * n - 1 - (x su2TimeDirection).val := by
      omega
    rw [hval]
    omega

theorem su2_negative_interior_reflects_positive
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n))
    (hp : su2NegativeInteriorLink n p) :
    su2PositiveInteriorLink n
      (fourDimensionalEvenTimeReflectLinkIndex p) := by
  rcases p with ⟨x, direction⟩
  refine ⟨su2_nonboundary_reflects_nonboundary n (x, direction) hp.1, ?_⟩
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hlt : (x su2TimeDirection).val < 2 * n := (x su2TimeDirection).isLt
  by_cases hTime : direction = su2TimeDirection
  · subst direction
    have hNotBoundary := hp.1
    have hNotLast : (x su2TimeDirection).val ≠ 2 * n - 1 := by
      intro h
      apply hNotBoundary
      exact ⟨rfl, Or.inr h⟩
    have htUpper : (x su2TimeDirection).val ≤ 2 * n - 2 := by
      omega
    rw [su2_reflected_temporal_link_time_coordinate]
    have hval :
        ((-x su2TimeDirection - 2 : Fin (2 * n))).val =
          2 * n - 2 - (x su2TimeDirection).val := by
      omega
    rw [hval]
    omega
  · rw [su2_reflected_spatial_link_time_coordinate n x direction hTime]
    have hval :
        ((-x su2TimeDirection - 1 : Fin (2 * n))).val =
          2 * n - 1 - (x su2TimeDirection).val := by
      omega
    rw [hval]
    omega

end RequestProject.YangMills
