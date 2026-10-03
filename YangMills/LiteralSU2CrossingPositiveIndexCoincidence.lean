import Mathlib
import YangMills.LiteralSU2CrossingHalfPathGaugeReadback

/-!
# Crossing left/right positive edge indices coincide

For each upper or lower crossing plaquette, the negative spatial edge reflects
back to the same positive spatial edge already appearing on the opposite half
path.  Thus the boundary-gauge crossing kernel acts on one common positive-link
feature family rather than two independently indexed families.
-/

namespace RequestProject.YangMills

private theorem crossing_second_direction_spatial'
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2FourDimensionalPlaquettes (2 * n))
    (hTime : p.2.1 = su2TimeDirection) :
    p.2.2 ≠ su2TimeDirection := by
  simp only [su2FourDimensionalPlaquettes,
    Finset.mem_filter, Finset.mem_univ, true_and] at hp
  intro hSecond
  rw [hTime, hSecond] at hp
  exact (lt_irrefl _ hp)

/-- Upper crossing: reflected-right spatial edge is the same positive edge as the left one. -/
theorem su2_upper_crossing_positive_index_coincides
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2UpperCrossingRightPositiveIndex n p hp =
      su2UpperCrossingLeftPositiveIndex n p hp := by
  apply Subtype.ext
  simp only [su2UpperCrossingRightPositiveIndex,
    su2UpperCrossingLeftPositiveIndex,
    su2PositiveNegativeLinkReflectionEquiv]
  simp only [su2UpperCrossingPlaquettes, Finset.mem_filter] at hp
  have hTime := hp.2.1
  have hBase := hp.2.2
  have hSpatial := crossing_second_direction_spatial' n p hp.1 hTime
  rw [four_dimensional_even_time_reflect_link_index_spatial _ _ hSpatial]
  rw [hTime, su2_even_time_reflect_forward_time_shift]
  have hfix := su2_boundary_temporal_link_index_fixed_left n p.1 hBase
  rw [four_dimensional_even_time_reflect_link_index_temporal] at hfix
  have hsite :
      su2ShiftBackward (su2EvenTimeReflectSite p.1) su2TimeDirection = p.1 :=
    congrArg Prod.fst hfix
  rw [hsite]

/-- Lower crossing: reflected-right spatial edge is the same positive edge as the wrapped left one. -/
theorem su2_lower_crossing_positive_index_coincides
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2LowerCrossingRightPositiveIndex n p hp =
      su2LowerCrossingLeftPositiveIndex n p hp := by
  apply Subtype.ext
  simp only [su2LowerCrossingRightPositiveIndex,
    su2LowerCrossingLeftPositiveIndex,
    su2PositiveNegativeLinkReflectionEquiv]
  simp only [su2LowerCrossingPlaquettes, Finset.mem_filter] at hp
  have hTime := hp.2.1
  have hBase := hp.2.2
  have hSpatial := crossing_second_direction_spatial' n p hp.1 hTime
  rw [four_dimensional_even_time_reflect_link_index_spatial _ _ hSpatial]
  have hfix := su2_boundary_temporal_link_index_fixed_right n p.1 hBase
  rw [four_dimensional_even_time_reflect_link_index_temporal] at hfix
  have hback :
      su2ShiftBackward (su2EvenTimeReflectSite p.1) su2TimeDirection = p.1 :=
    congrArg Prod.fst hfix
  have hsite :
      su2EvenTimeReflectSite p.1 = su2Shift p.1 su2TimeDirection := by
    have h := congrArg (fun x => su2Shift x su2TimeDirection) hback
    simpa [su2_shift_backward_forward_cancel] using h
  rw [hsite, hTime]

end RequestProject.YangMills
