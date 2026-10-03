import Mathlib
import YangMills.LiteralSU2CrossingSlabGeometry
import YangMills.LiteralSU2LinkHalfGeometry

/-!
# Exact OS-sector geometry of the four links in a crossing plaquette

For the upper crossing slab, the two-link half paths have the literal sector
pattern

  boundary · negative     versus     positive · boundary.

For the periodic lower slab the pattern is

  boundary · positive     versus     negative · boundary.

These are precisely the local configurations consumed by the already-proved
boundary-gauge trace identities.  This file proves the classification on the
actual link indices; no abstract crossing variables are introduced.
-/

namespace RequestProject.YangMills

private theorem upper_time_shift_value
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (ht : (x su2TimeDirection).val = n - 1) :
    ((su2Shift x su2TimeDirection) su2TimeDirection).val = n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hlt : n < 2 * n := by omega
  simp only [su2Shift, Function.update_same]
  rw [ZMod.val_add]
  simp [ht, Nat.sub_add_cancel hn, Nat.mod_eq_of_lt hlt]

private theorem lower_time_shift_value
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (ht : (x su2TimeDirection).val = 2 * n - 1) :
    ((su2Shift x su2TimeDirection) su2TimeDirection).val = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hpos : 1 ≤ 2 * n := by omega
  simp only [su2Shift, Function.update_same]
  rw [ZMod.val_add]
  simp [ht, Nat.sub_add_cancel hpos]

private theorem spatial_shift_preserves_time_value
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (direction : Fin 4)
    (hSpatial : direction ≠ su2TimeDirection) :
    ((su2Shift x direction) su2TimeDirection).val =
      (x su2TimeDirection).val := by
  simp [su2Shift, Function.update_noteq hSpatial]

private theorem crossing_second_direction_spatial
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2FourDimensionalPlaquettes (2 * n))
    (hTime : p.2.1 = su2TimeDirection) :
    p.2.2 ≠ su2TimeDirection := by
  simp only [su2FourDimensionalPlaquettes,
    Finset.mem_filter, Finset.mem_univ, true_and] at hp
  intro hSecond
  have : su2TimeDirection < su2TimeDirection := by
    simpa [hTime, hSecond] using hp
  exact (lt_irrefl _ this)

/-- Exact four-link sector pattern of an upper crossing plaquette. -/
theorem su2_upper_crossing_link_sector_geometry
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2ReflectionBoundaryTemporalLink n (p.1, p.2.1) ∧
    su2NegativeInteriorLink n (su2Shift p.1 p.2.1, p.2.2) ∧
    su2PositiveInteriorLink n (p.1, p.2.2) ∧
    su2ReflectionBoundaryTemporalLink n (su2Shift p.1 p.2.2, p.2.1) := by
  simp only [su2UpperCrossingPlaquettes, Finset.mem_filter] at hp
  have hPhysical := hp.1
  rcases hp.2 with ⟨hTime, hBase⟩
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hSpatial := crossing_second_direction_spatial n p hPhysical hTime
  have hSpatialShift :=
    spatial_shift_preserves_time_value n p.1 p.2.2 hSpatial
  have hTimeShift :
      ((su2Shift p.1 p.2.1) su2TimeDirection).val = n := by
    rw [hTime]
    exact upper_time_shift_value n p.1 hBase
  constructor
  · exact ⟨hTime, Or.inl hBase⟩
  constructor
  · refine ⟨?_, ?_⟩
    · intro hb
      exact hSpatial hb.1
    · exact hTimeShift.ge
  constructor
  · refine ⟨?_, ?_⟩
    · intro hb
      exact hSpatial hb.1
    · omega
  · refine ⟨hTime, Or.inl ?_⟩
    rw [hSpatialShift]
    exact hBase

/-- Exact four-link sector pattern of a periodic lower crossing plaquette. -/
theorem su2_lower_crossing_link_sector_geometry
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2ReflectionBoundaryTemporalLink n (p.1, p.2.1) ∧
    su2PositiveInteriorLink n (su2Shift p.1 p.2.1, p.2.2) ∧
    su2NegativeInteriorLink n (p.1, p.2.2) ∧
    su2ReflectionBoundaryTemporalLink n (su2Shift p.1 p.2.2, p.2.1) := by
  simp only [su2LowerCrossingPlaquettes, Finset.mem_filter] at hp
  have hPhysical := hp.1
  rcases hp.2 with ⟨hTime, hBase⟩
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hSpatial := crossing_second_direction_spatial n p hPhysical hTime
  have hSpatialShift :=
    spatial_shift_preserves_time_value n p.1 p.2.2 hSpatial
  have hTimeShift :
      ((su2Shift p.1 p.2.1) su2TimeDirection).val = 0 := by
    rw [hTime]
    exact lower_time_shift_value n p.1 hBase
  constructor
  · exact ⟨hTime, Or.inr hBase⟩
  constructor
  · refine ⟨?_, ?_⟩
    · intro hb
      exact hSpatial hb.1
    · rw [hTimeShift]
      exact hn
  constructor
  · refine ⟨?_, ?_⟩
    · intro hb
      exact hSpatial hb.1
    · omega
  · refine ⟨hTime, Or.inr ?_⟩
    rw [hSpatialShift]
    exact hBase

end RequestProject.YangMills
