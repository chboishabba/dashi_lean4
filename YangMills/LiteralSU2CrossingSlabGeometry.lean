import Mathlib
import YangMills.LiteralSU2EvenTimeReflectionGeometry

/-!
# Split the literal crossing plaquettes into the two periodic reflection slabs

The selected even-time OS reflection has exactly two temporal crossing slabs:
plaquettes based at time `n-1`, and the periodic wraparound plaquettes based at
time `2*n-1`.  This file makes that split exact on the SAME physical
plaquette index used by the finite Wilson product.

It is the plaquette-side companion to `LiteralSU2BoundaryPlaneHaarSplit`.
No reflection-positivity theorem is asserted here.
-/

namespace RequestProject.YangMills

/-- Ordinary reflection slab, based at time `n-1`. -/
def su2UpperCrossingPlaquette
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n)) : Prop :=
  p.2.1 = su2TimeDirection ∧
    (p.1 su2TimeDirection).val = n - 1

/-- Periodic wraparound reflection slab, based at time `2*n-1`. -/
def su2LowerCrossingPlaquette
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n)) : Prop :=
  p.2.1 = su2TimeDirection ∧
    (p.1 su2TimeDirection).val = 2 * n - 1

def su2UpperCrossingPlaquettes
    (n : ℕ) [NeZero n] :
    Finset (SU2LiteralPlaquetteIndex (2 * n)) :=
  (su2FourDimensionalPlaquettes (2 * n)).filter
    (su2UpperCrossingPlaquette n)

def su2LowerCrossingPlaquettes
    (n : ℕ) [NeZero n] :
    Finset (SU2LiteralPlaquetteIndex (2 * n)) :=
  (su2FourDimensionalPlaquettes (2 * n)).filter
    (su2LowerCrossingPlaquette n)

/-- The selected crossing predicate is exactly the disjunction of the two slabs. -/
theorem su2_crossing_plaquette_iff_upper_or_lower
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n)) :
    su2EvenTimeCrossingPlaquette n p ↔
      su2UpperCrossingPlaquette n p ∨
      su2LowerCrossingPlaquette n p := by
  constructor
  · rintro ⟨hTime, hUpper | hLower⟩
    · exact Or.inl ⟨hTime, hUpper⟩
    · exact Or.inr ⟨hTime, hLower⟩
  · rintro (⟨hTime, hUpper⟩ | ⟨hTime, hLower⟩)
    · exact ⟨hTime, Or.inl hUpper⟩
    · exact ⟨hTime, Or.inr hLower⟩

/-- The two crossing slabs are disjoint. -/
theorem su2_crossing_slabs_disjoint
    (n : ℕ) [NeZero n] :
    Disjoint (su2UpperCrossingPlaquettes n)
      (su2LowerCrossingPlaquettes n) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro p hUpper hLower
  simp only [su2UpperCrossingPlaquettes,
    su2LowerCrossingPlaquettes, Finset.mem_filter] at hUpper hLower
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h₁ := hUpper.2.2
  have h₂ := hLower.2.2
  omega

/-- The two slab finsets partition the complete selected crossing set exactly. -/
theorem su2_crossing_slabs_partition
    (n : ℕ) [NeZero n] :
    su2UpperCrossingPlaquettes n ∪ su2LowerCrossingPlaquettes n =
      su2EvenTimeCrossingPlaquettes n := by
  classical
  ext p
  simp only [Finset.mem_union,
    su2UpperCrossingPlaquettes,
    su2LowerCrossingPlaquettes,
    su2EvenTimeCrossingPlaquettes,
    Finset.mem_filter]
  constructor
  · rintro (⟨hp, hu⟩ | ⟨hp, hl⟩)
    · exact ⟨hp,
        (su2_crossing_plaquette_iff_upper_or_lower n p).2 (Or.inl hu)⟩
    · exact ⟨hp,
        (su2_crossing_plaquette_iff_upper_or_lower n p).2 (Or.inr hl)⟩
  · rintro ⟨hp, hc⟩
    rcases (su2_crossing_plaquette_iff_upper_or_lower n p).1 hc with hu | hl
    · exact Or.inl ⟨hp, hu⟩
    · exact Or.inr ⟨hp, hl⟩

end RequestProject.YangMills
