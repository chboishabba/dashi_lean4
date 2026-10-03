import Mathlib
import YangMills.LiteralSU2BoundaryPlaneHaarSplit
import YangMills.LiteralSU2CrossingGaugeSumReadback

/-!
# Upper/lower boundary-plane locality of the crossing gauge sums

The complete crossing readback still names the assembled temporal-boundary
field.  This file proves that the upper crossing sum reads only the upper slab
field and the periodic lower crossing sum reads only the lower slab field.

This is the last measure-carrier seam before the final boundary-Haar positivity
calculation: after this theorem, the two crossing exponentials depend on
independent product-Haar coordinates literally, not just by interpretation.
-/

namespace RequestProject.YangMills

/-- Upper source boundary link, now typed in the upper slab itself. -/
def su2UpperCrossingSourceUpperBoundaryIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    SU2UpperBoundaryTemporalLinkIndex n := by
  refine ⟨su2UpperCrossingSourceBoundaryIndex n p hp, ?_⟩
  simp only [su2UpperCrossingPlaquettes, Finset.mem_filter] at hp
  exact hp.2.2

/-- Upper target boundary link, typed in the same upper slab. -/
def su2UpperCrossingTargetUpperBoundaryIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    SU2UpperBoundaryTemporalLinkIndex n := by
  refine ⟨su2UpperCrossingTargetBoundaryIndex n p hp, ?_⟩
  simp only [su2UpperCrossingPlaquettes, Finset.mem_filter] at hp
  have hSpatial : p.2.2 ≠ su2TimeDirection := by
    intro h
    have hlt := hp.1
    simp only [su2FourDimensionalPlaquettes, Finset.mem_filter,
      Finset.mem_univ, true_and] at hlt
    rw [hp.2.1, h] at hlt
    exact (lt_irrefl _ hlt)
  simp [su2UpperCrossingTargetBoundaryIndex,
    su2Shift, Function.update_noteq hSpatial, hp.2.2]

/-- Lower source boundary link, typed in the periodic lower slab. -/
def su2LowerCrossingSourceLowerBoundaryIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    SU2LowerBoundaryTemporalLinkIndex n := by
  refine ⟨su2LowerCrossingSourceBoundaryIndex n p hp, ?_⟩
  simp only [su2LowerCrossingPlaquettes, Finset.mem_filter] at hp
  exact hp.2.2

/-- Lower target boundary link, typed in the same periodic lower slab. -/
def su2LowerCrossingTargetLowerBoundaryIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    SU2LowerBoundaryTemporalLinkIndex n := by
  refine ⟨su2LowerCrossingTargetBoundaryIndex n p hp, ?_⟩
  simp only [su2LowerCrossingPlaquettes, Finset.mem_filter] at hp
  have hSpatial : p.2.2 ≠ su2TimeDirection := by
    intro h
    have hlt := hp.1
    simp only [su2FourDimensionalPlaquettes, Finset.mem_filter,
      Finset.mem_univ, true_and] at hlt
    rw [hp.2.1, h] at hlt
    exact (lt_irrefl _ hlt)
  simp [su2LowerCrossingTargetBoundaryIndex,
    su2Shift, Function.update_noteq hSpatial, hp.2.2]

/-- Assembling the two planes reads an upper source coordinate from the upper field. -/
theorem su2_boundary_plane_assemble_upper_source
    (n : ℕ) [NeZero n]
    (planes : SU2BoundaryPlaneFields n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2BoundaryTemporalPlaneAssemble n planes
        (su2UpperCrossingSourceBoundaryIndex n p hp) =
      planes.1 (su2UpperCrossingSourceUpperBoundaryIndex n p hp) := by
  unfold su2BoundaryTemporalPlaneAssemble su2BoundaryTemporalPlaneEquiv
  simp [su2UpperCrossingSourceUpperBoundaryIndex]

/-- Assembling the two planes reads an upper target coordinate from the upper field. -/
theorem su2_boundary_plane_assemble_upper_target
    (n : ℕ) [NeZero n]
    (planes : SU2BoundaryPlaneFields n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2BoundaryTemporalPlaneAssemble n planes
        (su2UpperCrossingTargetBoundaryIndex n p hp) =
      planes.1 (su2UpperCrossingTargetUpperBoundaryIndex n p hp) := by
  unfold su2BoundaryTemporalPlaneAssemble su2BoundaryTemporalPlaneEquiv
  simp [su2UpperCrossingTargetUpperBoundaryIndex]

/-- Assembling the two planes reads a lower source coordinate from the lower field. -/
theorem su2_boundary_plane_assemble_lower_source
    (n : ℕ) [NeZero n]
    (planes : SU2BoundaryPlaneFields n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2BoundaryTemporalPlaneAssemble n planes
        (su2LowerCrossingSourceBoundaryIndex n p hp) =
      planes.2 (su2LowerCrossingSourceLowerBoundaryIndex n p hp) := by
  unfold su2BoundaryTemporalPlaneAssemble su2BoundaryTemporalPlaneEquiv
  have hNotUpper :
      ((su2LowerCrossingSourceBoundaryIndex n p hp).1.1 su2TimeDirection).val ≠ n - 1 := by
    simp only [su2LowerCrossingPlaquettes, Finset.mem_filter] at hp
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    simp [su2LowerCrossingSourceBoundaryIndex, hp.2.2]
    omega
  simp [hNotUpper, su2LowerCrossingSourceLowerBoundaryIndex]

/-- Assembling the two planes reads a lower target coordinate from the lower field. -/
theorem su2_boundary_plane_assemble_lower_target
    (n : ℕ) [NeZero n]
    (planes : SU2BoundaryPlaneFields n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2BoundaryTemporalPlaneAssemble n planes
        (su2LowerCrossingTargetBoundaryIndex n p hp) =
      planes.2 (su2LowerCrossingTargetLowerBoundaryIndex n p hp) := by
  unfold su2BoundaryTemporalPlaneAssemble su2BoundaryTemporalPlaneEquiv
  have hNotUpper :
      ((su2LowerCrossingTargetBoundaryIndex n p hp).1.1 su2TimeDirection).val ≠ n - 1 := by
    have hLower := (su2LowerCrossingTargetLowerBoundaryIndex n p hp).2
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    intro hUpper
    omega
  simp [hNotUpper, su2LowerCrossingTargetLowerBoundaryIndex]

/-- Upper gauge sum written directly on the upper slab field. -/
def su2UpperPlaneGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (upper : SU2UpperBoundaryTemporalLinks n) : ℝ :=
  ∑ p ∈ (su2UpperCrossingPlaquettes n).attach,
    su2RelativeFundamentalTrace
      (right (su2UpperCrossingRightPositiveIndex n p.1 p.2))
      (su2BoundaryGaugeTransformEdge
        (upper (su2UpperCrossingSourceUpperBoundaryIndex n p.1 p.2))
        (upper (su2UpperCrossingTargetUpperBoundaryIndex n p.1 p.2))
        (left (su2UpperCrossingLeftPositiveIndex n p.1 p.2)))

/-- Lower gauge sum written directly on the periodic lower slab field. -/
def su2LowerPlaneGaugedCrossingTraceSum
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (lower : SU2LowerBoundaryTemporalLinks n) : ℝ :=
  ∑ p ∈ (su2LowerCrossingPlaquettes n).attach,
    su2RelativeFundamentalTrace
      (left (su2LowerCrossingLeftPositiveIndex n p.1 p.2))
      (su2BoundaryGaugeTransformEdge
        (lower (su2LowerCrossingSourceLowerBoundaryIndex n p.1 p.2))
        (lower (su2LowerCrossingTargetLowerBoundaryIndex n p.1 p.2))
        (right (su2LowerCrossingRightPositiveIndex n p.1 p.2)))

/-- Upper crossing dependence is literally local to the upper Haar slab. -/
theorem su2_upper_gauged_crossing_sum_plane_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (planes : SU2BoundaryPlaneFields n) :
    su2UpperGaugedCrossingTraceSum n left right
      (su2BoundaryTemporalPlaneAssemble n planes) =
    su2UpperPlaneGaugedCrossingTraceSum n left right planes.1 := by
  unfold su2UpperGaugedCrossingTraceSum su2UpperPlaneGaugedCrossingTraceSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [su2_boundary_plane_assemble_upper_source,
    su2_boundary_plane_assemble_upper_target]

/-- Lower crossing dependence is literally local to the lower Haar slab. -/
theorem su2_lower_gauged_crossing_sum_plane_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (planes : SU2BoundaryPlaneFields n) :
    su2LowerGaugedCrossingTraceSum n left right
      (su2BoundaryTemporalPlaneAssemble n planes) =
    su2LowerPlaneGaugedCrossingTraceSum n left right planes.2 := by
  unfold su2LowerGaugedCrossingTraceSum su2LowerPlaneGaugedCrossingTraceSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [su2_boundary_plane_assemble_lower_source,
    su2_boundary_plane_assemble_lower_target]

end RequestProject.YangMills
