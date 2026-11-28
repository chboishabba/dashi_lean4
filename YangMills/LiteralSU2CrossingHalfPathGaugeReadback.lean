import Mathlib
import YangMills.LiteralSU2BoundaryGaugeCrossingAlgebra
import YangMills.LiteralSU2BoundaryGaugeProjectionSymmetry
import YangMills.LiteralSU2CrossingHalfPathSectorGeometry

/-!
# Literal crossing half-path gauge readback

This file performs the local same-object calculation left in Block A.  The
four links of each actual crossing plaquette were classified by OS sector in
`LiteralSU2CrossingHalfPathSectorGeometry`.  Reading those links through the
literal sector assembly gives the two physical half paths in the exact forms
used by the boundary-gauge trace lemmas.

Upper slab:

  first  = b_source * rightEdge
  second = leftEdge * b_target.

Lower periodic slab:

  first  = b_source * leftEdge
  second = rightEdge * b_target.

Consequently each literal crossing trace is exactly an ordinary relative-trace
kernel with a boundary gauge transform on one positive copy.
-/

namespace RequestProject.YangMills

private theorem upper_crossing_second_spatial
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    p.2.2 ≠ su2TimeDirection := by
  simp only [su2UpperCrossingPlaquettes, Finset.mem_filter,
    su2FourDimensionalPlaquettes, Finset.mem_univ, true_and] at hp
  intro h
  have hlt := hp.1
  rw [hp.2.1, h] at hlt
  exact (lt_irrefl _ hlt)

private theorem lower_crossing_second_spatial
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    p.2.2 ≠ su2TimeDirection := by
  simp only [su2LowerCrossingPlaquettes, Finset.mem_filter,
    su2FourDimensionalPlaquettes, Finset.mem_univ, true_and] at hp
  intro h
  have hlt := hp.1
  rw [hp.2.1, h] at hlt
  exact (lt_irrefl _ hlt)

/-- Source boundary link of an upper crossing plaquette. -/
def su2UpperCrossingSourceBoundaryIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    SU2BoundaryTemporalLinkIndex n :=
  ⟨(p.1, p.2.1),
    (su2_upper_crossing_link_sector_geometry n p hp).1⟩

/-- Target boundary link of an upper crossing plaquette. -/
def su2UpperCrossingTargetBoundaryIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    SU2BoundaryTemporalLinkIndex n :=
  ⟨(su2Shift p.1 p.2.2, p.2.1),
    (su2_upper_crossing_link_sector_geometry n p hp).2.2.2⟩

/-- Positive left-copy spatial edge in an upper crossing plaquette. -/
def su2UpperCrossingLeftPositiveIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    SU2PositiveInteriorLinkIndex n :=
  ⟨(p.1, p.2.2),
    (su2_upper_crossing_link_sector_geometry n p hp).2.2.1⟩

/-- Positive-copy preimage of the negative spatial edge in the upper slab. -/
def su2UpperCrossingRightPositiveIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    SU2PositiveInteriorLinkIndex n :=
  (su2PositiveNegativeLinkReflectionEquiv n).symm
    ⟨(su2Shift p.1 p.2.1, p.2.2),
      (su2_upper_crossing_link_sector_geometry n p hp).2.1⟩

/-- Source boundary link of a lower crossing plaquette. -/
def su2LowerCrossingSourceBoundaryIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    SU2BoundaryTemporalLinkIndex n :=
  ⟨(p.1, p.2.1),
    (su2_lower_crossing_link_sector_geometry n p hp).1⟩

/-- Target boundary link of a lower crossing plaquette. -/
def su2LowerCrossingTargetBoundaryIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    SU2BoundaryTemporalLinkIndex n :=
  ⟨(su2Shift p.1 p.2.2, p.2.1),
    (su2_lower_crossing_link_sector_geometry n p hp).2.2.2⟩

/-- Positive left-copy spatial edge after wrapping across the lower slab. -/
def su2LowerCrossingLeftPositiveIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    SU2PositiveInteriorLinkIndex n :=
  ⟨(su2Shift p.1 p.2.1, p.2.2),
    (su2_lower_crossing_link_sector_geometry n p hp).2.1⟩

/-- Positive-copy preimage of the negative spatial edge in the lower slab. -/
def su2LowerCrossingRightPositiveIndex
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    SU2PositiveInteriorLinkIndex n :=
  (su2PositiveNegativeLinkReflectionEquiv n).symm
    ⟨(p.1, p.2.2),
      (su2_lower_crossing_link_sector_geometry n p hp).2.2.1⟩

/-- Literal upper first half path reads as boundary times right-copy edge. -/
theorem su2_upper_crossing_first_half_path_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right) p =
      boundary (su2UpperCrossingSourceBoundaryIndex n p hp) *
        right (su2UpperCrossingRightPositiveIndex n p hp) := by
  let qn : SU2NegativeInteriorLinkIndex n :=
    ⟨(su2Shift p.1 p.2.1, p.2.2),
      (su2_upper_crossing_link_sector_geometry n p hp).2.1⟩
  have hSpatial := upper_crossing_second_spatial n p hp
  unfold su2LiteralCrossingFirstBoundary su2PlaquetteFirstHalfPath
  change
    su2LiteralSectorAssemble n
        (left, boundary, su2PositiveFieldReflectedToNegative n right)
        (p.1, p.2.1) *
      su2LiteralSectorAssemble n
        (left, boundary, su2PositiveFieldReflectedToNegative n right)
        (su2Shift p.1 p.2.1, p.2.2) = _
  rw [show (p.1, p.2.1) =
      (su2UpperCrossingSourceBoundaryIndex n p hp).1 by rfl,
    su2_literal_sector_assemble_boundary,
    show (su2Shift p.1 p.2.1, p.2.2) = qn.1 by rfl,
    su2_literal_sector_assemble_negative]
  unfold su2PositiveFieldReflectedToNegative
  change boundary _ *
      (if qn.1.2 = su2TimeDirection then
        (right ((su2PositiveNegativeLinkReflectionEquiv n).symm qn))⁻¹
       else right ((su2PositiveNegativeLinkReflectionEquiv n).symm qn)) = _
  rw [if_neg hSpatial]
  rfl

/-- Literal upper second half path reads as left-copy edge times boundary. -/
theorem su2_upper_crossing_second_half_path_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right) p =
      left (su2UpperCrossingLeftPositiveIndex n p hp) *
        boundary (su2UpperCrossingTargetBoundaryIndex n p hp) := by
  unfold su2LiteralCrossingSecondBoundary su2PlaquetteSecondHalfPath
  change
    su2LiteralSectorAssemble n
        (left, boundary, su2PositiveFieldReflectedToNegative n right)
        (p.1, p.2.2) *
      su2LiteralSectorAssemble n
        (left, boundary, su2PositiveFieldReflectedToNegative n right)
        (su2Shift p.1 p.2.2, p.2.1) = _
  rw [show (p.1, p.2.2) =
      (su2UpperCrossingLeftPositiveIndex n p hp).1 by rfl,
    su2_literal_sector_assemble_positive,
    show (su2Shift p.1 p.2.2, p.2.1) =
      (su2UpperCrossingTargetBoundaryIndex n p hp).1 by rfl,
    su2_literal_sector_assemble_boundary]

/-- Upper literal crossing trace is the left-gauged ordinary positive kernel. -/
theorem su2_upper_crossing_half_path_trace_gauge_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2RelativeFundamentalTrace
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right) p)
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right) p) =
    su2RelativeFundamentalTrace
      (right (su2UpperCrossingRightPositiveIndex n p hp))
      (su2BoundaryGaugeTransformEdge
        (boundary (su2UpperCrossingSourceBoundaryIndex n p hp))
        (boundary (su2UpperCrossingTargetBoundaryIndex n p hp))
        (left (su2UpperCrossingLeftPositiveIndex n p hp))) := by
  rw [su2_upper_crossing_first_half_path_readback,
    su2_upper_crossing_second_half_path_readback]
  exact su2_upper_crossing_trace_is_gauged_left _ _ _ _

/-- Literal lower first half path reads as boundary times left-copy edge. -/
theorem su2_lower_crossing_first_half_path_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right) p =
      boundary (su2LowerCrossingSourceBoundaryIndex n p hp) *
        left (su2LowerCrossingLeftPositiveIndex n p hp) := by
  unfold su2LiteralCrossingFirstBoundary su2PlaquetteFirstHalfPath
  change
    su2LiteralSectorAssemble n
        (left, boundary, su2PositiveFieldReflectedToNegative n right)
        (p.1, p.2.1) *
      su2LiteralSectorAssemble n
        (left, boundary, su2PositiveFieldReflectedToNegative n right)
        (su2Shift p.1 p.2.1, p.2.2) = _
  rw [show (p.1, p.2.1) =
      (su2LowerCrossingSourceBoundaryIndex n p hp).1 by rfl,
    su2_literal_sector_assemble_boundary,
    show (su2Shift p.1 p.2.1, p.2.2) =
      (su2LowerCrossingLeftPositiveIndex n p hp).1 by rfl,
    su2_literal_sector_assemble_positive]

/-- Literal lower second half path reads as right-copy edge times boundary. -/
theorem su2_lower_crossing_second_half_path_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right) p =
      right (su2LowerCrossingRightPositiveIndex n p hp) *
        boundary (su2LowerCrossingTargetBoundaryIndex n p hp) := by
  let qn : SU2NegativeInteriorLinkIndex n :=
    ⟨(p.1, p.2.2),
      (su2_lower_crossing_link_sector_geometry n p hp).2.2.1⟩
  have hSpatial := lower_crossing_second_spatial n p hp
  unfold su2LiteralCrossingSecondBoundary su2PlaquetteSecondHalfPath
  change
    su2LiteralSectorAssemble n
        (left, boundary, su2PositiveFieldReflectedToNegative n right)
        (p.1, p.2.2) *
      su2LiteralSectorAssemble n
        (left, boundary, su2PositiveFieldReflectedToNegative n right)
        (su2Shift p.1 p.2.2, p.2.1) = _
  rw [show (p.1, p.2.2) = qn.1 by rfl,
    su2_literal_sector_assemble_negative,
    show (su2Shift p.1 p.2.2, p.2.1) =
      (su2LowerCrossingTargetBoundaryIndex n p hp).1 by rfl,
    su2_literal_sector_assemble_boundary]
  unfold su2PositiveFieldReflectedToNegative
  change
    (if qn.1.2 = su2TimeDirection then
      (right ((su2PositiveNegativeLinkReflectionEquiv n).symm qn))⁻¹
     else right ((su2PositiveNegativeLinkReflectionEquiv n).symm qn)) *
      boundary _ = _
  rw [if_neg hSpatial]
  rfl

/-- Lower literal crossing trace is the right-gauged ordinary positive kernel. -/
theorem su2_lower_crossing_half_path_trace_gauge_readback
    (n : ℕ) [NeZero n]
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2RelativeFundamentalTrace
      (su2LiteralCrossingFirstBoundary
        (su2AssembleReflectedPair n left boundary right) p)
      (su2LiteralCrossingSecondBoundary
        (su2AssembleReflectedPair n left boundary right) p) =
    su2RelativeFundamentalTrace
      (left (su2LowerCrossingLeftPositiveIndex n p hp))
      (su2BoundaryGaugeTransformEdge
        (boundary (su2LowerCrossingSourceBoundaryIndex n p hp))
        (boundary (su2LowerCrossingTargetBoundaryIndex n p hp))
        (right (su2LowerCrossingRightPositiveIndex n p hp))) := by
  rw [su2_lower_crossing_first_half_path_readback,
    su2_lower_crossing_second_half_path_readback]
  exact su2_lower_crossing_trace_is_gauged_right _ _ _ _

end RequestProject.YangMills
