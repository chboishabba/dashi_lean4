import Mathlib
import YangMills.LiteralSU2LinkHalfGeometry

/-!
# Exact positive / boundary / negative link-index product split

This is the finite-index decomposition consumed by the final Wilson OS2
Fubini argument.  It introduces no new lattice carrier: all three sector types
are subtypes of the already-selected flat physical link index.
-/

namespace RequestProject.YangMills

abbrev SU2PositiveInteriorLinkIndex
    (n : ℕ) [NeZero n] :=
  {p : FourDimensionalLinkIndex (2 * n) // su2PositiveInteriorLink n p}

abbrev SU2BoundaryTemporalLinkIndex
    (n : ℕ) [NeZero n] :=
  {p : FourDimensionalLinkIndex (2 * n) // su2ReflectionBoundaryTemporalLink n p}

abbrev SU2NegativeInteriorLinkIndex
    (n : ℕ) [NeZero n] :=
  {p : FourDimensionalLinkIndex (2 * n) // su2NegativeInteriorLink n p}

/-- Reflection is an exact bijection between positive and negative interior link indices. -/
def su2PositiveNegativeLinkReflectionEquiv
    (n : ℕ) [NeZero n] :
    SU2PositiveInteriorLinkIndex n ≃ SU2NegativeInteriorLinkIndex n where
  toFun p :=
    ⟨fourDimensionalEvenTimeReflectLinkIndex p.1,
      su2_positive_interior_reflects_negative n p.1 p.2⟩
  invFun p :=
    ⟨fourDimensionalEvenTimeReflectLinkIndex p.1,
      su2_negative_interior_reflects_positive n p.1 p.2⟩
  left_inv p := by
    apply Subtype.ext
    exact four_dimensional_even_time_reflect_link_index_involutive p.1
  right_inv p := by
    apply Subtype.ext
    exact four_dimensional_even_time_reflect_link_index_involutive p.1

/-- Boundary temporal link indices are pointwise fixed by the index reflection. -/
theorem su2_boundary_link_reflection_eq
    (n : ℕ) [NeZero n]
    (p : SU2BoundaryTemporalLinkIndex n) :
    fourDimensionalEvenTimeReflectLinkIndex p.1 = p.1 :=
  su2_boundary_temporal_link_index_fixed n p.1 p.2

/--
Every flat physical link index is uniquely represented by one of the three
actual OS sectors.
-/
def su2LinkSectorSumEquiv
    (n : ℕ) [NeZero n] :
    (SU2PositiveInteriorLinkIndex n ⊕
      SU2BoundaryTemporalLinkIndex n ⊕
      SU2NegativeInteriorLinkIndex n) ≃
      FourDimensionalLinkIndex (2 * n) where
  toFun sector :=
    match sector with
    | Sum.inl p => p.1
    | Sum.inr (Sum.inl p) => p.1
    | Sum.inr (Sum.inr p) => p.1
  invFun p :=
    if hp : su2PositiveInteriorLink n p then
      Sum.inl ⟨p, hp⟩
    else if hb : su2ReflectionBoundaryTemporalLink n p then
      Sum.inr (Sum.inl ⟨p, hb⟩)
    else
      Sum.inr (Sum.inr ⟨p, by
        rcases su2_even_time_link_cut_exhaustive n p with hpos | hneg | hboundary
        · exact False.elim (hp hpos)
        · exact hneg
        · exact False.elim (hb hboundary)⟩)
  left_inv sector := by
    rcases sector with p | sector
    · simp [p.2]
    · rcases sector with p | p
      · have hnotPos : ¬ su2PositiveInteriorLink n p.1 := by
          intro hp
          exact (su2_even_time_link_cut_pairwise_disjoint n p.1).2.1
            ⟨hp, p.2⟩
        simp [hnotPos, p.2]
      · have hnotPos : ¬ su2PositiveInteriorLink n p.1 := by
          intro hp
          exact (su2_even_time_link_cut_pairwise_disjoint n p.1).1
            ⟨hp, p.2⟩
        have hnotBoundary : ¬ su2ReflectionBoundaryTemporalLink n p.1 := p.2.1
        simp [hnotPos, hnotBoundary]
  right_inv p := by
    by_cases hp : su2PositiveInteriorLink n p
    · simp [hp]
    · by_cases hb : su2ReflectionBoundaryTemporalLink n p
      · simp [hp, hb]
      · simp [hp, hb]

/-- The sector equivalence is literally exhaustive on the selected link carrier. -/
theorem su2_link_sector_sum_equiv_surjective
    (n : ℕ) [NeZero n] :
    Function.Surjective (su2LinkSectorSumEquiv n) :=
  (su2LinkSectorSumEquiv n).surjective

end RequestProject.YangMills
