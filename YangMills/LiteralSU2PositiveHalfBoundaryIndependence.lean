import Mathlib
import YangMills.LiteralSU2BoundaryGaugeProjectionSymmetry
import YangMills.LiteralSU2WilsonOSFactorization

/-!
# Positive Wilson half is independent of the reflection-boundary fields

A positive noncrossing plaquette uses only positive-interior links.  Therefore
its literal Wilson factor, and hence the complete positive Wilson half, reads
only the positive-interior field of `su2AssembleReflectedPair`.

This is the last finite-link locality theorem needed before the final
boundary-Haar/Fubini positivity calculation in Block A.
-/

namespace RequestProject.YangMills

private theorem positive_spatial_shift_preserves_time_value
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (direction : Fin 4)
    (hSpatial : direction ≠ su2TimeDirection) :
    ((su2Shift x direction) su2TimeDirection).val =
      (x su2TimeDirection).val := by
  simp [su2Shift, Function.update_noteq hSpatial]

private theorem positive_time_shift_value
    (n : ℕ) [NeZero n]
    (x : SU2TorusSite (2 * n))
    (ht : (x su2TimeDirection).val < n - 1) :
    ((su2Shift x su2TimeDirection) su2TimeDirection).val =
      (x su2TimeDirection).val + 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hlt : (x su2TimeDirection).val + 1 < 2 * n := by omega
  simp only [su2Shift, Function.update_same]
  rw [ZMod.val_add]
  have hone : ((1 : ZMod (2 * n))).val = 1 := by
    rw [ZMod.val_natCast_of_lt]
    omega
  rw [hone, Nat.mod_eq_of_lt hlt]

private theorem positive_second_direction_spatial
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2FourDimensionalPlaquettes (2 * n)) :
    p.2.2 ≠ su2TimeDirection := by
  simp only [su2FourDimensionalPlaquettes,
    Finset.mem_filter, Finset.mem_univ, true_and] at hp
  intro hSecond
  rw [hSecond] at hp
  have hImpossible : p.2.1.val < 0 := by
    simpa [su2TimeDirection] using hp
  omega

/-- All four links in a positive noncrossing plaquette are positive-interior links. -/
theorem su2_positive_noncrossing_link_sector_geometry
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2EvenTimePositivePlaquettes n) :
    su2PositiveInteriorLink n (p.1, p.2.1) ∧
    su2PositiveInteriorLink n (su2Shift p.1 p.2.1, p.2.2) ∧
    su2PositiveInteriorLink n (su2Shift p.1 p.2.2, p.2.1) ∧
    su2PositiveInteriorLink n (p.1, p.2.2) := by
  simp only [su2EvenTimePositivePlaquettes, Finset.mem_filter] at hp
  have hPhysical := hp.1
  have hNoncross := hp.2.1
  have hBase := hp.2.2
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hSecondSpatial := positive_second_direction_spatial n p hPhysical
  have hSecondShift :=
    positive_spatial_shift_preserves_time_value n p.1 p.2.2 hSecondSpatial
  have hFirst : su2PositiveInteriorLink n (p.1, p.2.1) := by
    refine ⟨?_, hBase⟩
    intro hb
    rcases hb with ⟨hTime, hUpper | hLower⟩
    · exact hNoncross ⟨hTime, Or.inl hUpper⟩
    · omega
  have hFourth : su2PositiveInteriorLink n (p.1, p.2.2) := by
    refine ⟨?_, hBase⟩
    intro hb
    exact hSecondSpatial hb.1
  have hThird :
      su2PositiveInteriorLink n (su2Shift p.1 p.2.2, p.2.1) := by
    refine ⟨?_, ?_⟩
    · intro hb
      rcases hb with ⟨hTime, hUpper | hLower⟩
      · have : (p.1 su2TimeDirection).val = n - 1 := by
          simpa [hSecondShift] using hUpper
        exact hNoncross ⟨hTime, Or.inl this⟩
      · rw [hSecondShift] at hLower
        omega
    · rw [hSecondShift]
      exact hBase
  have hSecond :
      su2PositiveInteriorLink n (su2Shift p.1 p.2.1, p.2.2) := by
    refine ⟨?_, ?_⟩
    · intro hb
      exact hSecondSpatial hb.1
    · by_cases hTime : p.2.1 = su2TimeDirection
      · have hNotUpper : (p.1 su2TimeDirection).val ≠ n - 1 := by
          intro hUpper
          exact hNoncross ⟨hTime, Or.inl hUpper⟩
        have hlt : (p.1 su2TimeDirection).val < n - 1 := by omega
        rw [hTime, positive_time_shift_value n p.1 hlt]
        omega
      · rw [positive_spatial_shift_preserves_time_value n p.1 p.2.1 hTime]
        exact hBase
  exact ⟨hFirst, hSecond, hThird, hFourth⟩

/-- Read any positive-interior coordinate of the reflected-pair assembly from `left`. -/
theorem su2_assembled_pair_positive_link_readback
    (n : ℕ) [NeZero n]
    (left : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (right : SU2PositiveInteriorLinks n)
    (p : FourDimensionalLinkIndex (2 * n))
    (hp : su2PositiveInteriorLink n p) :
    fourDimensionalFlattenLinks
        (su2AssembleReflectedPair n left boundary right) p =
      left ⟨p, hp⟩ := by
  change su2LiteralSectorAssemble n
      (left, boundary, su2PositiveFieldReflectedToNegative n right) p = _
  simpa using
    su2_literal_sector_assemble_positive n
      (left, boundary, su2PositiveFieldReflectedToNegative n right) ⟨p, hp⟩

/-- A positive noncrossing plaquette is independent of boundary and reflected-right data. -/
theorem su2_positive_noncrossing_plaquette_assembled_pair_independent
    (n : ℕ) [NeZero n]
    (left : SU2PositiveInteriorLinks n)
    (boundary₁ boundary₂ : SU2BoundaryTemporalLinks n)
    (right₁ right₂ : SU2PositiveInteriorLinks n)
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2EvenTimePositivePlaquettes n) :
    su2Plaquette (su2AssembleReflectedPair n left boundary₁ right₁)
        p.1 p.2.1 p.2.2 =
      su2Plaquette (su2AssembleReflectedPair n left boundary₂ right₂)
        p.1 p.2.1 p.2.2 := by
  rcases su2_positive_noncrossing_link_sector_geometry n p hp with
    ⟨h₁, h₂, h₃, h₄⟩
  unfold su2Plaquette
  change
    fourDimensionalFlattenLinks
        (su2AssembleReflectedPair n left boundary₁ right₁) (p.1, p.2.1) *
      fourDimensionalFlattenLinks
        (su2AssembleReflectedPair n left boundary₁ right₁)
          (su2Shift p.1 p.2.1, p.2.2) *
      (fourDimensionalFlattenLinks
        (su2AssembleReflectedPair n left boundary₁ right₁)
          (su2Shift p.1 p.2.2, p.2.1))⁻¹ *
      (fourDimensionalFlattenLinks
        (su2AssembleReflectedPair n left boundary₁ right₁) (p.1, p.2.2))⁻¹ = _
  rw [su2_assembled_pair_positive_link_readback n left boundary₁ right₁ _ h₁,
    su2_assembled_pair_positive_link_readback n left boundary₁ right₁ _ h₂,
    su2_assembled_pair_positive_link_readback n left boundary₁ right₁ _ h₃,
    su2_assembled_pair_positive_link_readback n left boundary₁ right₁ _ h₄,
    su2_assembled_pair_positive_link_readback n left boundary₂ right₂ _ h₁,
    su2_assembled_pair_positive_link_readback n left boundary₂ right₂ _ h₂,
    su2_assembled_pair_positive_link_readback n left boundary₂ right₂ _ h₃,
    su2_assembled_pair_positive_link_readback n left boundary₂ right₂ _ h₄]

/--
The complete positive Wilson half reads only the positive-interior field `left`.
In particular it is independent of both boundary Haar planes and of `right`.
-/
theorem su2_positive_half_assembled_pair_boundary_independent
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left : SU2PositiveInteriorLinks n)
    (boundary₁ boundary₂ : SU2BoundaryTemporalLinks n)
    (right₁ right₂ : SU2PositiveInteriorLinks n) :
    su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary₁ right₁) β =
      su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary₂ right₂) β := by
  unfold su2EvenTimePositiveWilsonHalf su2LiteralWilsonProduct
  apply Finset.prod_congr rfl
  intro p hp
  rw [su2_positive_noncrossing_plaquette_assembled_pair_independent
    n left boundary₁ boundary₂ right₁ right₂ p hp]

end RequestProject.YangMills
