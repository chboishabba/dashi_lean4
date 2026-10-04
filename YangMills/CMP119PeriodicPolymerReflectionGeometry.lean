import Mathlib
import YangMills.CMP119PolymerReflectionAudit
import YangMills.LiteralSU2LinkHalfGeometry

/-!
# Periodic 4D polymer reflection geometry for CMP119

This file grounds the Block-B four-way support classifier on the SAME finite
periodic four-dimensional link index used by the literal SU(2) lattice lane.
A source polymer is represented here only by its finite link support; source
coefficients/evaluators remain separate dictionary data.

The classifier asks whether that actual support meets the positive and negative
open time halves.  Boundary-only or empty support lands in `.empty`; a source
component may refine that branch if it distinguishes a boundary-supported local
term from an absent term.
-/

namespace RequestProject.YangMills

abbrev CMP119PeriodicLinkPolymer
    (n : ℕ) [NeZero n] :=
  Finset (FourDimensionalLinkIndex (2 * n))

/-- The finite polymer meets the selected positive open time half. -/
def cmp119PeriodicPolymerTouchesPositive
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) : Prop :=
  ∃ p ∈ X, su2PositiveInteriorLink n p

/-- The finite polymer meets the selected negative open time half. -/
def cmp119PeriodicPolymerTouchesNegative
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) : Prop :=
  ∃ p ∈ X, su2NegativeInteriorLink n p

/-- Literal four-way placement on the periodic link-support carrier. -/
noncomputable def cmp119PeriodicPolymerPlacement
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) : CMP119PolymerPlacement :=
  if cmp119PeriodicPolymerTouchesPositive n X then
    if cmp119PeriodicPolymerTouchesNegative n X then
      .crossing
    else
      .positive
  else if cmp119PeriodicPolymerTouchesNegative n X then
    .negative
  else
    .empty

/-- Crossing is exactly simultaneous support in both open time halves. -/
theorem cmp119_periodic_polymer_placement_crossing_iff
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) :
    cmp119PeriodicPolymerPlacement n X = CMP119PolymerPlacement.crossing ↔
      cmp119PeriodicPolymerTouchesPositive n X ∧
      cmp119PeriodicPolymerTouchesNegative n X := by
  unfold cmp119PeriodicPolymerPlacement
  by_cases hpos : cmp119PeriodicPolymerTouchesPositive n X <;>
    by_cases hneg : cmp119PeriodicPolymerTouchesNegative n X <;>
    simp [hpos, hneg]

/-- Positive-only support is exactly the corresponding periodic branch. -/
theorem cmp119_periodic_polymer_placement_positive_iff
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) :
    cmp119PeriodicPolymerPlacement n X = CMP119PolymerPlacement.positive ↔
      cmp119PeriodicPolymerTouchesPositive n X ∧
      ¬ cmp119PeriodicPolymerTouchesNegative n X := by
  unfold cmp119PeriodicPolymerPlacement
  by_cases hpos : cmp119PeriodicPolymerTouchesPositive n X <;>
    by_cases hneg : cmp119PeriodicPolymerTouchesNegative n X <;>
    simp [hpos, hneg]

/-- Negative-only support is exactly the corresponding periodic branch. -/
theorem cmp119_periodic_polymer_placement_negative_iff
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) :
    cmp119PeriodicPolymerPlacement n X = CMP119PolymerPlacement.negative ↔
      ¬ cmp119PeriodicPolymerTouchesPositive n X ∧
      cmp119PeriodicPolymerTouchesNegative n X := by
  unfold cmp119PeriodicPolymerPlacement
  by_cases hpos : cmp119PeriodicPolymerTouchesPositive n X <;>
    by_cases hneg : cmp119PeriodicPolymerTouchesNegative n X <;>
    simp [hpos, hneg]

/-- Boundary-only or empty support is exactly the residual branch. -/
theorem cmp119_periodic_polymer_placement_empty_iff
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) :
    cmp119PeriodicPolymerPlacement n X = CMP119PolymerPlacement.empty ↔
      ¬ cmp119PeriodicPolymerTouchesPositive n X ∧
      ¬ cmp119PeriodicPolymerTouchesNegative n X := by
  unfold cmp119PeriodicPolymerPlacement
  by_cases hpos : cmp119PeriodicPolymerTouchesPositive n X <;>
    by_cases hneg : cmp119PeriodicPolymerTouchesNegative n X <;>
    simp [hpos, hneg]

/--
Bridge the concrete periodic support classifier into the generic audit API.
The booleans are computed by decidability of the literal finite-support
predicates; no independent classification is selected.
-/
noncomputable def cmp119PeriodicPolymerReflectionDictionary
    (n : ℕ) [NeZero n] :
    CMP119PolymerReflectionDictionary (CMP119PeriodicLinkPolymer n) where
  touchesPositive := fun X => decide (cmp119PeriodicPolymerTouchesPositive n X)
  touchesNegative := fun X => decide (cmp119PeriodicPolymerTouchesNegative n X)

/-- The generic audit placement agrees exactly with the concrete periodic placement. -/
theorem cmp119_periodic_dictionary_placement_eq
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) :
    (cmp119PeriodicPolymerReflectionDictionary n).placement X =
      cmp119PeriodicPolymerPlacement n X := by
  by_cases hpos : cmp119PeriodicPolymerTouchesPositive n X <;>
    by_cases hneg : cmp119PeriodicPolymerTouchesNegative n X <;>
    simp [CMP119PolymerReflectionDictionary.placement,
      cmp119PeriodicPolymerReflectionDictionary,
      cmp119ClassifyPolymerSupport,
      cmp119PeriodicPolymerPlacement,
      hpos, hneg]

end RequestProject.YangMills
