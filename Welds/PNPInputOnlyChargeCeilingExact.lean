import Mathlib

namespace PNPInputOnlyChargeCeiling

/-- Static obligations distinguish a fixed original input from alternatives.
    Charging only original input coordinates can never exceed their count.
    No assertion about arbitrary computation events follows from this lemma. -/
theorem inputOnlyPackingCeiling {O I : Type*}
    (obligations : Finset O) (coordinates : Finset I)
    (charge : O → I → ℝ) (weight : O → ℝ)
    (cover : ∀ o ∈ obligations, weight o ≤ ∑ i ∈ coordinates, charge o i)
    (cap : ∀ i ∈ coordinates, (∑ o ∈ obligations, charge o i) ≤ 1) :
    (∑ o ∈ obligations, weight o) ≤ (coordinates.card : ℝ) := by
  classical
  calc
    (∑ o ∈ obligations, weight o) ≤
        ∑ o ∈ obligations, ∑ i ∈ coordinates, charge o i :=
      Finset.sum_le_sum cover
    _ = ∑ i ∈ coordinates, ∑ o ∈ obligations, charge o i :=
      Finset.sum_comm
    _ ≤ ∑ _i ∈ coordinates, (1 : ℝ) :=
      Finset.sum_le_sum cap
    _ = (coordinates.card : ℝ) := by simp

end PNPInputOnlyChargeCeiling
