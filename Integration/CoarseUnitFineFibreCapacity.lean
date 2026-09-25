import Mathlib

/-!
# Coarse unit / fine fibre capacity

A single coarse unit may sit over k fine states.  This does not imply automatic
semantic or physical amplification.  A fine distinction matters only for a
consumer/future relation that actually separates it.
-/

namespace Integration.CoarseUnitFineFibreCapacity

abbrev CoarseUnitFineState (k : Nat) := Unit × Fin k

def coarseUnitProject {k : Nat} :
    CoarseUnitFineState k → Unit := fun _ => ()

def fineIndex {k : Nat} :
    CoarseUnitFineState k → Fin k := Prod.snd

theorem same_coarse_unit
    {k : Nat}
    (left right : CoarseUnitFineState k) :
    coarseUnitProject left = coarseUnitProject right := rfl

theorem fine_index_injective
    {k : Nat} :
    Function.Injective (fineIndex : CoarseUnitFineState k → Fin k) := by
  intro left right h
  rcases left with ⟨⟨⟩, li⟩
  rcases right with ⟨⟨⟩, ri⟩
  simp_all [fineIndex]

theorem coarse_projection_not_injective_when_two_or_more
    {k : Nat}
    (h : 2 ≤ k) :
    ¬ Function.Injective
      (coarseUnitProject : CoarseUnitFineState k → Unit) := by
  intro hinj
  let i0 : Fin k := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) h⟩
  let i1 : Fin k := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) h⟩
  have pairEq : (((), i0) : CoarseUnitFineState k) = ((), i1) := hinj rfl
  have : i0 = i1 := congrArg Prod.snd pairEq
  exact Fin.zero_ne_one this

theorem nineteen_six_eighty_three_is_nontrivial : 2 ≤ 19683 := by norm_num

theorem completion_fine_coordinate_count : 1 * 19683 = 19683 := by norm_num

structure CoarseUnitFineFibreCapacityBoundary where
  oneCoarseUnitCanIndexFiniteFineFibre : Bool
  jCompletionFineCoordinateCountRecorded : Bool
  fixedValueFibreCardinalityNotInferred : Bool
  oneExtraCoordinateAutomaticallyImprovesEveryConsumer : Bool
  fibreSizeAloneCreatesPhysicalMechanism : Bool
  deriving Repr

def canonicalBoundary : CoarseUnitFineFibreCapacityBoundary where
  oneCoarseUnitCanIndexFiniteFineFibre := true
  jCompletionFineCoordinateCountRecorded := true
  fixedValueFibreCardinalityNotInferred := true
  oneExtraCoordinateAutomaticallyImprovesEveryConsumer := false
  fibreSizeAloneCreatesPhysicalMechanism := false

end Integration.CoarseUnitFineFibreCapacity
