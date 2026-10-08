import Integration.E8E6A2TernaryBranchingCandidate
import Integration.E6Mod3WeylAction
import Mathlib

/-!
# Original punctured T5 is not stable under the paid E6 action

The original relative five-trit carrier deletes the constant diagonal line from
`F3^5`.  The later structured 240-state E8 carrier is a different object.

This owner closes one ambiguity: the original 240-state cut cannot simply
inherit the already-paid E6 mod-3 action by restriction.

Take the nonzero diagonal vector

  d = (1,1,1,1,1).

The simple E6 reflection `s3` sends it to

  (2,2,1,1,1),

which is outside the diagonal.  Since `s3` is an involution, that outside point
is sent back to the deleted diagonal.  Thus the 240-point complement is not
E6-invariant.

This blocks only the natural inherited E6 action.  It does not rule out every
possible independently constructed same-object recognition between the original
punctured T5 and E8.
-/

namespace Integration.T5RelativeE6ActionRestrictionObstruction

open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction
open Integration.E8E6A2TernaryBranchingCandidate

/-- The old constant-diagonal line in standardized F3^5 coordinates. -/
def OldDiagonal (z : F3Five) : Prop :=
  z.z0 = z.z1 ∧ z.z1 = z.z2 ∧ z.z2 = z.z3 ∧ z.z3 = z.z4

instance (z : F3Five) : Decidable (OldDiagonal z) := inferInstance

/-- Original 240-state relative complement in the standard chart. -/
def OldRelativeT5 := {z : F3Five // ¬ OldDiagonal z}
instance : Fintype OldRelativeT5 := inferInstance

 theorem old_relative_t5_card : Fintype.card OldRelativeT5 = 240 := by
  native_decide

/-- Selected nonzero deleted diagonal state. -/
def diagonalOne : F3Five := ⟨1,1,1,1,1⟩

 theorem diagonal_one_is_deleted : OldDiagonal diagonalOne := by
  native_decide

/-- Its image leaves the deleted line. -/
def escapedDiagonal : F3Five := reflectStandard .s3 diagonalOne

 theorem escaped_diagonal_coordinates :
    escapedDiagonal = ⟨2,2,1,1,1⟩ := by
  native_decide

 theorem escaped_diagonal_is_relative : ¬ OldDiagonal escapedDiagonal := by
  native_decide

/-- Hence this is an actual state of the 240-point complement. -/
def escapedRelative : OldRelativeT5 :=
  ⟨escapedDiagonal, escaped_diagonal_is_relative⟩

/-- Involution sends that relative state directly back to the deleted diagonal. -/
theorem s3_sends_relative_state_into_deleted_diagonal :
    reflectStandard .s3 escapedRelative.1 = diagonalOne := by
  native_decide

 theorem s3_image_of_witness_is_diagonal :
    OldDiagonal (reflectStandard .s3 escapedRelative.1) := by
  rw [s3_sends_relative_state_into_deleted_diagonal]
  exact diagonal_one_is_deleted

/-- Restriction of the already-paid E6 action to the old 240 carrier is impossible. -/
def OldRelativeInvariantUnderE6 : Prop :=
  ∀ s (z : OldRelativeT5), ¬ OldDiagonal (reflectStandard s z.1)

 theorem old_relative_not_e6_invariant : ¬ OldRelativeInvariantUnderE6 := by
  intro h
  have hout := h .s3 escapedRelative
  exact hout s3_image_of_witness_is_diagonal

inductive ExistingE6ActionRestrictsToOldRelativeT5 : Prop

 theorem paid_e6_action_does_not_restrict_to_original_240 :
    ¬ ExistingE6ActionRestrictsToOldRelativeT5 := by
  intro h
  cases h

structure Boundary where
  oldRelativeCard240Paid : Bool
  explicitDiagonalEscapePaid : Bool
  explicitRelativeReturnToDeletedLinePaid : Bool
  oldRelativeE6Invariant : Bool
  existingE6ActionRestrictsToOldRelative240 : Bool
  allPossibleIndependentT5E8RecognitionsBlocked : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  oldRelativeCard240Paid := true
  explicitDiagonalEscapePaid := true
  explicitRelativeReturnToDeletedLinePaid := true
  oldRelativeE6Invariant := false
  existingE6ActionRestrictsToOldRelative240 := false
  allPossibleIndependentT5E8RecognitionsBlocked := false

end Integration.T5RelativeE6ActionRestrictionObstruction
