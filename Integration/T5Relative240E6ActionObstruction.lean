import Integration.T5QuadraticOrbitAudit
import Integration.E6Mod3WeylAction
import Mathlib

/-!
# Natural E6-action obstruction for the canonical relative T5 240

The canonical `RelativeT5Carrier` removes the three constant/diagonal states
from the 243-state five-trit carrier.  Cardinality 240 is exact, but the
independently paid E6 action on the corresponding `F3^5` coordinates does not
preserve that complement.

There is an explicit witness: the non-diagonal standard vector
`(1,1,2,2,2)` is sent by the paid simple reflection `s3` to the constant
vector `(2,2,2,2,2)`.  Hence the natural E6 action cannot even be restricted
to the canonical 240-state complement.  This closes the proposed same-action
recognition *for this natural action*.  It does not prove that every imaginable
240-state ternary action is impossible.
-/

namespace Integration.T5Relative240E6ActionObstruction

open Integration.E6Mod3QuadraticBridge
open Integration.E6Mod3WeylAction

/-- Diagonal/constant predicate directly in the standard F3^5 coordinate. -/
def standardIsDiagonal (z : F3Five) : Bool :=
  decide (z.z0 = z.z1 ∧ z.z1 = z.z2 ∧ z.z2 = z.z3 ∧ z.z3 = z.z4)

/-- The standard-coordinate version of the canonical 240 complement. -/
def StandardRelative240 := {z : F3Five // standardIsDiagonal z = false}
instance : Fintype StandardRelative240 := inferInstance

/-- Exact count independently of any E8 interpretation. -/
theorem standard_relative_card_240 : Fintype.card StandardRelative240 = 240 := by
  native_decide

/-- Explicit non-diagonal witness. -/
def badPoint : F3Five := ⟨1, 1, 2, 2, 2⟩

theorem bad_point_is_relative : standardIsDiagonal badPoint = false := by
  native_decide

/-- The paid E6 reflection `s3` sends the witness to a diagonal point. -/
theorem s3_sends_bad_point_to_diagonal :
    standardIsDiagonal (reflectStandard .s3 badPoint) = true := by
  native_decide

/-- Global invariance predicate for the canonical complement under the existing
E6 simple-reflection action. -/
def NaturalRelative240InvariantUnderE6 : Prop :=
  ∀ s z, standardIsDiagonal z = false →
    standardIsDiagonal (reflectStandard s z) = false

theorem natural_relative_240_not_e6_invariant :
    ¬ NaturalRelative240InvariantUnderE6 := by
  intro h
  have hout := h .s3 badPoint bad_point_is_relative
  rw [s3_sends_bad_point_to_diagonal] at hout
  contradiction

/-- A proposed restriction of the already-defined E6 action to the 240-state
subtype must agree pointwise with `reflectStandard`. -/
structure NaturalE6ActionOnRelative240 : Type where
  act : E6SimpleReflection → StandardRelative240 → StandardRelative240
  agrees : ∀ s z, (act s z).1 = reflectStandard s z.1

/-- Such a restriction cannot exist because of the explicit escape witness. -/
theorem no_natural_e6_action_on_relative_240 :
    IsEmpty NaturalE6ActionOnRelative240 := by
  refine ⟨fun A => ?_⟩
  let z : StandardRelative240 := ⟨badPoint, bad_point_is_relative⟩
  have hz := (A.act .s3 z).2
  have hagree := A.agrees .s3 z
  change standardIsDiagonal ((A.act .s3 z).1) = false at hz
  rw [hagree, s3_sends_bad_point_to_diagonal] at hz
  contradiction

inductive Cardinality240OverridesActionObstruction : Prop
inductive NaturalActionNoGoBlocksAllPossibleTernaryActions : Prop

theorem cardinality_cannot_override_natural_action_obstruction :
    ¬ Cardinality240OverridesActionObstruction := by
  intro h; cases h

theorem natural_no_go_is_not_universal_no_go :
    ¬ NaturalActionNoGoBlocksAllPossibleTernaryActions := by
  intro h; cases h

structure Boundary where
  standardRelative240CountPaid : Bool
  explicitEscapeWitnessPaid : Bool
  naturalE6InvarianceRefuted : Bool
  naturalE6RestrictionImpossible : Bool
  naturalSameActionE8RecognitionBlocked : Bool
  allPossibleTernary240ActionsBlocked : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  standardRelative240CountPaid := true
  explicitEscapeWitnessPaid := true
  naturalE6InvarianceRefuted := true
  naturalE6RestrictionImpossible := true
  naturalSameActionE8RecognitionBlocked := true
  allPossibleTernary240ActionsBlocked := false

end Integration.T5Relative240E6ActionObstruction
