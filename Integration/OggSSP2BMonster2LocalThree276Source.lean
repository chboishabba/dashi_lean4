import Mathlib

/-!
# Source-native Monster 2-local three-276 donor

Holmes--Wilson construct the 196882-dimensional Monster module over F3 and, on
restriction to the 2B-pure Klein-four centralizer, obtain three literal 276-dimensional
constituents 276a, 276b and 276c.  Their order-three normalizer matrix cycles these three
constituents; an outer K:2 element interchanges 276b and 276c.

This is a genuine source-native three-276 carrier but not the characteristic-two Tate
same-object theorem: the published module here is over F3, whereas the 2B Tate head is
over F2.
-/

namespace Integration.OggSSP2BMonster2LocalThree276Source

inductive Three276
  | a | b | c
  deriving DecidableEq, Repr, Fintype

def moduleDimension : Three276 → Nat := fun _ => 276

def trialityT : Three276 → Three276
  | .a => .b
  | .b => .c
  | .c => .a

def outerK2Swap : Three276 → Three276
  | .a => .a
  | .b => .c
  | .c => .b

theorem triality_order_three (m : Three276) :
    trialityT (trialityT (trialityT m)) = m := by
  cases m <;> rfl

theorem outer_swap_involutive (m : Three276) :
    outerK2Swap (outerK2Swap m) = m := by
  cases m <;> rfl

theorem three_constituent_total_dimension :
    moduleDimension .a + moduleDimension .b + moduleDimension .c = 828 := by
  norm_num [moduleDimension]

structure SourceReceipt where
  ambientMonsterModuleDimension : Nat
  ambientCharacteristic : Nat
  literalThree276ConstituentsSourced : Bool
  orderThreeTrialitySourced : Bool
  outerK2SwapSourced : Bool
  characteristicTwoTateIdentificationPaid : Bool
  characteristicChangePaid : Bool
  source : String

/-- Exact source boundary. -/
def canonicalSourceReceipt : SourceReceipt where
  ambientMonsterModuleDimension := 196882
  ambientCharacteristic := 3
  literalThree276ConstituentsSourced := true
  orderThreeTrialitySourced := true
  outerK2SwapSourced := true
  characteristicTwoTateIdentificationPaid := false
  characteristicChangePaid := false
  source := "Holmes--Wilson, A new computer construction of the Monster using 2-local subgroups"

inductive GF3Three276IsCharacteristicTwoTateThreeFibre : Prop

theorem gf3_three276_does_not_construct_tate_three_fibre :
    ¬ GF3Three276IsCharacteristicTwoTateThreeFibre := by
  intro h
  cases h

end Integration.OggSSP2BMonster2LocalThree276Source
