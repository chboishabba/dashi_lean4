import Mathlib
import Integration.RiemannSSP15DepthFiveRoleCodec

/-!
# Chosen RH/SSP15 5×3 grid versus prime-native and CM observers

Lean mirror of the finite Agda table.

The chosen role-grid assignment is:
* origin column: {2,7,17,29,47}
* j column:      {3,11,19,31,59}
* s column:      {5,13,23,41,71}

Each role column crosses Q(sqrt(-7)) CM splitting classes.  The chosen internal
mode coordinate also differs from the independently defined prime-native nonary
complement observer, whose occupancies are 3,5,1,6,0.

This is a finite repository mirror, not an external arithmetic theorem.
-/

namespace Integration.RiemannSSP15ChosenGridTransversality

open Integration.RiemannSSP15DepthFiveRoleCodec

inductive Prime15
  | p2 | p3 | p5 | p7 | p11 | p13 | p17 | p19 | p23 | p29 | p31 | p41 | p47 | p59 | p71
  deriving DecidableEq, Repr, Fintype

def roleCodeToPrime : RHSSP15RoleCode → Prime15
  | (.mode09,.origin) => .p2
  | (.mode09,.j) => .p3
  | (.mode09,.s) => .p5
  | (.mode18,.origin) => .p7
  | (.mode18,.j) => .p11
  | (.mode18,.s) => .p13
  | (.mode27,.origin) => .p17
  | (.mode27,.j) => .p19
  | (.mode27,.s) => .p23
  | (.mode36,.origin) => .p29
  | (.mode36,.j) => .p31
  | (.mode36,.s) => .p41
  | (.mode45,.origin) => .p47
  | (.mode45,.j) => .p59
  | (.mode45,.s) => .p71

def originPrimeAt (m : Mode5) : Prime15 := roleCodeToPrime (m,.origin)
def jPrimeAt (m : Mode5) : Prime15 := roleCodeToPrime (m,.j)
def sPrimeAt (m : Mode5) : Prime15 := roleCodeToPrime (m,.s)

theorem origin_column_exact :
    [originPrimeAt .mode09, originPrimeAt .mode18, originPrimeAt .mode27,
      originPrimeAt .mode36, originPrimeAt .mode45]
    = [.p2,.p7,.p17,.p29,.p47] := rfl

theorem j_column_exact :
    [jPrimeAt .mode09, jPrimeAt .mode18, jPrimeAt .mode27,
      jPrimeAt .mode36, jPrimeAt .mode45]
    = [.p3,.p11,.p19,.p31,.p59] := rfl

theorem s_column_exact :
    [sPrimeAt .mode09, sPrimeAt .mode18, sPrimeAt .mode27,
      sPrimeAt .mode36, sPrimeAt .mode45]
    = [.p5,.p13,.p23,.p41,.p71] := rfl

inductive CMClass
  | split | inert | ramified
  deriving DecidableEq, Repr

def cmClass : Prime15 → CMClass
  | .p2 => .split
  | .p3 => .inert
  | .p5 => .inert
  | .p7 => .ramified
  | .p11 => .split
  | .p13 => .inert
  | .p17 => .inert
  | .p19 => .inert
  | .p23 => .split
  | .p29 => .split
  | .p31 => .inert
  | .p41 => .inert
  | .p47 => .inert
  | .p59 => .inert
  | .p71 => .split

theorem origin_column_crosses_cm :
    cmClass (originPrimeAt .mode09) ≠ cmClass (originPrimeAt .mode18) := by
  decide

theorem j_column_crosses_cm :
    cmClass (jPrimeAt .mode09) ≠ cmClass (jPrimeAt .mode18) := by
  decide

theorem s_column_crosses_cm :
    cmClass (sPrimeAt .mode09) ≠ cmClass (sPrimeAt .mode27) := by
  decide

/-- Lean mirror of the independent Agda prime-native complement observer. -/
def nativeComplementMode : Prime15 → Mode5
  | .p2 => .mode27
  | .p3 => .mode36
  | .p5 => .mode45
  | .p7 => .mode27
  | .p11 => .mode27
  | .p13 => .mode45
  | .p17 => .mode18
  | .p19 => .mode18
  | .p23 => .mode45
  | .p29 => .mode27
  | .p31 => .mode45
  | .p41 => .mode45
  | .p47 => .mode27
  | .p59 => .mode45
  | .p71 => .mode18

def nativeModeOccupancy (m : Mode5) : Nat :=
  (Finset.univ.filter fun p : Prime15 => nativeComplementMode p = m).card

theorem native_mode18_occupancy : nativeModeOccupancy .mode18 = 3 := by native_decide
theorem native_mode27_occupancy : nativeModeOccupancy .mode27 = 5 := by native_decide
theorem native_mode36_occupancy : nativeModeOccupancy .mode36 = 1 := by native_decide
theorem native_mode45_occupancy : nativeModeOccupancy .mode45 = 6 := by native_decide
theorem native_mode09_occupancy : nativeModeOccupancy .mode09 = 0 := by native_decide

theorem native_occupancies_sum_to_fifteen :
    nativeModeOccupancy .mode18 +
    nativeModeOccupancy .mode27 +
    nativeModeOccupancy .mode36 +
    nativeModeOccupancy .mode45 +
    nativeModeOccupancy .mode09 = 15 := by
  native_decide

theorem chosen_mode09_origin_not_native_mode :
    nativeComplementMode (roleCodeToPrime (.mode09,.origin)) ≠ .mode09 := by
  decide

theorem chosen_grid_not_native_five_by_three :
    nativeModeOccupancy .mode09 ≠ 3 := by
  native_decide

inductive PromotionError
  | chosenGridIsPrimeNativeComplementPartition
  | roleColumnsAreCMClasses
  deriving DecidableEq, Repr

structure Boundary where
  exactChosenPrimeColumnsOwned : Bool
  everyRoleColumnCrossesCMClasses : Bool
  nativeOccupancyThreeFiveOneSixZeroOwned : Bool
  chosenModeDiffersFromNativeObserver : Bool
  chosenGridPromotedToPrimeNativePartition : Bool
  roleColumnsPromotedToCMClasses : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  exactChosenPrimeColumnsOwned := true
  everyRoleColumnCrossesCMClasses := true
  nativeOccupancyThreeFiveOneSixZeroOwned := true
  chosenModeDiffersFromNativeObserver := true
  chosenGridPromotedToPrimeNativePartition := false
  roleColumnsPromotedToCMClasses := false

end Integration.RiemannSSP15ChosenGridTransversality
