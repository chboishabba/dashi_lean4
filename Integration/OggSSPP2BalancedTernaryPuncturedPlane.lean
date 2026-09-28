import Mathlib
import Integration.BalancedTernaryAntipodal369OrbitHierarchy
import Integration.OggSSPP2F4AntipodalStratifiedRefinement

/-!
# p=2 balanced-ternary punctured plane

The 1+1+8 p=2 target profile has the exact balanced-ternary normal form

  1 + 1 + (3^2 - 1) = 3^2 + 1 = 10.

The eight-state conjugate fibre is recharted to the punctured ternary plane
T^2 \ {(0,0)}.  The full ten-state target is therefore a duplicated-centre
completion of one nine-sheet.

This is finite target geometry only; no arithmetic CM identification follows.
-/

namespace Integration.OggSSPP2BalancedTernaryPuncturedPlane

open Integration.BalancedTernaryAntipodal369OrbitHierarchy
open Integration.OggSSPP2F4AntipodalStratifiedRefinement
open Integration.OggSSPSmallCharacteristicRecognition

abbrev NineSheet := Trit × Trit

inductive PuncturedNineSheet
  | negativeFirstAxis
  | positiveFirstAxis
  | negativeSecondAxis
  | positiveSecondAxis
  | negativeEqualDiagonal
  | positiveEqualDiagonal
  | negativeOppositeDiagonal
  | positiveOppositeDiagonal
  deriving DecidableEq, Repr, Fintype

def puncturedToNineSheet : PuncturedNineSheet → NineSheet
  | .negativeFirstAxis => (.neg, .zero)
  | .positiveFirstAxis => (.pos, .zero)
  | .negativeSecondAxis => (.zero, .neg)
  | .positiveSecondAxis => (.zero, .pos)
  | .negativeEqualDiagonal => (.neg, .neg)
  | .positiveEqualDiagonal => (.pos, .pos)
  | .negativeOppositeDiagonal => (.neg, .pos)
  | .positiveOppositeDiagonal => (.pos, .neg)

theorem punctured_cardinality :
    Fintype.card PuncturedNineSheet = 8 := by decide

theorem eight_is_three_squared_minus_one :
    Fintype.card PuncturedNineSheet = 3 * 3 - 1 := by decide

def conjugateMarkToPunctured :
    StrictSide × NoncentralNineOrbit → PuncturedNineSheet
  | (.lower, .firstAxis) => .negativeFirstAxis
  | (.upper, .firstAxis) => .positiveFirstAxis
  | (.lower, .secondAxis) => .negativeSecondAxis
  | (.upper, .secondAxis) => .positiveSecondAxis
  | (.lower, .equalSign) => .negativeEqualDiagonal
  | (.upper, .equalSign) => .positiveEqualDiagonal
  | (.lower, .oppositeSign) => .negativeOppositeDiagonal
  | (.upper, .oppositeSign) => .positiveOppositeDiagonal

def puncturedToConjugateMark :
    PuncturedNineSheet → StrictSide × NoncentralNineOrbit
  | .negativeFirstAxis => (.lower, .firstAxis)
  | .positiveFirstAxis => (.upper, .firstAxis)
  | .negativeSecondAxis => (.lower, .secondAxis)
  | .positiveSecondAxis => (.upper, .secondAxis)
  | .negativeEqualDiagonal => (.lower, .equalSign)
  | .positiveEqualDiagonal => (.upper, .equalSign)
  | .negativeOppositeDiagonal => (.lower, .oppositeSign)
  | .positiveOppositeDiagonal => (.upper, .oppositeSign)

theorem conjugate_punctured_roundtrip
    (m : StrictSide × NoncentralNineOrbit) :
    puncturedToConjugateMark (conjugateMarkToPunctured m) = m := by
  rcases m with ⟨side, orbit⟩
  cases side <;> cases orbit <;> rfl

theorem punctured_conjugate_roundtrip
    (p : PuncturedNineSheet) :
    conjugateMarkToPunctured (puncturedToConjugateMark p) = p := by
  cases p <;> rfl

inductive DuplicatedCentreNineSheet
  | lowerCentre
  | upperCentre
  | puncturedPoint (point : PuncturedNineSheet)
  deriving DecidableEq, Repr, Fintype

def duplicatedCentreToStratified :
    DuplicatedCentreNineSheet → StratifiedTargetState
  | .lowerCentre => .fixedZero
  | .upperCentre => .fixedOne
  | .puncturedPoint p =>
      let m := puncturedToConjugateMark p
      .conjugate m.1 m.2

def stratifiedToDuplicatedCentre :
    StratifiedTargetState → DuplicatedCentreNineSheet
  | .fixedZero => .lowerCentre
  | .fixedOne => .upperCentre
  | .conjugate side orbit =>
      .puncturedPoint (conjugateMarkToPunctured (side, orbit))

theorem duplicated_centre_stratified_roundtrip
    (s : DuplicatedCentreNineSheet) :
    stratifiedToDuplicatedCentre (duplicatedCentreToStratified s) = s := by
  cases s with
  | lowerCentre => rfl
  | upperCentre => rfl
  | puncturedPoint p =>
      simp [duplicatedCentreToStratified, stratifiedToDuplicatedCentre,
        punctured_conjugate_roundtrip]

theorem stratified_duplicated_centre_roundtrip
    (s : StratifiedTargetState) :
    duplicatedCentreToStratified (stratifiedToDuplicatedCentre s) = s := by
  cases s with
  | fixedZero => rfl
  | fixedOne => rfl
  | conjugate side orbit =>
      cases side <;> cases orbit <;> rfl

def collapseDuplicatedCentre :
    DuplicatedCentreNineSheet → NineSheet
  | .lowerCentre => (.zero, .zero)
  | .upperCentre => (.zero, .zero)
  | .puncturedPoint p => puncturedToNineSheet p

theorem duplicated_centres_collapse_together :
    collapseDuplicatedCentre .lowerCentre =
      collapseDuplicatedCentre .upperCentre := rfl

theorem duplicated_centre_cardinality :
    Fintype.card DuplicatedCentreNineSheet = 10 := by decide

theorem ten_is_one_plus_one_plus_punctured_plane :
    Fintype.card DuplicatedCentreNineSheet =
      1 + 1 + Fintype.card PuncturedNineSheet := by decide

theorem ten_is_three_squared_plus_one :
    Fintype.card DuplicatedCentreNineSheet = 3 * 3 + 1 := by decide

inductive ClaimOrigin
  | repositoryCrossModuleInference
  | openArithmeticRecognition
  deriving DecidableEq, Repr

structure Boundary where
  conjugateFibreIsPuncturedTernaryPlane : Bool
  puncturedPlaneHasEightStates : Bool
  eightIsThreeSquaredMinusOne : Bool
  targetIsDuplicatedCentreNineSheet : Bool
  tenIsThreeSquaredPlusOne : Bool
  arithmeticCMIdentificationClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  conjugateFibreIsPuncturedTernaryPlane := true
  puncturedPlaneHasEightStates := true
  eightIsThreeSquaredMinusOne := true
  targetIsDuplicatedCentreNineSheet := true
  tenIsThreeSquaredPlusOne := true
  arithmeticCMIdentificationClaimed := false

end Integration.OggSSPP2BalancedTernaryPuncturedPlane
