import Mathlib
import Integration.OggSSPSmallCharacteristicRecognition

/-!
# Balanced ternary antipodal 3 / 9 / 27 orbit hierarchy

Lean mirror of the Agda balanced-ternary antipodal hierarchy owner.

This consolidates the finite antipodal quotient geometry

* 3 = 1 + 1*2  -> 2 orbit classes
* 9 = 1 + 4*2  -> 5 orbit classes
* 27 = 1 + 13*2 -> 14 orbit classes

and proves that the small-characteristic target counts are presentations of
this hierarchy.

No arithmetic recognition theorem is inferred from these cardinal identities.
-/

namespace Integration.BalancedTernaryAntipodal369OrbitHierarchy

open Integration.OggSSPSmallCharacteristicRecognition

inductive Trit
  | neg | zero | pos
  deriving DecidableEq, Repr, Fintype

def antipode : Trit → Trit
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

theorem antipode_involutive (x : Trit) : antipode (antipode x) = x := by
  cases x <;> rfl

inductive Orbit3
  | centre | nonzero
  deriving DecidableEq, Repr, Fintype

def classify3 : Trit → Orbit3
  | .zero => .centre
  | .neg => .nonzero
  | .pos => .nonzero

theorem classify3_antipode_invariant (x : Trit) :
    classify3 (antipode x) = classify3 x := by
  cases x <;> rfl

inductive Orbit9
  | centre | firstAxis | secondAxis | sameSignDiagonal | oppositeSignDiagonal
  deriving DecidableEq, Repr, Fintype

def classify9 : Trit × Trit → Orbit9
  | (.zero, .zero) => .centre
  | (.pos, .zero) => .firstAxis
  | (.neg, .zero) => .firstAxis
  | (.zero, .pos) => .secondAxis
  | (.zero, .neg) => .secondAxis
  | (.pos, .pos) => .sameSignDiagonal
  | (.neg, .neg) => .sameSignDiagonal
  | (.pos, .neg) => .oppositeSignDiagonal
  | (.neg, .pos) => .oppositeSignDiagonal

def antipode9 : Trit × Trit → Trit × Trit
  | (a,b) => (antipode a, antipode b)

theorem classify9_antipode_invariant (x : Trit × Trit) :
    classify9 (antipode9 x) = classify9 x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> rfl

inductive Orbit27
  | centre
  | firstPositive (b c : Trit)
  | secondPositive (c : Trit)
  | thirdPositive
  deriving DecidableEq, Repr, Fintype

theorem orbit3_cardinality : Fintype.card Orbit3 = 2 := by decide
theorem orbit9_cardinality : Fintype.card Orbit9 = 5 := by decide
theorem orbit27_cardinality : Fintype.card Orbit27 = 14 := by decide

theorem trit_cardinality : Fintype.card Trit = 3 := by decide
theorem trit_pair_cardinality : Fintype.card (Trit × Trit) = 9 := by decide
theorem trit_triple_cardinality : Fintype.card (Trit × Trit × Trit) = 27 := by decide

theorem three_centre_plus_pairs : 3 = 1 + 1 * 2 := by decide
theorem nine_centre_plus_pairs : 9 = 1 + 4 * 2 := by decide
theorem twenty_seven_centre_plus_pairs : 27 = 1 + 13 * 2 := by decide

inductive Rank
  | one | two | three
  deriving DecidableEq, Repr

def rawCarrierCount : Rank → Nat
  | .one => 3
  | .two => 9
  | .three => 27

def pairedOrbitCount : Rank → Nat
  | .one => 1
  | .two => 4
  | .three => 13

def quotientOrbitCount : Rank → Nat
  | .one => 2
  | .two => 5
  | .three => 14

theorem raw_count_is_centre_plus_pairs (r : Rank) :
    rawCarrierCount r = 1 + pairedOrbitCount r * 2 := by
  cases r <;> decide

theorem quotient_count_is_centre_plus_pair_classes (r : Rank) :
    quotientOrbitCount r = 1 + pairedOrbitCount r := by
  cases r <;> decide

def nineOrbitToAntipodal : NineOrbit → Orbit9
  | .zero => .centre
  | .firstAxis => .firstAxis
  | .secondAxis => .secondAxis
  | .equalSign => .sameSignDiagonal
  | .oppositeSign => .oppositeSignDiagonal

def antipodalToNineOrbit : Orbit9 → NineOrbit
  | .centre => .zero
  | .firstAxis => .firstAxis
  | .secondAxis => .secondAxis
  | .sameSignDiagonal => .equalSign
  | .oppositeSignDiagonal => .oppositeSign

theorem nine_antipodal_roundtrip (o : NineOrbit) :
    antipodalToNineOrbit (nineOrbitToAntipodal o) = o := by
  cases o <;> rfl

theorem antipodal_nine_roundtrip (o : Orbit9) :
    nineOrbitToAntipodal (antipodalToNineOrbit o) = o := by
  cases o <;> rfl

def p3OrbitToAntipodal : P3Orbit → Orbit3
  | .zero => .centre
  | .nonzero => .nonzero

def antipodalToP3Orbit : Orbit3 → P3Orbit
  | .centre => .zero
  | .nonzero => .nonzero

theorem p3_antipodal_roundtrip (o : P3Orbit) :
    antipodalToP3Orbit (p3OrbitToAntipodal o) = o := by
  cases o <;> rfl

theorem antipodal_p3_roundtrip (o : Orbit3) :
    p3OrbitToAntipodal (antipodalToP3Orbit o) = o := by
  cases o <;> rfl

def p3AntipodalTargetCount : Nat := quotientOrbitCount .one
def p2RetainedAntipodalTargetCount : Nat := 2 * quotientOrbitCount .two

theorem p3_antipodal_target_count : p3AntipodalTargetCount = 2 := by rfl
theorem p2_retained_antipodal_target_count : p2RetainedAntipodalTargetCount = 10 := by rfl

theorem p3_existing_target_matches_rank1 :
    Fintype.card P3Orbit = quotientOrbitCount .one := by decide

theorem p2_existing_orbit_matches_rank2 :
    Fintype.card NineOrbit = quotientOrbitCount .two := by decide

theorem p2_existing_retained_target_matches_binary_times_rank2 :
    Fintype.card P2State = 2 * quotientOrbitCount .two := by decide

inductive ClaimOrigin
  | finiteGroupActionCalibration
  | repositoryCrossModuleInference
  | openArithmeticRecognition
  deriving DecidableEq, Repr

def hierarchyOrigin : ClaimOrigin := .repositoryCrossModuleInference
def arithmeticRecognitionOrigin : ClaimOrigin := .openArithmeticRecognition

structure Boundary where
  rank1ThreeToTwo : Bool
  rank2NineToFive : Bool
  rank3TwentySevenToFourteen : Bool
  uniqueFixedCentrePlusPairs : Bool
  p3TargetRechartedToRank1 : Bool
  p2OrbitRechartedToRank2 : Bool
  p2RetainedTargetIsBinaryTimesRank2 : Bool
  arithmeticRecognitionAutomatic : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  rank1ThreeToTwo := true
  rank2NineToFive := true
  rank3TwentySevenToFourteen := true
  uniqueFixedCentrePlusPairs := true
  p3TargetRechartedToRank1 := true
  p2OrbitRechartedToRank2 := true
  p2RetainedTargetIsBinaryTimesRank2 := true
  arithmeticRecognitionAutomatic := false

end Integration.BalancedTernaryAntipodal369OrbitHierarchy
