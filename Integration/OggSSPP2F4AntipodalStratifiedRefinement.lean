import Mathlib
import Integration.OggSSPSmallCharacteristicRecognition
import Integration.OggSSPP2F4FrobeniusCandidateNoGo

/-!
# p=2 F4-shaped 1+1+8 antipodal refinement

Lean mirror of the Agda target-side stratified rechart.

The retained target has ten states.  Relative to raw F4 Frobenius orbit type it
admits the exact profile

  fixed0 -> 1
  fixed1 -> 1
  conjugatePair -> 8

so 1 + 1 + 8 = 10.

The two fixed strata map to the two binary copies of the antipodal centre; the
conjugate-pair stratum maps to the eight binary/noncentral states.  The raw-F4
stabilizer sizes 2,2,1 match the inherited antipodal stabilizer TYPES.

This is not an arithmetic marked-source construction.
-/

namespace Integration.OggSSPP2F4AntipodalStratifiedRefinement

open Integration.OggSSPSmallCharacteristicRecognition
open Integration.OggSSPP2F4FrobeniusCandidateNoGo

inductive NoncentralNineOrbit
  | firstAxis
  | secondAxis
  | equalSign
  | oppositeSign
  deriving DecidableEq, Repr, Fintype

def noncentralToNineOrbit : NoncentralNineOrbit → NineOrbit
  | .firstAxis => .firstAxis
  | .secondAxis => .secondAxis
  | .equalSign => .equalSign
  | .oppositeSign => .oppositeSign

inductive StratifiedTargetState
  | fixedZero
  | fixedOne
  | conjugate (side : StrictSide) (orbit : NoncentralNineOrbit)
  deriving DecidableEq, Repr, Fintype

def stratumOf : StratifiedTargetState → F4Orbit
  | .fixedZero => .zeroFixed
  | .fixedOne => .oneFixed
  | .conjugate _ _ => .conjugatePair

def toRetainedTarget : StratifiedTargetState → P2State
  | .fixedZero => (.lower, .zero)
  | .fixedOne => (.upper, .zero)
  | .conjugate side .firstAxis => (side, .firstAxis)
  | .conjugate side .secondAxis => (side, .secondAxis)
  | .conjugate side .equalSign => (side, .equalSign)
  | .conjugate side .oppositeSign => (side, .oppositeSign)

def fromRetainedTarget : P2State → StratifiedTargetState
  | (.lower, .zero) => .fixedZero
  | (.upper, .zero) => .fixedOne
  | (side, .firstAxis) => .conjugate side .firstAxis
  | (side, .secondAxis) => .conjugate side .secondAxis
  | (side, .equalSign) => .conjugate side .equalSign
  | (side, .oppositeSign) => .conjugate side .oppositeSign

theorem stratified_target_roundtrip (s : StratifiedTargetState) :
    fromRetainedTarget (toRetainedTarget s) = s := by
  cases s with
  | fixedZero => rfl
  | fixedOne => rfl
  | conjugate side orbit =>
      cases side <;> cases orbit <;> rfl

theorem retained_target_roundtrip (s : P2State) :
    toRetainedTarget (fromRetainedTarget s) = s := by
  rcases s with ⟨side, orbit⟩
  cases side <;> cases orbit <;> rfl

theorem stratified_target_cardinality :
    Fintype.card StratifiedTargetState = 10 := by decide

def stratumRefinementCount : F4Orbit → Nat
  | .zeroFixed => 1
  | .oneFixed => 1
  | .conjugatePair => 8

theorem one_plus_one_plus_eight :
    stratumRefinementCount .zeroFixed +
      stratumRefinementCount .oneFixed +
      stratumRefinementCount .conjugatePair = 10 := by
  rfl

theorem conjugate_refinement_is_binary_times_four :
    stratumRefinementCount .conjugatePair = 2 * 4 := by
  rfl

def rawF4OrbitStabilizerSize : F4Orbit → Nat
  | .zeroFixed => 2
  | .oneFixed => 2
  | .conjugatePair => 1

def inheritedAntipodalStabilizerSize : P2State → Nat
  | (_, .zero) => 2
  | (_, .firstAxis) => 1
  | (_, .secondAxis) => 1
  | (_, .equalSign) => 1
  | (_, .oppositeSign) => 1

theorem stratified_rechart_preserves_stabilizer_type
    (s : StratifiedTargetState) :
    rawF4OrbitStabilizerSize (stratumOf s) =
      inheritedAntipodalStabilizerSize (toRetainedTarget s) := by
  cases s with
  | fixedZero => rfl
  | fixedOne => rfl
  | conjugate side orbit =>
      cases orbit <;> rfl

inductive ClaimOrigin
  | repositoryCrossModuleInference
  | openArithmeticRecognition
  deriving DecidableEq, Repr

def rechartOrigin : ClaimOrigin := .repositoryCrossModuleInference
def arithmeticRecognitionOrigin : ClaimOrigin := .openArithmeticRecognition

structure Boundary where
  exactOneOneEightRechart : Bool
  twoFixedStrataMatchTwoCentreCopiesByType : Bool
  conjugateStratumMatchesEightNoncentralCopiesByType : Bool
  inheritedStabilizerTypePreserved : Bool
  uniformThreeStratumLiftRuledOut : Bool
  arithmeticMarkedRefinementConstructed : Bool
  arithmeticRecognitionClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  exactOneOneEightRechart := true
  twoFixedStrataMatchTwoCentreCopiesByType := true
  conjugateStratumMatchesEightNoncentralCopiesByType := true
  inheritedStabilizerTypePreserved := true
  uniformThreeStratumLiftRuledOut := true
  arithmeticMarkedRefinementConstructed := false
  arithmeticRecognitionClaimed := false

end Integration.OggSSPP2F4AntipodalStratifiedRefinement
