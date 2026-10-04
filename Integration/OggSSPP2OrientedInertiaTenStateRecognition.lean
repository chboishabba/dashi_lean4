import Mathlib
import Integration.OggSSPP2F4AntipodalStratifiedRefinement

/-!
# p=2 oriented-inertia ten-state carrier

Lean mirror of the finite carrier used on the Agda small-characteristic branch.

Classically sourced ingredients on the Agda side:
* two orientations of the relevant quadratic-order datum;
* five inversion-orbits of the binary-tetrahedral inertia conjugacy classes.

This Lean file reconstructs only the finite product and its exact rechart to the
already-paid ten-state p=2 target. It does not claim that the product is itself
the Gamma_0(4) supersingular level fibre or a named classical moduli stack.
-/

namespace Integration.OggSSPP2OrientedInertiaTenStateRecognition

namespace Target := Integration.OggSSPP2F4AntipodalStratifiedRefinement

inductive ClassicalQuadraticOrientation
  | lower
  | upper
  deriving DecidableEq, Repr, Fintype

inductive BinaryTetrahedralInversionOrbit
  | identity
  | centralMinusOne
  | orderFour
  | orderThreePair
  | orderSixPair
  deriving DecidableEq, Repr, Fintype

abbrev State :=
  ClassicalQuadraticOrientation × BinaryTetrahedralInversionOrbit

theorem state_cardinality :
    Fintype.card State = 10 := by
  decide

def toTarget : State → Target.StratifiedTargetState
  | (.lower, .identity) => .fixedZero
  | (.upper, .identity) => .fixedOne
  | (.lower, .centralMinusOne) => .conjugate .lower .firstAxis
  | (.upper, .centralMinusOne) => .conjugate .upper .firstAxis
  | (.lower, .orderFour) => .conjugate .lower .secondAxis
  | (.upper, .orderFour) => .conjugate .upper .secondAxis
  | (.lower, .orderThreePair) => .conjugate .lower .equalSign
  | (.upper, .orderThreePair) => .conjugate .upper .equalSign
  | (.lower, .orderSixPair) => .conjugate .lower .oppositeSign
  | (.upper, .orderSixPair) => .conjugate .upper .oppositeSign

def fromTarget : Target.StratifiedTargetState → State
  | .fixedZero => (.lower, .identity)
  | .fixedOne => (.upper, .identity)
  | .conjugate .lower .firstAxis => (.lower, .centralMinusOne)
  | .conjugate .upper .firstAxis => (.upper, .centralMinusOne)
  | .conjugate .lower .secondAxis => (.lower, .orderFour)
  | .conjugate .upper .secondAxis => (.upper, .orderFour)
  | .conjugate .lower .equalSign => (.lower, .orderThreePair)
  | .conjugate .upper .equalSign => (.upper, .orderThreePair)
  | .conjugate .lower .oppositeSign => (.lower, .orderSixPair)
  | .conjugate .upper .oppositeSign => (.upper, .orderSixPair)

theorem state_roundtrip (s : State) :
    fromTarget (toTarget s) = s := by
  rcases s with ⟨orientation, inertia⟩
  cases orientation <;> cases inertia <;> rfl

theorem target_roundtrip (s : Target.StratifiedTargetState) :
    toTarget (fromTarget s) = s := by
  cases s with
  | fixedZero => rfl
  | fixedOne => rfl
  | conjugate side orbit =>
      cases side <;> cases orbit <;> rfl

def equivTarget : State ≃ Target.StratifiedTargetState where
  toFun := toTarget
  invFun := fromTarget
  left_inv := state_roundtrip
  right_inv := target_roundtrip

def coarseOrbit : State →
    Integration.OggSSPP2F4FrobeniusCandidateNoGo.F4Orbit :=
  Target.stratumOf ∘ toTarget

theorem coarse_orbit_preserved (s : State) :
    Target.stratumOf (toTarget s) = coarseOrbit s := rfl

structure Boundary where
  twoOrientationCarrierOwned : Bool
  fiveInertiaOrbitCarrierOwned : Bool
  exactTwoTimesFiveCarrierOwned : Bool
  exactRechartToPaidTenStateTarget : Bool
  gamma0FourLevelFibreIdentityClaimed : Bool
  namedClassicalModuliStackClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  twoOrientationCarrierOwned := true
  fiveInertiaOrbitCarrierOwned := true
  exactTwoTimesFiveCarrierOwned := true
  exactRechartToPaidTenStateTarget := true
  gamma0FourLevelFibreIdentityClaimed := false
  namedClassicalModuliStackClaimed := false

end Integration.OggSSPP2OrientedInertiaTenStateRecognition
