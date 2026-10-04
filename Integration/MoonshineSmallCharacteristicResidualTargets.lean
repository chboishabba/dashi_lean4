import Integration.ActionOrbitRecognition
import Integration.TernaryHub
import Mathlib

/-!
# Base369 small-characteristic residual targets

Lean mirror of the independent Agda target owners:

* `Base369P3ConstantTernaryActionGroupoidExact`;
* `Base369P2FiveOrbitOrientationGroupoidsExact`.

These are target constructions only.  No arithmetic recognition is claimed.
-/

namespace Integration.MoonshineSmallCharacteristicResidualTargets

open Integration.ActionOrbitRecognition
open Integration.TernaryHub

/-! ## §1 C2 -/

inductive C2
  | e | flip
  deriving DecidableEq, Repr, Fintype

def c2Mul : C2 → C2 → C2
  | .e, h => h
  | .flip, .e => .flip
  | .flip, .flip => .e

def c2Inv : C2 → C2 := id

/-! ## §2 p=3 constant ternary target -/

def negateSSP : SSPTrit → SSPTrit
  | .negOne => .posOne
  | .zero => .zero
  | .posOne => .negOne

def p3Act : C2 → SSPTrit → SSPTrit
  | .e, s => s
  | .flip, s => negateSSP s

def p3Action : InvertibleAction SSPTrit C2 where
  identity := .e
  combine := c2Mul
  inverse := c2Inv
  act := p3Act
  identity_acts := by intro s; rfl
  combine_acts := by intro g h s; cases g <;> cases h <;> cases s <;> rfl
  inverse_left := by intro g s; cases g <;> cases s <;> rfl
  inverse_right := by intro g s; cases g <;> cases s <;> rfl

inductive P3Orbit
  | zeroOrbit | nonzeroOrbit
  deriving DecidableEq, Repr, Fintype

def p3OrbitOf : SSPTrit → P3Orbit
  | .zero => .zeroOrbit
  | .negOne | .posOne => .nonzeroOrbit

def p3Representative : P3Orbit → SSPTrit
  | .zeroOrbit => .zero
  | .nonzeroOrbit => .posOne

def p3Transporter : SSPTrit → C2
  | .negOne => .flip
  | .zero | .posOne => .e

def p3OrbitPresentation : OrbitPresentation p3Action where
  Orbit := P3Orbit
  orbitOf := p3OrbitOf
  representative := p3Representative
  orbitInvariant := by intro g s; cases g <;> cases s <;> rfl
  representativeInOrbit := by intro o; cases o <;> rfl
  transporter := p3Transporter
  transporterHits := by intro s; cases s <;> rfl

theorem p3_zero_fixed_by_flip :
    p3Action.act .flip (p3OrbitPresentation.representative .zeroOrbit) =
      p3OrbitPresentation.representative .zeroOrbit := rfl

theorem p3_nonzero_not_fixed_by_flip :
    p3Action.act .flip (p3OrbitPresentation.representative .nonzeroOrbit) ≠
      p3OrbitPresentation.representative .nonzeroOrbit := by decide

theorem p3_pi0_count : Fintype.card P3Orbit = 2 := by decide

/-! ## §3 p=2 ten-object carrier -/

inductive OrientationPolarity
  | negative | positive
  deriving DecidableEq, Repr, Fintype

def flipOrientation : OrientationPolarity → OrientationPolarity
  | .negative => .positive
  | .positive => .negative

inductive FiveOrbit
  | o0 | o1 | o2 | o3 | o4
  deriving DecidableEq, Repr, Fintype

abbrev P2State := OrientationPolarity × FiveOrbit

def p2GaugeAct : C2 → P2State → P2State
  | .e, s => s
  | .flip, (orientation, orbit) => (flipOrientation orientation, orbit)

def p2GaugeAction : InvertibleAction P2State C2 where
  identity := .e
  combine := c2Mul
  inverse := c2Inv
  act := p2GaugeAct
  identity_acts := by intro s; rfl
  combine_acts := by
    intro g h s
    rcases s with ⟨orientation,orbit⟩
    cases g <;> cases h <;> cases orientation <;> rfl
  inverse_left := by
    intro g s
    rcases s with ⟨orientation,orbit⟩
    cases g <;> cases orientation <;> rfl
  inverse_right := by
    intro g s
    rcases s with ⟨orientation,orbit⟩
    cases g <;> cases orientation <;> rfl

def p2GaugeOrbitPresentation : OrbitPresentation p2GaugeAction where
  Orbit := FiveOrbit
  orbitOf := Prod.snd
  representative := fun o => (.negative,o)
  orbitInvariant := by
    intro g s
    rcases s with ⟨orientation,orbit⟩
    cases g <;> rfl
  representativeInOrbit := by intro o; rfl
  transporter := fun s => match s.1 with
    | .negative => .e
    | .positive => .flip
  transporterHits := by
    intro s
    rcases s with ⟨orientation,orbit⟩
    cases orientation <;> rfl

/-! Retained orientation: identity-only groupoid. -/

def unitAction : InvertibleAction P2State Unit where
  identity := ()
  combine := fun _ _ => ()
  inverse := fun _ => ()
  act := fun _ s => s
  identity_acts := by intro s; rfl
  combine_acts := by intro g h s; rfl
  inverse_left := by intro g s; rfl
  inverse_right := by intro g s; rfl

def p2RetainedOrbitPresentation : OrbitPresentation unitAction where
  Orbit := P2State
  orbitOf := id
  representative := id
  orbitInvariant := by intro g s; rfl
  representativeInOrbit := by intro o; rfl
  transporter := fun _ => ()
  transporterHits := by intro s; rfl

theorem p2_fine_state_count : Fintype.card P2State = 10 := by decide
theorem p2_gauge_pi0_count : Fintype.card FiveOrbit = 5 := by decide
theorem p2_retained_pi0_count : Fintype.card P2State = 10 := by decide

inductive P2TargetSemantics
  | binaryFlipAsGauge
  | orientationRetainedAsGluingData
  deriving DecidableEq, Repr

def p2TargetPi0Count : P2TargetSemantics → Nat
  | .binaryFlipAsGauge => 5
  | .orientationRetainedAsGluingData => 10

theorem p2_flip_target_not_ten :
    p2TargetPi0Count .binaryFlipAsGauge ≠ 10 := by decide

theorem p2_retained_target_is_ten :
    p2TargetPi0Count .orientationRetainedAsGluingData = 10 := rfl

structure Boundary where
  p3CanonicalThreeStateTargetOwned : Bool
  p3TwoOrbitPresentationOwned : Bool
  p3ZeroFixedNonzeroFreeSplitOwned : Bool
  p2SameTenFineStatesSupportBothSemantics : Bool
  p2GaugePi0Five : Bool
  p2RetainedPi0Ten : Bool
  carrierAloneChoosesSemantics : Bool
  arithmeticRecognitionClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  p3CanonicalThreeStateTargetOwned := true
  p3TwoOrbitPresentationOwned := true
  p3ZeroFixedNonzeroFreeSplitOwned := true
  p2SameTenFineStatesSupportBothSemantics := true
  p2GaugePi0Five := true
  p2RetainedPi0Ten := true
  carrierAloneChoosesSemantics := false
  arithmeticRecognitionClaimed := false

end Integration.MoonshineSmallCharacteristicResidualTargets
