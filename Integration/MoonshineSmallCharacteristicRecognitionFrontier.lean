import Integration.ActionOrbitRecognition
import Integration.MoonshineSmallCharacteristicResidualTargets
import Mathlib

/-!
# Small-characteristic arithmetic -> Base369 recognition frontier

The exceptional arithmetic residual counts are:

* p=2: R₂ = 10
* p=3: R₃ = 2

These values are external arithmetic input mirrored from the attributed
Duncan--Swisher Agda lane.  Everything below is a DASHI recognition gate.

A matching component count is necessary but not sufficient for full
action/orbit/stabilizer recognition.
-/

namespace Integration.MoonshineSmallCharacteristicRecognitionFrontier

open Integration.ActionOrbitRecognition
open Integration.MoonshineSmallCharacteristicResidualTargets

def p2ExceptionalResidual : Nat := 10
def p3ExceptionalResidual : Nat := 2

structure Pi0RecognitionGate (sourcePi0 targetPi0 : Nat) : Prop where
  preservesCount : sourcePi0 = targetPi0

theorem p3_target_passes_pi0 :
    Pi0RecognitionGate p3ExceptionalResidual (Fintype.card P3Orbit) :=
  ⟨by decide⟩

theorem p2_gauge_target_fails_pi0 :
    ¬ Pi0RecognitionGate p2ExceptionalResidual (Fintype.card FiveOrbit) := by
  intro h
  exact (by decide : (10 : Nat) ≠ 5) (by simpa [p2ExceptionalResidual] using h.preservesCount)

theorem p2_retained_target_passes_pi0 :
    Pi0RecognitionGate p2ExceptionalResidual (Fintype.card P2State) :=
  ⟨by decide⟩

inductive RecognitionEvidenceStage
  | numericalCompatibilityOnly
  | targetGroupoidStructureExplicit
  | fullArithmeticActionGroupoidRecognition
  deriving DecidableEq, Repr

def p2CurrentStage : RecognitionEvidenceStage :=
  .targetGroupoidStructureExplicit

def p3CurrentStage : RecognitionEvidenceStage :=
  .targetGroupoidStructureExplicit

inductive Pi0CompatibilityAutomaticallyBuildsRecognition : Prop

theorem pi0_compatibility_does_not_build_recognition :
    ¬ Pi0CompatibilityAutomaticallyBuildsRecognition := by
  intro h
  cases h

/-! ## p=2 target semantics are selected by the component-count gate -/

def P2PassesArithmeticPi0 : P2TargetSemantics → Prop
  | .binaryFlipAsGauge => False
  | .orientationRetainedAsGluingData => True

theorem p2_retained_passes :
    P2PassesArithmeticPi0 .orientationRetainedAsGluingData :=
  trivial

theorem p2_gauge_does_not_pass :
    ¬ P2PassesArithmeticPi0 .binaryFlipAsGauge :=
  id

theorem p2_passing_target_must_retain_orientation
    (target : P2TargetSemantics)
    (h : P2PassesArithmeticPi0 target) :
    target = .orientationRetainedAsGluingData := by
  cases target with
  | binaryFlipAsGauge => contradiction
  | orientationRetainedAsGluingData => rfl

/-! ## Typed arithmetic source socket

The missing object is not another count.  It is an arithmetic action groupoid
that can be related to the independent target through
`OrbitStabilizerRecognition`.
-/

structure ArithmeticSourceGroupoid where
  State : Type
  Symmetry : Type
  action : InvertibleAction State Symmetry
  orbits : OrbitPresentation action

/-- Full recognition at p=3 must inhabit the generic repository owner. -/
abbrev P3FullRecognition
    (source : ArithmeticSourceGroupoid)
    (F : ActionRecognitionFunctor source.action p3Action) :=
  OrbitStabilizerRecognition F source.orbits p3OrbitPresentation

/-- Full recognition at p=2, after the pi0 discriminator, must target the
retained-orientation groupoid, not the flip quotient. -/
abbrev P2RetainedFullRecognition
    (source : ArithmeticSourceGroupoid)
    (F : ActionRecognitionFunctor source.action unitAction) :=
  OrbitStabilizerRecognition F source.orbits p2RetainedOrbitPresentation

inductive P2ArithmeticRecognitionConstructed : Prop
inductive P3ArithmeticRecognitionConstructed : Prop

theorem p2_recognition_still_open :
    ¬ P2ArithmeticRecognitionConstructed := by
  intro h
  cases h

theorem p3_recognition_still_open :
    ¬ P3ArithmeticRecognitionConstructed := by
  intro h
  cases h

structure Boundary where
  exceptionalResidualCountsTyped : Bool
  p3TargetPassesPi0 : Bool
  p2GaugeTargetFailsPi0 : Bool
  p2RetainedTargetPassesPi0 : Bool
  p2GateSelectsRetainedOrientation : Bool
  genericFullRecognitionOwnerUsed : Bool
  p2FullRecognitionConstructed : Bool
  p3FullRecognitionConstructed : Bool
  cardinalityMatchPromotedToRecognition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  exceptionalResidualCountsTyped := true
  p3TargetPassesPi0 := true
  p2GaugeTargetFailsPi0 := true
  p2RetainedTargetPassesPi0 := true
  p2GateSelectsRetainedOrientation := true
  genericFullRecognitionOwnerUsed := true
  p2FullRecognitionConstructed := false
  p3FullRecognitionConstructed := false
  cardinalityMatchPromotedToRecognition := false

end Integration.MoonshineSmallCharacteristicRecognitionFrontier
