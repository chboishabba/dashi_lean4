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

/-! ## Cheap source-proxy eliminations -/

/-- Mirroring the Agda p=2 source-side fact: a naive identity-only residual
proxy built from the 2-dimensional spinor basis would have two components,
not the required ten.  This rejects that proxy only. -/
theorem p2_spinor_identity_proxy_fails_pi0 :
    ¬ Pi0RecognitionGate p2ExceptionalResidual 2 := by
  intro h
  exact (by decide : (10 : Nat) ≠ 2)
    (by simpa [p2ExceptionalResidual] using h.preservesCount)

/-- Mirroring the Agda p=3 separation theorem: the supersingular Frobenius
proxy has one component, not the required two. -/
theorem p3_supersingular_frobenius_proxy_fails_pi0 :
    ¬ Pi0RecognitionGate p3ExceptionalResidual 1 := by
  intro h
  exact (by decide : (2 : Nat) ≠ 1)
    (by simpa [p3ExceptionalResidual] using h.preservesCount)

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

inductive ExceptionalResidualPrime
  | p2 | p3
  deriving DecidableEq, Repr

def expectedResidualCount : ExceptionalResidualPrime → Nat
  | .p2 => p2ExceptionalResidual
  | .p3 => p3ExceptionalResidual

structure ArithmeticSourceGroupoid (prime : ExceptionalResidualPrime) where
  State : Type
  Symmetry : Type
  action : InvertibleAction State Symmetry
  orbits : OrbitPresentation action
  pi0Count : Nat
  pi0CountExact : pi0Count = expectedResidualCount prime
  provenance : String
  arithmeticConstructionReference : String
  actionGroupoidExternallySourcedClaim : Bool

/-- Full recognition includes the generic orbit/stabilizer recognition plus an
explicit count receipt. -/
structure P3FullRecognition
    (source : ArithmeticSourceGroupoid .p3) where
  functor : ActionRecognitionFunctor source.action p3Action
  recognition :
    OrbitStabilizerRecognition functor source.orbits p3OrbitPresentation
  pi0CountPreserved : source.pi0Count = Fintype.card P3Orbit

structure P2RetainedFullRecognition
    (source : ArithmeticSourceGroupoid .p2) where
  functor : ActionRecognitionFunctor source.action unitAction
  recognition :
    OrbitStabilizerRecognition functor source.orbits p2RetainedOrbitPresentation
  pi0CountPreserved : source.pi0Count = Fintype.card P2State

/-- Stronger optional grade: literal two-sided state and symmetry recovery. -/
structure P3SamePresentation
    (source : ArithmeticSourceGroupoid .p3) where
  functor : ActionRecognitionFunctor source.action p3Action
  presentationIsomorphism :
    ActionGroupoidPresentationIsomorphism
      functor source.orbits p3OrbitPresentation

structure P2RetainedSamePresentation
    (source : ArithmeticSourceGroupoid .p2) where
  functor : ActionRecognitionFunctor source.action unitAction
  presentationIsomorphism :
    ActionGroupoidPresentationIsomorphism
      functor source.orbits p2RetainedOrbitPresentation

theorem p3_full_recognition_closes_count
    (source : ArithmeticSourceGroupoid .p3)
    (recognized : P3FullRecognition source) :
    source.pi0Count = p3ExceptionalResidual := by
  exact source.pi0CountExact

theorem p2_full_recognition_closes_count
    (source : ArithmeticSourceGroupoid .p2)
    (recognized : P2RetainedFullRecognition source) :
    source.pi0Count = p2ExceptionalResidual := by
  exact source.pi0CountExact

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
  p2NaiveSpinorProxyRejected : Bool
  p3SupersingularFrobeniusProxyRejected : Bool
  genericFullRecognitionOwnerUsed : Bool
  sourceRequiresIndependentPi0Receipt : Bool
  sourceCarriesProvenanceReference : Bool
  samePresentationRequiresStateAndSymmetryBijections : Bool
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
  p2NaiveSpinorProxyRejected := true
  p3SupersingularFrobeniusProxyRejected := true
  genericFullRecognitionOwnerUsed := true
  sourceRequiresIndependentPi0Receipt := true
  sourceCarriesProvenanceReference := true
  samePresentationRequiresStateAndSymmetryBijections := true
  p2FullRecognitionConstructed := false
  p3FullRecognitionConstructed := false
  cardinalityMatchPromotedToRecognition := false

end Integration.MoonshineSmallCharacteristicRecognitionFrontier
