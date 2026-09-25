import Mathlib
import Integration.TwistronicsRelativeRegistrationComparator
import Integration.FutureSafeCoarseFibreCapacity

namespace Integration.TwistronicsRegistrationControlFutureSplit

open Integration.TwistronicsRelativeRegistrationComparator

structure RegistrationControl (Registration : Type) where
  updateRegistration : Registration → Registration
  label : String
  deriving Repr

inductive ControlAction
  | applyRegistrationControl
  deriving DecidableEq, Repr

def controlledState
    {Microscopic Registration : Type}
    (control : RegistrationControl Registration)
    (state : OverlayState Microscopic Registration) :
    OverlayState Microscopic Registration :=
  { state with
    relativeRegistration :=
      control.updateRegistration state.relativeRegistration }

theorem control_preserves_left
    {Microscopic Registration : Type}
    (control : RegistrationControl Registration)
    (state : OverlayState Microscopic Registration) :
    (controlledState control state).leftMicroscopic =
      state.leftMicroscopic := rfl

theorem control_preserves_right
    {Microscopic Registration : Type}
    (control : RegistrationControl Registration)
    (state : OverlayState Microscopic Registration) :
    (controlledState control state).rightMicroscopic =
      state.rightMicroscopic := rfl

structure ControlSplitWitness
    {Microscopic Registration Effective : Type}
    (observeEffective : OverlayState Microscopic Registration → Effective)
    (control : RegistrationControl Registration) where
  microscopic : Microscopic
  firstRegistration : Registration
  secondRegistration : Registration
  sameBefore :
    observeEffective
      ⟨microscopic, microscopic, firstRegistration⟩ =
    observeEffective
      ⟨microscopic, microscopic, secondRegistration⟩
  differentAfter :
    observeEffective
      (controlledState control
        ⟨microscopic, microscopic, firstRegistration⟩) ≠
    observeEffective
      (controlledState control
        ⟨microscopic, microscopic, secondRegistration⟩)

structure Boundary where
  primaryInSituTwistControlAttributedInAgdaOwner : Bool
  proofBearingRegistrationControlShapeMirrored : Bool
  controlPreservesMicroscopicLayerSlots : Bool
  futureSplitRequiresExplicitControlSensitiveWitness : Bool
  exactExperimentalEqualBeforeUnequalAfterPairInvented : Bool
  staticParameterDependenceCalledTimeEvolution : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  primaryInSituTwistControlAttributedInAgdaOwner := true
  proofBearingRegistrationControlShapeMirrored := true
  controlPreservesMicroscopicLayerSlots := true
  futureSplitRequiresExplicitControlSensitiveWitness := true
  exactExperimentalEqualBeforeUnequalAfterPairInvented := false
  staticParameterDependenceCalledTimeEvolution := false

end Integration.TwistronicsRegistrationControlFutureSplit
