import Mathlib
import Integration.FutureSafeCoarseFibreCapacity

/-!
# Latent distinction activation

A generic two-state dynamic shape:

* equal current coarse observation;
* same admissible/control action;
* unequal later observation.

The Agda owner binds this directly to the proof-bearing action-system,
FutureEquivalent and residual-capacity machinery.  This Lean mirror records the
finite theorem shape.
-/

namespace Integration.LatentDistinctionActivation

structure Activation
    {State Observation : Type}
    (project : State → Observation) where
  left : State
  right : State
  leftAfter : State
  rightAfter : State
  sameCurrent : project left = project right
  differentAfter : project leftAfter ≠ project rightAfter

def representative
    {State Observation : Type}
    {project : State → Observation}
    (a : Activation project) : Fin 2 → State
  | ⟨0, _⟩ => a.left
  | ⟨1, _⟩ => a.right

theorem activation_pair_distinct
    {State Observation : Type}
    {project : State → Observation}
    (a : Activation project)
    (stepLeft : a.leftAfter = a.left)
    (stepRight : a.rightAfter = a.right) :
    a.left ≠ a.right := by
  intro h
  apply a.differentAfter
  rw [stepLeft, stepRight, h]

structure Boundary where
  sameCurrentObservationRequired : Bool
  commonDynamicExposureRequiredInAgdaOwner : Bool
  laterObservationSplitRequired : Bool
  hiddenDifferenceAutomaticallyMatters : Bool
  theoremCreatesDomainMechanism : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sameCurrentObservationRequired := true
  commonDynamicExposureRequiredInAgdaOwner := true
  laterObservationSplitRequired := true
  hiddenDifferenceAutomaticallyMatters := false
  theoremCreatesDomainMechanism := false

end Integration.LatentDistinctionActivation
