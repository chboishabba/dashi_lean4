import Mathlib
import Integration.NonginOnePointOneArmyRefinement
import Integration.TwistronicsRelativeRegistrationComparator
import Integration.FutureSafeCoarseFibreCapacity

/-!
# Nongin / TSFV / twistronics future-safety bridge

The current-observer non-factorisation shape is already available for the
nongin and twistronics mirrors.  Concrete future-equivalence promotion remains
conditional on a proof-bearing dynamics/action system; this file does not
invent one.
-/

namespace Integration.NonginTSFVTwistronicsFutureSafetyBridge

inductive DomainLane
  | nonginFrame
  | tsfvHistory
  | twistronicsRegistration
  deriving DecidableEq, Repr

structure DomainFutureSafetyStatus where
  lane : DomainLane
  currentConsumerNonDescentProved : Bool
  proofBearingActionSystemSuppliedHere : Bool
  finiteFutureDistinctFibreSuppliedHere : Bool
  concreteFutureCapacityBoundInstantiatedHere : Bool
  deriving Repr

def nonginStatus : DomainFutureSafetyStatus where
  lane := .nonginFrame
  currentConsumerNonDescentProved := true
  proofBearingActionSystemSuppliedHere := false
  finiteFutureDistinctFibreSuppliedHere := false
  concreteFutureCapacityBoundInstantiatedHere := false

def tsfvStatus : DomainFutureSafetyStatus where
  lane := .tsfvHistory
  currentConsumerNonDescentProved := true
  proofBearingActionSystemSuppliedHere := false
  finiteFutureDistinctFibreSuppliedHere := false
  concreteFutureCapacityBoundInstantiatedHere := false

def twistronicsStatus : DomainFutureSafetyStatus where
  lane := .twistronicsRegistration
  currentConsumerNonDescentProved := true
  proofBearingActionSystemSuppliedHere := false
  finiteFutureDistinctFibreSuppliedHere := false
  concreteFutureCapacityBoundInstantiatedHere := false

structure FutureSafetyBoundary where
  sharedCurrentNonDescentShape : Bool
  sharedFutureCapacityTheoremAvailable : Bool
  currentNonDescentImpliesFutureDistinctionAutomatically : Bool
  sharedShapeImpliesSharedPhysicalMechanism : Bool
  deriving Repr

def canonicalBoundary : FutureSafetyBoundary where
  sharedCurrentNonDescentShape := true
  sharedFutureCapacityTheoremAvailable := true
  currentNonDescentImpliesFutureDistinctionAutomatically := false
  sharedShapeImpliesSharedPhysicalMechanism := false

end Integration.NonginTSFVTwistronicsFutureSafetyBridge
