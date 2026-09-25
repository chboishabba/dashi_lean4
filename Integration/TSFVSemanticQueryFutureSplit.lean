import Mathlib
import Integration.FutureSafeCoarseFibreCapacity

/-!
# TSFV/PNF semantic query future split

Finite mirror of the existing Agda two-world regression.  The state keeps both
the current query and the retained world.  A common "reveal provenance" action
preserves the world while refining the query, splitting two states that were
coarse-equal before the action.

This is a semantic dynamic fixture, not physical TSFV time evolution.
-/

namespace Integration.TSFVSemanticQueryFutureSplit

inductive World
  | canonical
  | impersonator
  deriving DecidableEq, Repr

inductive Query
  | coarseIdentity
  | provenance
  deriving DecidableEq, Repr

inductive Observation
  | neg
  | zer
  | pos
  deriving DecidableEq, Repr

abbrev State := Query × World

def observe : State → Observation
  | (.coarseIdentity, _) => .zer
  | (.provenance, .canonical) => .pos
  | (.provenance, .impersonator) => .neg

inductive Action
  | revealProvenance
  deriving DecidableEq, Repr

def step : State → Action → Option State
  | (.coarseIdentity, w), .revealProvenance => some (.provenance, w)
  | (.provenance, _), .revealProvenance => none

def canonicalBefore : State := (.coarseIdentity, .canonical)
def impersonatorBefore : State := (.coarseIdentity, .impersonator)
def canonicalAfter : State := (.provenance, .canonical)
def impersonatorAfter : State := (.provenance, .impersonator)

theorem current_observations_agree :
    observe canonicalBefore = observe impersonatorBefore := rfl

theorem canonical_reveal :
    step canonicalBefore .revealProvenance = some canonicalAfter := rfl

theorem impersonator_reveal :
    step impersonatorBefore .revealProvenance = some impersonatorAfter := rfl

theorem future_observations_differ :
    observe canonicalAfter ≠ observe impersonatorAfter := by decide

def representative : Fin 2 → State
  | ⟨0, _⟩ => canonicalBefore
  | ⟨1, _⟩ => impersonatorBefore

theorem representatives_distinct :
    representative (0 : Fin 2) ≠ representative (1 : Fin 2) := by decide

structure Boundary where
  proofBearingDynamicShapeMirrored : Bool
  sameCurrentObservation : Bool
  commonRevealAction : Bool
  futureObservationSplit : Bool
  physicalTSFVRealizationConstructed : Bool
  semanticActionIsPhysicalTimeEvolution : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  proofBearingDynamicShapeMirrored := true
  sameCurrentObservation := true
  commonRevealAction := true
  futureObservationSplit := true
  physicalTSFVRealizationConstructed := false
  semanticActionIsPhysicalTimeEvolution := false

end Integration.TSFVSemanticQueryFutureSplit
