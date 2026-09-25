import Mathlib
import Integration.NonginOnePointOneArmyRefinement
import Integration.FutureSafeCoarseFibreCapacity

namespace Integration.NonginOnePointOneFutureSplit

inductive Visibility
  | hidden
  | surfaced
  deriving DecidableEq, Repr

abbrev State :=
  Visibility ×
    Integration.NonginOnePointOneArmyRefinement.OnePointOneCarrier
      Integration.NonginOnePointOneArmyRefinement.Base1
      Integration.NonginOnePointOneArmyRefinement.Frame2

inductive Observation
  | commonOnePointZero
  | immersedFrame
  | observingFrame
  deriving DecidableEq, Repr

def observe : State → Observation
  | (.hidden, _) => .commonOnePointZero
  | (.surfaced, (.sharedSituation, .immersed)) => .immersedFrame
  | (.surfaced, (.sharedSituation, .frameAware)) => .observingFrame

inductive Action
  | surfaceFrame
  deriving DecidableEq, Repr

def step : State → Action → Option State
  | (.hidden, state), .surfaceFrame => some (.surfaced, state)
  | (.surfaced, _), .surfaceFrame => none

def immersedBefore : State := (.hidden, (.sharedSituation, .immersed))
def awareBefore : State := (.hidden, (.sharedSituation, .frameAware))
def immersedAfter : State := (.surfaced, (.sharedSituation, .immersed))
def awareAfter : State := (.surfaced, (.sharedSituation, .frameAware))

theorem current_collision : observe immersedBefore = observe awareBefore := rfl
theorem immersed_step : step immersedBefore .surfaceFrame = some immersedAfter := rfl
theorem aware_step : step awareBefore .surfaceFrame = some awareAfter := rfl
theorem future_split : observe immersedAfter ≠ observe awareAfter := by decide

structure Boundary where
  proofBearingDynamicShapeMirrored : Bool
  onePointZeroCollision : Bool
  commonSurfaceAction : Bool
  futureSplit : Bool
  literalTenPercentPerformanceLaw : Bool
  universalCognitiveSuperiorityClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  proofBearingDynamicShapeMirrored := true
  onePointZeroCollision := true
  commonSurfaceAction := true
  futureSplit := true
  literalTenPercentPerformanceLaw := false
  universalCognitiveSuperiorityClaimed := false

end Integration.NonginOnePointOneFutureSplit
