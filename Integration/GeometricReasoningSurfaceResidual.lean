import Mathlib

/-!
# Geometric surface plus dependent residual routing

A compact geometric surface may be sufficient for some consumers while a
history-, magnitude-, orientation-, or composition-sensitive consumer needs a
dependent residual.  This module types that distinction and leaves concrete
non-descent proofs to the consumer that owns the collision.
-/

namespace Integration.GeometricReasoningSurfaceResidual

universe u v w

structure GeometricSurfaceCode (State : Type u) (Surface : Type v) where
  surface : State → Surface
  Residual : Surface → Type w
  residual : (state : State) → Residual (surface state)
  reopen : (s : Surface) → Residual s → State
  reopenExact : ∀ state, reopen (surface state) (residual state) = state
  provenance : String

inductive GeometricConsumerClass
  | surfaceOnly
  | selectedResidual
  | fullState
  deriving DecidableEq, Repr

structure SurfaceConsumerFactors
    {State : Type u} {Surface : Type v} {Output : Type w}
    (code : GeometricSurfaceCode State Surface)
    (consumer : State → Output) where
  consumeSurface : Surface → Output
  factors : ∀ state, consumer state = consumeSurface (code.surface state)

structure SurfaceCollision
    {State : Type u} {Surface : Type v} {Output : Type w}
    (surface : State → Surface)
    (consumer : State → Output) where
  left : State
  right : State
  sameSurface : surface left = surface right
  differentConsumer : consumer left ≠ consumer right

structure Boundary where
  dependentResidualTyped : Bool
  exactReopenRequired : Bool
  surfaceOnlyConsumerTyped : Bool
  collisionWitnessTyped : Bool
  genericCollisionAutoPromotedToUniversalNonDescent : Bool
  geometricSurfaceAutomaticallyComplete : Bool
  residualAvailabilityAutomaticallyProvesNecessity : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  dependentResidualTyped := true
  exactReopenRequired := true
  surfaceOnlyConsumerTyped := true
  collisionWitnessTyped := true
  genericCollisionAutoPromotedToUniversalNonDescent := false
  geometricSurfaceAutomaticallyComplete := false
  residualAvailabilityAutomaticallyProvesNecessity := false

end Integration.GeometricReasoningSurfaceResidual
