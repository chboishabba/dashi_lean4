import Mathlib

/-!
# Future-safe coarse-fibre capacity

Lean mirror of the relation-level capacity result: for a declared canonical
future-equivalence relation, a residual that is safe on one coarse fibre must
separate representatives that are not future-equivalent.

This file keeps the action-system construction abstract; the Agda core owns the
full proof-bearing dynamic trace machinery.
-/

namespace Integration.FutureSafeCoarseFibreCapacity

def InjectiveOnRepresentatives
    {State Residual : Type}
    {k : Nat}
    (representative : Fin k → State)
    (residual : State → Residual) : Prop :=
  Function.Injective (fun i => residual (representative i))

structure FutureSafePair
    {State Coarse Residual : Type}
    (FutureEq : State → State → Prop)
    (coarsen : State → Coarse)
    (residual : State → Residual) : Prop where
  safe :
    ∀ {left right},
      coarsen left = coarsen right →
      residual left = residual right →
      FutureEq left right

structure FiniteFutureDistinctFibre
    {State Coarse : Type}
    (k : Nat)
    (FutureEq : State → State → Prop)
    (coarsen : State → Coarse) where
  representative : Fin k → State
  fibreClass : Coarse
  inSameFibre : ∀ i, coarsen (representative i) = fibreClass
  futureEquivalentIndicesEqual :
    ∀ {i j}, FutureEq (representative i) (representative j) → i = j

theorem safe_residual_injective_on_future_classes
    {State Coarse Residual : Type}
    {k : Nat}
    {FutureEq : State → State → Prop}
    {coarsen : State → Coarse}
    {residual : State → Residual}
    (safe : FutureSafePair FutureEq coarsen residual)
    (fibre : FiniteFutureDistinctFibre k FutureEq coarsen) :
    InjectiveOnRepresentatives fibre.representative residual := by
  intro i j hres
  apply fibre.futureEquivalentIndicesEqual
  apply safe.safe
  · exact (fibre.inSameFibre i).trans (fibre.inSameFibre j).symm
  · exact hres

structure FutureSafeCoarseFibreCapacityBoundary where
  futureDistinctClassesRequireDistinctSafeResidualCodes : Bool
  retainOnlyFutureRelevantDistinctions : Bool
  everyFineDifferenceMustBeRetained : Bool
  sharedTheoremCreatesDomainMechanism : Bool
  deriving Repr

def canonicalBoundary : FutureSafeCoarseFibreCapacityBoundary where
  futureDistinctClassesRequireDistinctSafeResidualCodes := true
  retainOnlyFutureRelevantDistinctions := true
  everyFineDifferenceMustBeRetained := false
  sharedTheoremCreatesDomainMechanism := false

end Integration.FutureSafeCoarseFibreCapacity
