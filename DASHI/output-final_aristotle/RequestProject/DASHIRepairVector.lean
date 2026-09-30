/-!
DASHI multi-consumer repair vector.

A modeled repair can improve one consumer while regressing another. This
module prevents an overall "acceptable for review" conclusion unless no
checked consumer regresses and at least one checked consumer improves.
Unchecked consumers remain explicit. This is not edit authority.
-/
import RequestProject.DASHIScopedSoftTyping

namespace DASHI.ContextIndexedOntology

inductive RepairOutcome
  | improved | preserved | regressed | unchecked
  deriving DecidableEq, Repr

structure ConsumerRepairResult where
  consumerRef : String
  outcome : RepairOutcome
  preservationWitnessRef : Option String
  dischargedObligationRefs : List String
  newObligationRefs : List String
  deriving Repr

def noRegression : List ConsumerRepairResult → Prop
  | [] => True
  | r :: rs => r.outcome ≠ .regressed ∧ noRegression rs

def someImprovement : List ConsumerRepairResult → Prop
  | [] => False
  | r :: rs => r.outcome = .improved ∨ someImprovement rs

structure RepairVector where
  repairRef : String
  results : List ConsumerRepairResult
  noCheckedRegressions : noRegression results
  atLeastOneImprovement : someImprovement results

theorem RepairVector.reviewableHasNoCheckedRegression
    (v : RepairVector) :
    noRegression v.results :=
  v.noCheckedRegressions

theorem RepairVector.reviewableHasImprovement
    (v : RepairVector) :
    someImprovement v.results :=
  v.atLeastOneImprovement

/-- Explicitly unchecked consumers are not silently promoted to preserved. -/
theorem uncheckedNePreserved :
    RepairOutcome.unchecked ≠ RepairOutcome.preserved := by
  intro h
  cases h

end DASHI.ContextIndexedOntology
