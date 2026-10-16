import Integration.ConsumerRelativeRepresentationParity

namespace Integration.ConsumerRelativeRepresentationParityRegression

open Integration.ScopedVerifierConsumerSufficiency
open Integration.ConsumerRelativeRepresentationParity

inductive State where
  | simple
  | elaborate
  | changed
  deriving DecidableEq, Repr

inductive Meaning where
  | base
  | changed
  deriving DecidableEq, Repr

inductive Complexity where
  | low
  | high
  deriving DecidableEq, Repr

inductive Answer where
  | base
  | changed
  deriving DecidableEq, Repr

private def meaning : State → Meaning
  | .simple => .base
  | .elaborate => .base
  | .changed => .changed

private def complexity : State → Complexity
  | .simple => .low
  | .elaborate => .high
  | .changed => .low

private def consumer : State → Answer
  | .simple => .base
  | .elaborate => .base
  | .changed => .changed

private def factor : ConsumerFactorization meaning consumer where
  decode
    | .base => .base
    | .changed => .changed
  factorizes := by intro x; cases x <;> rfl

private def expressive : ExpressiveAsymmetryWitness meaning complexity where
  leftState := .simple
  rightState := .elaborate
  sameSemantic := rfl
  complexitySeparates := by simp [complexity]

example : consumer expressive.leftState = consumer expressive.rightState :=
  expressiveComplexityCannotChangeFactorizedConsumer factor expressive

private def preserving : ConsumerPerturbation consumer where
  actState
    | .simple => .elaborate
    | .elaborate => .simple
    | .changed => .changed
  actOutcome := id
  commutes := by intro x; cases x <;> rfl

example : ConsumerInvariant preserving := by
  intro x
  cases x <;> rfl

end Integration.ConsumerRelativeRepresentationParityRegression
