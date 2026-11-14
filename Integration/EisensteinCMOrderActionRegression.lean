import Integration.EisensteinCMOrderActionExact

/-!
RED-first regression for the algebraic CM step.

The target is deliberately a ring action, not an injective CM-order embedding:
faithfulness on the selected rational-point group is an additional geometric
payment and must not be inferred from the quadratic relation alone.
-/

namespace Integration.EisensteinCMOrderActionRegression

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroCMConcreteExact
open Integration.EisensteinCMOrderActionExact

example : EisensteinQA →+*
    AddMonoid.End eisensteinJZeroCurve.Point :=
  eisensteinOrderAction

example : eisensteinOrderAction (QuadraticAlgebra.omega : EisensteinQA) =
    eisensteinCMEndomorphism :=
  eisensteinOrderAction_omega

example : rationalPointActionFaithfulPaid = false := rfl
example : geometricCMEmbeddingPaid = false := rfl

end Integration.EisensteinCMOrderActionRegression
