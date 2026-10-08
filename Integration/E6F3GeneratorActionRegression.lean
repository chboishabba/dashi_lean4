import Integration.E6F3GeneratorAction

namespace Integration.E6F3GeneratorActionRegression

open Integration.E6F3GeneratorAction

example : ∀ g u v, symplectic4 (liftAction g u) (liftAction g v) = -(symplectic4 u v) :=
  multiplier_minus_one_all

example : ∀ g u v, symplectic4 u v = 0 →
    wedgePrimitiveCoordinates (liftAction g u) (liftAction g v) =
      primitiveAction g (wedgePrimitiveCoordinates u v) :=
  wedge_covariance_all

example : ∀ g p,
    primitiveToStandard (primitiveAction g p) = weylAction g (primitiveToStandard p) :=
  standard_intertwining_all

example : canonicalBoundary.groupClosureOrder51840Paid = false := rfl
example : canonicalBoundary.projectiveKernelPlusMinusIPaid = false := rfl

end Integration.E6F3GeneratorActionRegression
