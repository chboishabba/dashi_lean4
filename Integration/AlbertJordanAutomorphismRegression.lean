import Integration.AlbertJordanAutomorphism

namespace Integration.AlbertJordanAutomorphismRegression

open Integration.AlbertScalarTraceless
open Integration.AlbertJordanAutomorphism

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

example (A : AlbertStructure J) (g : JordanAutomorphism A)
    (x : Traceless A.traceUnit) :
    A.traceUnit.trace (g.toLinearEquiv x.1) = 0 :=
  g.maps_traceless A x

example : canonicalBoundary.tracelessActionRestrictionPaid = true := rfl
example : canonicalBoundary.f4AutomorphismRecognitionPaidHere = false := rfl
example : canonicalBoundary.e6UnitStabilizerRecognitionPaidHere = false := rfl
example : canonicalBoundary.dimension52CreatesF4 = false := rfl

end Integration.AlbertJordanAutomorphismRegression
