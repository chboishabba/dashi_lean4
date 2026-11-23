import Integration.AlbertLinearMinusculeTransport

namespace Integration.AlbertLinearMinusculeTransportRegression

open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6MinusculeWeightModule
open Integration.AlbertLinearMinusculeTransport

variable {J : Type*} [AddCommGroup J] [Module ℝ J] [Module.Finite ℝ J]

example (hJ : Module.finrank ℝ J = 27) : Nonempty (J ≃ₗ[ℝ] MinusculeModule) :=
  linear_transport_exists hJ

example (e : J ≃ₗ[ℝ] MinusculeModule) :
    Function.Injective (transportedWeightLine e) :=
  transportedWeightLine_injective e

example : canonicalBoundary.linearEquivalenceFromFinrank27Paid = true := rfl
example : canonicalBoundary.twentySevenDistinctTransportedLinesPaid = true := rfl
example : canonicalBoundary.conjugatedLinearE6ActionTyped = true := rfl
example : canonicalBoundary.exceptionalJordanCompatibilityTyped = true := rfl
example : canonicalBoundary.exceptionalJordanCompatibilityPaidHere = false := rfl

end Integration.AlbertLinearMinusculeTransportRegression
