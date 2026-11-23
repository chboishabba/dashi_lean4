import Integration.AlbertStructureTransport

namespace Integration.AlbertStructureTransportRegression

open Integration.AlbertStructureTransport
open Integration.AlbertJordanAutomorphism
open Integration.E6MinusculeWeightModule

variable {J V : Type*}
variable [AddCommGroup J] [Module ℝ J]
variable [AddCommGroup V] [Module ℝ V]

example (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V) : AlbertStructure V :=
  transportAlbertStructure A e

example (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V)
    (g : JordanAutomorphism A) :
    JordanAutomorphism (transportAlbertStructure A e) :=
  transportJordanAutomorphism A e g

example (A : AlbertStructure J) (e : J ≃ₗ[ℝ] V)
    (g : V ≃ₗ[ℝ] V) (h : PreservesTransportedAlbert A e g) :
    JordanAutomorphism (transportAlbertStructure A e) :=
  jordanAutomorphismOfPreserves A e g h

example : canonicalBoundary.fullAlbertStructureTransportPaid = true := rfl
example : canonicalBoundary.jordanAutomorphismTransportPaid = true := rfl
example : canonicalBoundary.minusculeModuleAlbertStructureExistsFromAnyActualAlbert27 = true := rfl
example : canonicalBoundary.exactE6CompatibilityPredicateTyped = true := rfl
example : canonicalBoundary.preservationReceiptCompilesToJordanAutomorphism = true := rfl
example : canonicalBoundary.e6CompatibilityCompilesToSimpleJordanAutomorphisms = true := rfl
example : canonicalBoundary.independentE6CompatibilityPaidHere = false := rfl

end Integration.AlbertStructureTransportRegression
