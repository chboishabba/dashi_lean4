import Integration.AlbertF4CompatibilityTerminal

namespace Integration.AlbertF4CompatibilityTerminalRegression

open Integration.AlbertF4CompatibilityTerminal
open Integration.AlbertJordanAutomorphism
open Integration.AlbertStructureTransport
open Integration.F4MinusculeOnePlus26

variable {J : Type*} [AddCommGroup J] [Module ℝ J] [Module.Finite ℝ J]

example : canonicalBoundary.terminalCompatibilityObjectTyped = true := rfl
example : canonicalBoundary.unitSameObjectRequirementTyped = true := rfl
example : canonicalBoundary.traceSameObjectRequirementTyped = true := rfl
example : canonicalBoundary.fourFoldedAlbertPreservationRequirementsTyped = true := rfl
example : canonicalBoundary.compatibilityCompilesToJordanAutomorphisms = true := rfl
example : canonicalBoundary.actualTracelessCarrierIdentificationCompiles = true := rfl
example : canonicalBoundary.fullF4RecognitionTypedSeparately = true := rfl
example : canonicalBoundary.terminalCompatibilityPaidHere = false := rfl
example : canonicalBoundary.fullF4RecognitionPaidHere = false := rfl

end Integration.AlbertF4CompatibilityTerminalRegression
