import Dashi.Biology.PersuasionTransmissionTruthBoundaryExact

namespace Dashi.Biology.PersuasionTransmissionTruthBoundaryRegression

open Dashi.Biology.PersuasionTransmissionTruthBoundaryExact

example : canonicalTruthTransmissionBoundary.persuasionCollapsedWithTransmission = false := rfl
example : canonicalTruthTransmissionBoundary.positiveEmotionCreatesTruthAuthority = false := rfl
example : canonicalTruthTransmissionBoundary.truthIntentAdvantageRepresented = true := rfl
example : canonicalTruthTransmissionBoundary.controlledExperimentUniversalizesToPlatforms = false := rfl

#check AdmittedPersuasionSource.fay2026PaysControlledExperimentOutcome

example : AdmittedPersuasionSource .fay2026ControlledExperimentOutcome :=
  .fay2026PaysControlledExperimentOutcome

end Dashi.Biology.PersuasionTransmissionTruthBoundaryRegression
