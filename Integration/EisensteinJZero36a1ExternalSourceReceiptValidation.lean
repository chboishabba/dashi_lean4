import Integration.EisensteinJZero36a1ExternalSourceReceipt

/-! RED-first provenance validation for externally acquired 36a1 metadata. -/

namespace Integration.EisensteinJZero36a1ExternalSourceReceiptValidation

open Integration.EisensteinJZero36a1ExternalSourceReceipt

example : receipt.externalCurveLabelObserved = true := rfl
example : receipt.externalEquationObserved = true := rfl
example : receipt.externalConductor36Observed = true := rfl
example : receipt.externalDiscriminantFormulaObserved = true := rfl
example : receipt.externalF2SingularityExampleObserved = true := rfl
example : receipt.externalSourceIsProofAuthority = false := rfl
example : receipt.mathlibInfrastructureAttributedToExternalSource = false := rfl
example : receipt.dashiSpecializationAttributedToExternalSource = false := rfl

end Integration.EisensteinJZero36a1ExternalSourceReceiptValidation
