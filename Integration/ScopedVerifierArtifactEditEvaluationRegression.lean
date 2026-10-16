import Integration.ScopedVerifierArtifactEditEvaluation

namespace Integration.ScopedVerifierArtifactEditEvaluationRegression

open Integration.ScopedVerifierArtifactEditEvaluation

example : canonicalBoundary.sameArtifactIdentityRequired = true := rfl
example : canonicalBoundary.postEditValidationRequired = true := rfl
example : canonicalBoundary.futureSufficiencyRequired = true := rfl
example : canonicalBoundary.sameObjectHeldOutEvaluationRequired = true := rfl
example : canonicalBoundary.editReplayAloneCountsAsEvaluation = false := rfl
example : canonicalBoundary.futureSufficiencyAloneCountsAsEmpiricalWin = false := rfl

end Integration.ScopedVerifierArtifactEditEvaluationRegression
