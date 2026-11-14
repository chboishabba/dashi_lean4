import Integration.ScopedVerifierConsumerSufficiency

namespace Integration.ScopedVerifierConsumerSufficiencyRegression

open Integration.ScopedVerifierConsumerSufficiency

example : canonicalBoundary.consumerRelativeAdequacyRequired = true := rfl
example : canonicalBoundary.coarseCollisionAloneImpliesFailure = false := rfl
example : canonicalBoundary.validatorPassImpliesAllConsumerSufficiency = false := rfl
example : canonicalBoundary.refinementRequiresConsumerFactorization = true := rfl

end Integration.ScopedVerifierConsumerSufficiencyRegression
