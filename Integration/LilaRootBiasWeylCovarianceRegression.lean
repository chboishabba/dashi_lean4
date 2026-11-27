import Integration.LilaRootBiasWeylCovariance

namespace Integration.LilaRootBiasWeylCovarianceRegression

open Integration.LilaRootBiasWeylCovariance

example : canonicalBoundary.rankOneBiasCovarianceTheoremPaid = true := rfl
example : canonicalBoundary.requiresProjectionIntertwinerForModelEquivariance = true := rfl
example : canonicalBoundary.rootCodebookAlonePaysModelWeylEquivariance = false := rfl
example : canonicalBoundary.learnedHeadScaleBreaksCovarianceAutomatically = false := rfl

end Integration.LilaRootBiasWeylCovarianceRegression
