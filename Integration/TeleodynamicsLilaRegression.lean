import Integration.TeleodynamicsLila
import Integration.TeleodynamicsExceptionalPrior

namespace Integration.TeleodynamicsLilaRegression

open Integration.TeleodynamicsLila
open Integration.TeleodynamicsExceptionalPrior

example : demoSharedOrthogonalQK.scoreAfter = demoSharedOrthogonalQK.scoreBefore :=
  sharedOrthogonalQKPreservesScore demoSharedOrthogonalQK

example : rankOneBiasedScore 3 0 5 7 = (3 : ℝ) := by
  simpa using rankOneBias_zero_scale (baseline := 3) (qProj := 5) (kProj := 7)

example : canonicalLilaBoundary.e8EquivarianceEstablished = false := rfl
example : canonicalLilaBoundary.leechMinimalVectorBasisEstablished = false := rfl

example : e8RootPrior.rootRank = 8 := rfl
example : e8RootPrior.rootCount = 240 := rfl
example : e6RepresentationCarrier.dimension = 27 := rfl
example : canonicalExceptionalBoundary.rootRankEqualsRepresentationDimension = false := rfl
example : canonicalExceptionalBoundary.dimensionMatchCreatesAction = false := rfl

end Integration.TeleodynamicsLilaRegression
