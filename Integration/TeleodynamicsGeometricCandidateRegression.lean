import Integration.TeleodynamicsGeometricCandidateBridge

namespace Integration.TeleodynamicsGeometricCandidateRegression

open Integration.TeleodynamicsGeometricCandidateBridge
open Integration.GeometricReasoningCandidateSelection

example : reasoningCandidate .noPrior = .unstructuredBaseline := rfl
example : reasoningCandidate .e8Root = .lilaE8RootPrior := rfl
example : reasoningCandidate .f4Root = .genericFiniteActionGeometry := rfl
example : canonicalBoundary.bestCandidateCreatesMechanism = false := rfl
example : canonicalBoundary.cosineSimilarityAloneClosesSelection = false := rfl

end Integration.TeleodynamicsGeometricCandidateRegression
