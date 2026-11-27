import Integration.TeleodynamicsLocalLawTopology

namespace Integration.TeleodynamicsLocalLawTopologyRegression
open Integration.TeleodynamicsLocalLawTopology

example : canonicalBoundary.sameTopologyDifferentLocalLawCanChangeFuture = true := rfl
example : canonicalBoundary.topologyDeterminesLocalTransitionByDefinition = false := rfl
example : canonicalBoundary.sameArchitectureSimilarityDeterminesLocalLaw = false := rfl
example : canonicalBoundary.iitMatchedGateScanReportedInSibling = true := rfl

example : recurrentStep xorB counterexampleState ≠ recurrentStep orB counterexampleState :=
  xorOrCounterexample

end Integration.TeleodynamicsLocalLawTopologyRegression
