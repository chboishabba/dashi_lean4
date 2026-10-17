import Integration.TeleodynamicsConsensus

namespace Integration.TeleodynamicsConsensusRegression

open Integration.TeleodynamicsConsensus

example {ι : Type*} {w : ι → ι → ℝ} {x : ι → ℝ} {root node : ι}
    (path : PositivePath w root node)
    (edgeAgree : ∀ i j, 0 < w i j → x i = x j) :
    x root = x node :=
  positivePath_propagates_agreement path edgeAgree

example {ι : Type*} {w : ι → ι → ℝ} {x : ι → ℝ} {root : ι}
    (connected : PositiveConnectedAt w root)
    (edgeAgree : ∀ i j, 0 < w i j → x i = x j) :
    ∀ node, x node = x root :=
  connected_edgewise_agreement_implies_consensus connected edgeAgree

example : canonicalBoundary.connectedStationaryStateIsConsensus = true := rfl
example : canonicalBoundary.connectivityAloneProvesFlowConvergence = false := rfl

end Integration.TeleodynamicsConsensusRegression
