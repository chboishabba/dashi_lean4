import Mathlib

/-!
# Weighted-consensus structural endpoint

This pays the graph-theoretic half of the generic radiant-coupling consensus
claim.  A state that agrees across every positive-weight edge is globally
constant on every positive-edge connected component.

This is deliberately not an ODE convergence theorem: connectivity alone does
not prove that a trajectory converges to an edgewise stationary state.
-/

namespace Integration.TeleodynamicsConsensus

universe u

variable {ι : Type u}

/-- Reachability using only strictly positive directed weights. -/
inductive PositivePath (w : ι → ι → ℝ) (root : ι) : ι → Prop
  | refl : PositivePath w root root
  | step {u v : ι} : PositivePath w root u → 0 < w u v → PositivePath w root v

/-- Every node is reachable from one root by positive-weight edges. -/
def PositiveConnectedAt (w : ι → ι → ℝ) (root : ι) : Prop :=
  ∀ node, PositivePath w root node

theorem positivePath_propagates_agreement
    {w : ι → ι → ℝ} {x : ι → ℝ} {root node : ι}
    (path : PositivePath w root node)
    (edgeAgree : ∀ i j, 0 < w i j → x i = x j) :
    x root = x node := by
  induction path with
  | refl => rfl
  | @step u v prior positive ih =>
      exact ih.trans (edgeAgree u v positive)

theorem connected_edgewise_agreement_implies_consensus
    {w : ι → ι → ℝ} {x : ι → ℝ} {root : ι}
    (connected : PositiveConnectedAt w root)
    (edgeAgree : ∀ i j, 0 < w i j → x i = x j) :
    ∀ node, x node = x root := by
  intro node
  exact (positivePath_propagates_agreement (connected node) edgeAgree).symm

/-- Exact cut for the remaining analytic convergence problem. -/
structure ConsensusLimitReceipt (w : ι → ι → ℝ) where
  root : ι
  limitState : ι → ℝ
  positiveConnected : PositiveConnectedAt w root
  edgewiseStationaryAgreement : ∀ i j, 0 < w i j → limitState i = limitState j
  trajectoryConvergesToLimit : Prop
  convergenceReceipt : trajectoryConvergesToLimit

 theorem consensusLimitReceipt_gives_pairwise_consensus
    {w : ι → ι → ℝ} (receipt : ConsensusLimitReceipt w) :
    ∀ i j, receipt.limitState i = receipt.limitState j := by
  intro i j
  have hi := connected_edgewise_agreement_implies_consensus
    receipt.positiveConnected receipt.edgewiseStationaryAgreement i
  have hj := connected_edgewise_agreement_implies_consensus
    receipt.positiveConnected receipt.edgewiseStationaryAgreement j
  exact hi.trans hj.symm

structure Boundary where
  positiveEdgeReachabilityTyped : Bool
  connectedStationaryStateIsConsensus : Bool
  convergenceReceiptSeparated : Bool
  connectivityAloneProvesFlowConvergence : Bool
  consensusCreatesNonlocalPhysicalTransmission : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  positiveEdgeReachabilityTyped := true
  connectedStationaryStateIsConsensus := true
  convergenceReceiptSeparated := true
  connectivityAloneProvesFlowConvergence := false
  consensusCreatesNonlocalPhysicalTransmission := false

end Integration.TeleodynamicsConsensus
