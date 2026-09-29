import RequestProject.QuantumMereologySelection
import Integration.LeastSufficient

/-!
# Quantum-mereology observer bridge

This is a cross-module DASHI inference. It does not attribute the observer
theorems to Carroll--Singh, Cao--Carroll--Michalakis, or Pasqualini--Fortin.

For real-valued downstream consumers, the quantum-mereology criterion observer
uses exactly the existing Integration.LeastSufficient fibre-constancy notion.
-/

namespace QuantumMereology

namespace ObserverBridge

open Integration.LeastSufficient

structure RealCriterionConsumerSurface
    {W : BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) where
  Surface : Type
  observeCriterion : P.Candidate → Surface
  consumer : P.Candidate → ℝ

def RealCriterionConsumerSurface.Sufficient
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : RealCriterionConsumerSurface P) : Prop :=
  Integration.LeastSufficient.Sufficient S.observeCriterion S.consumer

theorem sufficient_iff_refines_canonical_consumer
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : RealCriterionConsumerSurface P) :
    S.Sufficient ↔
      Integration.LeastSufficient.Refines S.observeCriterion S.consumer :=
  Integration.LeastSufficient.sufficient_iff_refines _ _

theorem sufficient_criterion_refines_canonical_consumer
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : RealCriterionConsumerSurface P)
    (h : S.Sufficient) :
    Integration.LeastSufficient.Refines S.observeCriterion S.consumer :=
  Integration.LeastSufficient.canonical_least
    S.observeCriterion S.consumer h

structure RealCriterionCollision
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : RealCriterionConsumerSurface P) where
  left right : P.Candidate
  sameCriterion : S.observeCriterion left = S.observeCriterion right
  differentOutcome : S.consumer left ≠ S.consumer right

theorem realCriterionCollisionBlocksSufficiency
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    {S : RealCriterionConsumerSurface P}
    (collision : RealCriterionCollision S) :
    ¬ S.Sufficient := by
  intro sufficient
  exact collision.differentOutcome
    (sufficient collision.left collision.right collision.sameCriterion)

theorem realCriterionCollisionBlocksCanonicalRefinement
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    {S : RealCriterionConsumerSurface P}
    (collision : RealCriterionCollision S) :
    ¬ Integration.LeastSufficient.Refines
        S.observeCriterion S.consumer := by
  intro refines
  have sufficient :
      Integration.LeastSufficient.Sufficient
        S.observeCriterion S.consumer :=
    (Integration.LeastSufficient.sufficient_iff_refines
      S.observeCriterion S.consumer).2 refines
  exact realCriterionCollisionBlocksSufficiency collision sufficient

end ObserverBridge

end QuantumMereology
