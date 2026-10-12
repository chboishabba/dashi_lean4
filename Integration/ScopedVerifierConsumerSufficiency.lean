import Integration.ScopedVerifierArtifact

namespace Integration.ScopedVerifierConsumerSufficiency

open Integration.ScopedVerifierArtifact

structure ConsumerNonDescentWitness {X O C : Type}
    (observe : X → O) (consumer : X → C) where
  leftState : X
  rightState : X
  observationCollision : observe leftState = observe rightState
  consumerSeparates : consumer leftState ≠ consumer rightState

structure ConsumerFactorization {X O C : Type}
    (observe : X → O) (consumer : X → C) where
  decode : O → C
  factorizes : ∀ x, decode (observe x) = consumer x

theorem factorizedConsumersEqual {X O C : Type}
    {observe : X → O} {consumer : X → C}
    (w : ConsumerNonDescentWitness observe consumer)
    (f : ConsumerFactorization observe consumer) :
    consumer w.leftState = consumer w.rightState := by
  calc
    consumer w.leftState = f.decode (observe w.leftState) := (f.factorizes w.leftState).symm
    _ = f.decode (observe w.rightState) := congrArg f.decode w.observationCollision
    _ = consumer w.rightState := f.factorizes w.rightState

theorem collisionBlocksFactorization {X O C : Type}
    {observe : X → O} {consumer : X → C}
    (w : ConsumerNonDescentWitness observe consumer) :
    ¬ ConsumerFactorization observe consumer := by
  intro f
  exact w.consumerSeparates (factorizedConsumersEqual w f)

structure ValidatorConsumerAdequacy {X O C : Type}
    (V : ScopedValidator X) (observe : X → O) (consumer : X → C) where
  consumerFactorization : ConsumerFactorization observe consumer

 theorem validatorCollisionBlocksAdequacy {X O C : Type}
    {V : ScopedValidator X} {observe : X → O} {consumer : X → C}
    (w : ConsumerNonDescentWitness observe consumer) :
    ¬ ValidatorConsumerAdequacy V observe consumer := by
  intro a
  exact collisionBlocksFactorization w a.consumerFactorization

structure ConsumerAdequateRefinement {X R C : Type}
    (refine : X → R) (consumer : X → C) where
  refinedFactorization : ConsumerFactorization refine consumer

theorem adequateRefinementMustSeparate {X O R C : Type}
    {coarse : X → O} {consumer : X → C} {refine : X → R}
    (w : ConsumerNonDescentWitness coarse consumer)
    (repair : ConsumerAdequateRefinement refine consumer) :
    refine w.leftState ≠ refine w.rightState := by
  intro h
  let refinedWitness : ConsumerNonDescentWitness refine consumer :=
    ⟨w.leftState, w.rightState, h, w.consumerSeparates⟩
  exact collisionBlocksFactorization refinedWitness repair.refinedFactorization

structure ConsumerSufficiencyBoundary where
  consumerRelativeAdequacyRequired : Bool
  coarseCollisionAloneImpliesFailure : Bool
  distinguishingConsumerCollisionBlocksDescent : Bool
  validatorPassImpliesAllConsumerSufficiency : Bool
  refinementRequiresConsumerFactorization : Bool
  adequateRefinementMustSeparateWitness : Bool
  nonginSiblingUsedAsConceptualDonorOnly : Bool
  deriving DecidableEq, Repr

def canonicalBoundary : ConsumerSufficiencyBoundary :=
  ⟨true, false, true, false, true, true, true⟩

end Integration.ScopedVerifierConsumerSufficiency
