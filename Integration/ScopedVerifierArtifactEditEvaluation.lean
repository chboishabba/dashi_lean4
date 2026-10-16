import Integration.ScopedVerifierArtifact
import Integration.ScopedVerifierSameObjectEvaluation

namespace Integration.ScopedVerifierArtifactEditEvaluation

open Integration.ScopedVerifierArtifact
open Integration.ScopedVerifierSameObjectEvaluation

structure ArtifactEditHeldOutEvaluation
    {Identity Body Residual X O₁ O₂ C Intervention : Type}
    (V : ScopedValidator (ArtifactState Identity Body Residual))
    (M : ArtifactFutureModel Body Residual)
    (before after : ArtifactState Identity Body Residual)
    (candidateObserve : X → O₁)
    (baselineObserve : X → O₂)
    (consumer : X → C) where
  transition : VerifiedArtifactTransition V before after
  futureSufficiency : ResidualFutureSufficiency M after
  evaluation : SameObjectHeldOutEvaluation
    candidateObserve baselineObserve consumer Identity Intervention
  candidateCaseMatchesBefore : evaluation.candidateCase = before.identity
  baselineCaseMatchesAfter : evaluation.baselineCase = after.identity


theorem editPreservesArtifactIdentity
    {Identity Body Residual X O₁ O₂ C Intervention : Type}
    {V : ScopedValidator (ArtifactState Identity Body Residual)}
    {M : ArtifactFutureModel Body Residual}
    {before after : ArtifactState Identity Body Residual}
    {candidateObserve : X → O₁}
    {baselineObserve : X → O₂}
    {consumer : X → C}
    (r : ArtifactEditHeldOutEvaluation V M before after candidateObserve baselineObserve consumer) :
    before.identity = after.identity :=
  sameArtifactIdentity r.transition


theorem heldOutCasesTrackSameArtifact
    {Identity Body Residual X O₁ O₂ C Intervention : Type}
    {V : ScopedValidator (ArtifactState Identity Body Residual)}
    {M : ArtifactFutureModel Body Residual}
    {before after : ArtifactState Identity Body Residual}
    {candidateObserve : X → O₁}
    {baselineObserve : X → O₂}
    {consumer : X → C}
    (r : ArtifactEditHeldOutEvaluation V M before after candidateObserve baselineObserve consumer) :
    r.evaluation.candidateCase = r.evaluation.baselineCase :=
  r.evaluation.sameCase


theorem candidateHeldOutCaseIsPostEditIdentity
    {Identity Body Residual X O₁ O₂ C Intervention : Type}
    {V : ScopedValidator (ArtifactState Identity Body Residual)}
    {M : ArtifactFutureModel Body Residual}
    {before after : ArtifactState Identity Body Residual}
    {candidateObserve : X → O₁}
    {baselineObserve : X → O₂}
    {consumer : X → C}
    (r : ArtifactEditHeldOutEvaluation V M before after candidateObserve baselineObserve consumer) :
    r.evaluation.candidateCase = after.identity := by
  calc
    r.evaluation.candidateCase = before.identity := r.candidateCaseMatchesBefore
    _ = after.identity := sameArtifactIdentity r.transition


theorem baselineHeldOutCaseIsPreEditIdentity
    {Identity Body Residual X O₁ O₂ C Intervention : Type}
    {V : ScopedValidator (ArtifactState Identity Body Residual)}
    {M : ArtifactFutureModel Body Residual}
    {before after : ArtifactState Identity Body Residual}
    {candidateObserve : X → O₁}
    {baselineObserve : X → O₂}
    {consumer : X → C}
    (r : ArtifactEditHeldOutEvaluation V M before after candidateObserve baselineObserve consumer) :
    r.evaluation.baselineCase = before.identity := by
  calc
    r.evaluation.baselineCase = after.identity := r.baselineCaseMatchesAfter
    _ = before.identity := (sameArtifactIdentity r.transition).symm

structure ArtifactEditEvaluationBoundary where
  sameArtifactIdentityRequired : Bool
  declaredEditSemanticsRequired : Bool
  postEditValidationRequired : Bool
  futureSufficiencyRequired : Bool
  sameObjectHeldOutEvaluationRequired : Bool
  editReplayAloneCountsAsEvaluation : Bool
  futureSufficiencyAloneCountsAsEmpiricalWin : Bool
  validatorPassAloneCountsAsArtifactIdentity : Bool
  deriving DecidableEq, Repr


def canonicalBoundary : ArtifactEditEvaluationBoundary :=
  ⟨true, true, true, true, true, false, false, false⟩

end Integration.ScopedVerifierArtifactEditEvaluation
