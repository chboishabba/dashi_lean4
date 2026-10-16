import Integration.ConsumerRelativeRepresentationParity
import Integration.ScopedVerifierEvaluationProtocol

namespace Integration.ScopedVerifierSameObjectEvaluation

open Integration.ConsumerRelativeRepresentationParity
open Integration.ScopedVerifierEvaluationProtocol

structure HeldOutProtocol where
  targetHeldOut : Bool
  contextHeldOut : Bool
  modelHeldOut : Bool
  checkpointHeldOut : Bool
  matchedPairingDeclared : Bool
  dynamicTraceRequired : Bool
  targetRealizationRequired : Bool
  protocolReference : String
  deriving Repr

structure SameObjectHeldOutEvaluation
    {X O₁ O₂ C : Type}
    (candidateObserve : X → O₁)
    (baselineObserve : X → O₂)
    (consumer : X → C)
    (Case Intervention : Type) where
  candidateEligibility : EligibleRepresentation candidateObserve consumer
  baselineEligibility : EligibleRepresentation baselineObserve consumer
  evaluation : EvaluationReceipt
  protocol : HeldOutProtocol

  candidateCase : Case
  baselineCase : Case
  sameCase : candidateCase = baselineCase

  candidateIntervention : Intervention
  baselineIntervention : Intervention
  sameIntervention : candidateIntervention = baselineIntervention

  targetHoldoutPaid : protocol.targetHeldOut = true
  contextHoldoutPaid : protocol.contextHeldOut = true
  modelHoldoutPaid : protocol.modelHeldOut = true
  checkpointHoldoutPaid : protocol.checkpointHeldOut = true
  matchedPairingPaid : protocol.matchedPairingDeclared = true
  dynamicTracePaid : protocol.dynamicTraceRequired = true
  targetRealizationPaid : protocol.targetRealizationRequired = true

  sameTaskSetPaid : evaluation.pair.sameTaskSet = true
  sameToolAccessPaid : evaluation.pair.sameToolAccess = true
  sameContextBudgetPaid : evaluation.pair.sameContextBudget = true
  sameComputeAccountingPaid : evaluation.pair.sameComputeAccounting = true
  sameDeclaredConsumersPaid : evaluation.pair.sameDeclaredConsumers = true
  sameValidatorScopePaid : evaluation.pair.sameValidatorScope = true


theorem candidateAdmissibilityPaid
    {X O₁ O₂ C Case Intervention : Type}
    {candidateObserve : X → O₁} {baselineObserve : X → O₂}
    {consumer : X → C}
    (r : SameObjectHeldOutEvaluation candidateObserve baselineObserve consumer Case Intervention) :
    r.candidateEligibility.Admissible :=
  r.candidateEligibility.admissibilityReceipt


theorem candidateConsumerAdequacyPaid
    {X O₁ O₂ C Case Intervention : Type}
    {candidateObserve : X → O₁} {baselineObserve : X → O₂}
    {consumer : X → C}
    (r : SameObjectHeldOutEvaluation candidateObserve baselineObserve consumer Case Intervention) :
    r.candidateEligibility.ConsumerAdequate :=
  r.candidateEligibility.consumerAdequacyReceipt


theorem baselineAdmissibilityPaid
    {X O₁ O₂ C Case Intervention : Type}
    {candidateObserve : X → O₁} {baselineObserve : X → O₂}
    {consumer : X → C}
    (r : SameObjectHeldOutEvaluation candidateObserve baselineObserve consumer Case Intervention) :
    r.baselineEligibility.Admissible :=
  r.baselineEligibility.admissibilityReceipt


theorem baselineConsumerAdequacyPaid
    {X O₁ O₂ C Case Intervention : Type}
    {candidateObserve : X → O₁} {baselineObserve : X → O₂}
    {consumer : X → C}
    (r : SameObjectHeldOutEvaluation candidateObserve baselineObserve consumer Case Intervention) :
    r.baselineEligibility.ConsumerAdequate :=
  r.baselineEligibility.consumerAdequacyReceipt

structure SameObjectEvaluationBoundary where
  eligibilityRequiredBeforeEmpiricalRanking : Bool
  eligibilityAloneImpliesMatchedHeldOutExperiment : Bool
  sameCandidateBaselineCaseRequired : Bool
  sameCandidateBaselineInterventionRequired : Bool
  completeHeldOutAxisCoverageRequired : Bool
  matchedPairingRequired : Bool
  dynamicTraceRequired : Bool
  targetRealizationRequired : Bool
  consumerAdequacyImpliesWorldCompleteness : Bool
  matchedHeldOutFitImpliesMechanism : Bool
  equalScalarScoreImpliesTheoryIdentity : Bool
  deriving DecidableEq, Repr


def canonicalBoundary : SameObjectEvaluationBoundary :=
  ⟨true, false, true, true, true, true, true, true, false, false, false⟩

end Integration.ScopedVerifierSameObjectEvaluation
