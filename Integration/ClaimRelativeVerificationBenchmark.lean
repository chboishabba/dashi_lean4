import Integration.ScopedVerifierSameObjectEvaluation

namespace Integration.ClaimRelativeVerificationBenchmark

open Integration.ScopedVerifierSameObjectEvaluation

/-!
Lean structural mirror of the claim-relative verification benchmark.

Authority boundary:
* Lean owns only the structures and equalities source-written here.
* Agda `HumanReviewCore` receipts are not imported or treated as Lean theorems.
* External 2026 verification/abstention papers remain external motivation only.
-/

structure SpecificationTranslationReceipt
    (Source Specification Consumer : Type) where
  source : Source
  specification : Specification
  consumer : Consumer
  translationAdequacyReference : String
  sourceReference : String
  specificationReference : String
  consumerReference : String
  deriving Repr

inductive WeakVerificationStatus where
  | weakPass
  | weakFail
  | weakUnknown
  | weakOutOfDomain
  deriving DecidableEq, Repr

structure WeakVerificationReceipt (Specification : Type) where
  checkedSpecification : Specification
  status : WeakVerificationStatus
  verifierReference : String
  evidenceReference : String
  deriving Repr

inductive EscalationTarget where
  | strongVerifier
  | evidenceAcquisition
  | executionOrSimulation
  | humanReview
  deriving DecidableEq, Repr

inductive EscalationPayload : EscalationTarget → Type
  | strongVerifierPayload
      (receiptReference : String) :
      EscalationPayload .strongVerifier
  | evidenceAcquisitionPayload
      (targetReference obligationReference : String) :
      EscalationPayload .evidenceAcquisition
  | executionOrSimulationPayload
      (receiptReference : String) :
      EscalationPayload .executionOrSimulation
  | humanReviewReferencePayload
      (reviewReceiptReference exactItemBindingReference : String) :
      EscalationPayload .humanReview

structure EscalationReceipt {Specification : Type}
    (weak : WeakVerificationReceipt Specification) where
  target : EscalationTarget
  payload : EscalationPayload target
  escalationReasonReference : String
  priorFrontierReference : String
  nextFrontierReference : String

structure FrontierAdvisoryReceipt where
  historyReference : String
  currentFrontierReference : String
  historyComplete : Bool
  advisoryReference : String
  advisoryOnly : Bool
  deriving DecidableEq, Repr

structure ClaimRelativeEvaluationPacket
    {X O₁ O₂ C Case Intervention : Type}
    (candidateObserve : X → O₁)
    (baselineObserve : X → O₂)
    (consumer : X → C)
    (Source Specification Consumer : Type) where
  translation : SpecificationTranslationReceipt Source Specification Consumer
  weakReceipt : WeakVerificationReceipt Specification
  weakChecksSameSpecification : weakReceipt.checkedSpecification = translation.specification
  frontierAdvisory : FrontierAdvisoryReceipt
  sameObjectEvaluation :
    SameObjectHeldOutEvaluation candidateObserve baselineObserve consumer Case Intervention
  validatorObservationReference : String
  consumerOutcomeReference : String
  packetReference : String

structure SelectiveVerificationScorecard where
  trialCount : Nat
  incorrectAcceptanceCount : Nat
  incorrectRejectionCount : Nat
  strongVerificationCount : Nat
  abstentionCount : Nat
  outOfDomainCount : Nat
  validatorSuccessConsumerFailureCount : Nat
  runtimeCostReference : String
  calibrationReference : String
  scorecardReference : String
  deriving DecidableEq, Repr

structure MatchedComparatorContract where
  sameTaskSet : Bool
  sameToolAccess : Bool
  sameContextBudget : Bool
  sameComputeAccounting : Bool
  sameDeclaredConsumer : Bool
  sameValidatorScope : Bool
  comparatorReference : String
  deriving DecidableEq, Repr

structure ClaimRelativeBenchmark
    {X O₁ O₂ C Case Intervention : Type}
    (candidateObserve : X → O₁)
    (baselineObserve : X → O₂)
    (consumer : X → C)
    (Source Specification Consumer : Type) where
  evaluation :
    ClaimRelativeEvaluationPacket
      candidateObserve baselineObserve consumer Source Specification Consumer
  comparator : MatchedComparatorContract
  sameTaskSetPaid : comparator.sameTaskSet = true
  sameToolAccessPaid : comparator.sameToolAccess = true
  sameContextBudgetPaid : comparator.sameContextBudget = true
  sameComputeAccountingPaid : comparator.sameComputeAccounting = true
  sameDeclaredConsumerPaid : comparator.sameDeclaredConsumer = true
  sameValidatorScopePaid : comparator.sameValidatorScope = true
  scorecard : SelectiveVerificationScorecard
  benchmarkReference : String

structure PairedActionAbstentionCase (Environment Task : Type) where
  environment : Environment
  shouldActTask : Task
  shouldAbstainTask : Task
  controlledPerturbationReference : String
  criticalActionReference : String
  pairReference : String
  deriving Repr

inductive ObservedActionDisposition where
  | acted
  | abstainedBeforeCriticalAction
  | abstainedAfterCriticalAction
  | failedWithoutDecision
  deriving DecidableEq, Repr

structure PairedActionAbstentionResult
    {Environment Task : Type}
    (pair : PairedActionAbstentionCase Environment Task) where
  shouldActObserved : ObservedActionDisposition
  shouldAbstainObserved : ObservedActionDisposition
  traceReference : String
  outcomeReference : String
  deriving Repr

def PairedCorrect
    {Environment Task : Type}
    {pair : PairedActionAbstentionCase Environment Task}
    (result : PairedActionAbstentionResult pair) : Prop :=
  result.shouldActObserved = .acted ∧
  result.shouldAbstainObserved = .abstainedBeforeCriticalAction

structure ClaimRelativeVerificationBenchmarkBoundary where
  formalVerificationCreatesTranslationAdequacy : Bool
  weakVerificationCreatesDecisionAuthority : Bool
  validatorSuccessCreatesConsumerSuccess : Bool
  postHocAbstentionCountsAsSuccessfulAbstention : Bool
  abstentionEvaluationUsesPairedActAbstainCases : Bool
  singleAggregateScoreDeterminesReliability : Bool
  comparatorMayChangeDeclaredConsumer : Bool
  comparatorMayChangeValidatorScope : Bool
  zeroTrialScorecardCountsAsEmpiricalSupport : Bool
  frontierNarrativeCreatesTheoremAuthority : Bool
  agdaHumanReviewReceiptImportedIntoLean : Bool
  deriving DecidableEq, Repr

def canonicalBoundary : ClaimRelativeVerificationBenchmarkBoundary :=
  ⟨false, false, false, false, true, false, false, false, false, false, false⟩

end Integration.ClaimRelativeVerificationBenchmark
