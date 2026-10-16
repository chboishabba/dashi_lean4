import Integration.ScopedVerifierSameObjectEvaluation

namespace Integration.ScopedVerifierSameObjectEvaluationRegression

open Integration.ConsumerRelativeRepresentationParity
open Integration.ScopedVerifierSameObjectEvaluation

inductive Fixture where
  | a | b
  deriving DecidableEq, Repr

inductive Observation where
  | same
  deriving DecidableEq, Repr

inductive Consumer where
  | same
  deriving DecidableEq, Repr

inductive Case where
  | shared
  deriving DecidableEq, Repr

inductive Intervention where
  | shared
  deriving DecidableEq, Repr

def observe : Fixture → Observation := fun _ => .same

def consume : Fixture → Consumer := fun _ => .same

def factorization :
    Integration.ScopedVerifierConsumerSufficiency.ConsumerFactorization observe consume :=
  ⟨fun _ => .same, by intro x; cases x <;> rfl⟩

def eligible : EligibleRepresentation observe consume where
  Admissible := True
  admissibilityReceipt := trivial
  ConsumerAdequate := True
  consumerAdequacyReceipt := trivial
  consumerFactorization := factorization

def matchedPair : Integration.ScopedVerifierEvaluationProtocol.MatchedSystemPair :=
  { candidateLabel := "candidate"
    baselineLabel := "baseline"
    sameTaskSet := true
    sameToolAccess := true
    sameContextBudget := true
    sameComputeAccounting := true
    sameDeclaredConsumers := true
    sameValidatorScope := true }

def task : Integration.ScopedVerifierEvaluationProtocol.EvaluationTask :=
  { taskLabel := "fixture"
    declaredDomain := "fixture"
    heldOutProtocol := "all axes held out" }

def measurements : Integration.ScopedVerifierEvaluationProtocol.ComparativeMeasurements :=
  { editIdentityTrials := 1
    editIdentitySuccesses := 1
    factualTrials := 1
    factualVerifiedCorrect := 1
    oodTrials := 1
    oodCorrectAbstentions := 1
    applicableTrials := 1
    validatorCoveredTrials := 1
    candidateCostUnits := 1
    baselineCostUnits := 1 }

def evaluation : Integration.ScopedVerifierEvaluationProtocol.EvaluationReceipt :=
  { task := task
    pair := matchedPair
    measurements := measurements
    provenance := "fixture"
    independentlyReproducible := true }

def protocol : HeldOutProtocol :=
  { targetHeldOut := true
    contextHeldOut := true
    modelHeldOut := true
    checkpointHeldOut := true
    matchedPairingDeclared := true
    dynamicTraceRequired := true
    targetRealizationRequired := true
    protocolReference := "fixture protocol" }

def receipt : SameObjectHeldOutEvaluation observe observe consume Case Intervention where
  candidateEligibility := eligible
  baselineEligibility := eligible
  evaluation := evaluation
  protocol := protocol
  candidateCase := .shared
  baselineCase := .shared
  sameCase := rfl
  candidateIntervention := .shared
  baselineIntervention := .shared
  sameIntervention := rfl
  targetHoldoutPaid := rfl
  contextHoldoutPaid := rfl
  modelHoldoutPaid := rfl
  checkpointHoldoutPaid := rfl
  matchedPairingPaid := rfl
  dynamicTracePaid := rfl
  targetRealizationPaid := rfl
  sameTaskSetPaid := rfl
  sameToolAccessPaid := rfl
  sameContextBudgetPaid := rfl
  sameComputeAccountingPaid := rfl
  sameDeclaredConsumersPaid := rfl
  sameValidatorScopePaid := rfl

example : receipt.candidateCase = receipt.baselineCase := receipt.sameCase
example : eligible.Admissible := candidateAdmissibilityPaid receipt
example : eligible.ConsumerAdequate := candidateConsumerAdequacyPaid receipt

end Integration.ScopedVerifierSameObjectEvaluationRegression
