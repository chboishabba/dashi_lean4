namespace Integration.ScopedVerifierEvaluationProtocol

structure EvaluationTask where
  taskLabel : String
  declaredDomain : String
  heldOutProtocol : String
  deriving Repr

structure MatchedSystemPair where
  candidateLabel : String
  baselineLabel : String
  sameTaskSet : Bool
  sameToolAccess : Bool
  sameContextBudget : Bool
  sameComputeAccounting : Bool
  sameDeclaredConsumers : Bool
  sameValidatorScope : Bool
  deriving Repr

structure ComparativeMeasurements where
  editIdentityTrials : Nat
  editIdentitySuccesses : Nat
  factualTrials : Nat
  factualVerifiedCorrect : Nat
  oodTrials : Nat
  oodCorrectAbstentions : Nat
  applicableTrials : Nat
  validatorCoveredTrials : Nat
  candidateCostUnits : Nat
  baselineCostUnits : Nat
  deriving Repr

structure EvaluationReceipt where
  task : EvaluationTask
  pair : MatchedSystemPair
  measurements : ComparativeMeasurements
  provenance : String
  independentlyReproducible : Bool
  deriving Repr

structure EvaluationBoundary where
  architectureImpliesEmpiricalWin : Bool
  zeroTrialCountAcceptedAsPerformance : Bool
  unmatchedBaselineAccepted : Bool
  consumerMismatchAccepted : Bool
  validatorScopeMismatchAccepted : Bool
  coverageSeparatedFromAccuracy : Bool
  abstentionSeparatedFromRefutation : Bool
  runtimeCostReportedSeparately : Bool
  deriving DecidableEq, Repr

def canonicalEvaluationBoundary : EvaluationBoundary :=
  ⟨false, false, false, false, false, true, true, true⟩

end Integration.ScopedVerifierEvaluationProtocol
