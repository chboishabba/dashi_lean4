namespace AgdaMirror.Governance.IRISDenaPublicRecordConsumerNonDescent

inductive CandidateOperationalState
  | defensiveCandidate
  | maintenanceCandidate
  deriving DecidableEq, Repr

inductive PublicSurface
  | presentProtocolGovernedNonOffensive
  deriving DecidableEq, Repr

inductive ExactDutyOutcome
  | defensiveOutcome
  | maintenanceOutcome
  deriving DecidableEq, Repr

def publicObserver : CandidateOperationalState -> PublicSurface
  | .defensiveCandidate => .presentProtocolGovernedNonOffensive
  | .maintenanceCandidate => .presentProtocolGovernedNonOffensive

def exactDutyConsumer : CandidateOperationalState -> ExactDutyOutcome
  | .defensiveCandidate => .defensiveOutcome
  | .maintenanceCandidate => .maintenanceOutcome

theorem same_public_surface :
    publicObserver .defensiveCandidate = publicObserver .maintenanceCandidate := by
  rfl

theorem different_exact_duty :
    exactDutyConsumer .defensiveCandidate != exactDutyConsumer .maintenanceCandidate := by
  decide

structure NonDescentBoundary where
  samePublicSurfaceCanHideDifferentExactDuty : Bool := true
  publicSurfaceSufficientForExactDuty : Bool := false
  nonDescentChoosesHistoricalTruth : Bool := false
  nonDescentProvesCovertAction : Bool := false


def canonicalBoundary : NonDescentBoundary := {}

theorem public_record_is_not_exact_duty_complete :
    canonicalBoundary.samePublicSurfaceCanHideDifferentExactDuty = true ∧
    canonicalBoundary.publicSurfaceSufficientForExactDuty = false ∧
    canonicalBoundary.nonDescentChoosesHistoricalTruth = false ∧
    canonicalBoundary.nonDescentProvesCovertAction = false := by
  decide

end AgdaMirror.Governance.IRISDenaPublicRecordConsumerNonDescent
