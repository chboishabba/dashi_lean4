import AgdaMirror.Governance.IRISDenaHansardCorrectionAwareEvidence
import AgdaMirror.Governance.AUKUSOnboardConductSovereigntyBoundary

namespace AgdaMirror.Governance.IRISDenaSameObjectAcquisitionMaxCut

inductive AcquisitionStage
  | correctionAwareHansard
  | embeddingProtocol
  | watchDutyAssignment
  | operationalActionLog
  | debriefAfterAction
  deriving DecidableEq, Repr

structure AcquisitionCell where
  stage : AcquisitionStage
  objectRef : String
  currentlyPaid : Bool := false
  mayCloseDutyClass : Bool
  mayCloseExactTask : Bool
  mayProveCovertDivergence : Bool := false


def hansardCell : AcquisitionCell :=
  ⟨.correctionAwareHansard,
   "FADT transcript ref. 29619 pp. 49-52 plus applicable Chief of Navy correction(s)",
   false, true, false⟩

def protocolCell : AcquisitionCell :=
  ⟨.embeddingProtocol,
   "rules/protocols governing embedded RAN personnel during third-party hostilities",
   false, true, false⟩

def watchCell : AcquisitionCell :=
  ⟨.watchDutyAssignment,
   "watchbill/duty assignment for the three Australian personnel at the time of the engagement",
   false, true, true⟩

def actionLogCell : AcquisitionCell :=
  ⟨.operationalActionLog,
   "same-episode operational action log identifying actual tasks during the torpedo engagement",
   false, true, true⟩

structure PaidBoundary where
  presencePaid : Bool := true
  governmentNonOffensivePositionPaid : Bool := true
  notOrderedToBunksPaid : Bool := true
  embeddingRulesExistencePaid : Bool := true
  parliamentaryTranscriptIdentityPaid : Bool := true
  laterCorrectionExistencePaid : Bool := true
  exactDutyPaid : Bool := false
  exactProtocolPaid : Bool := false
  independentOperationalReconstructionPaid : Bool := false


def currentPaidBoundary : PaidBoundary := {}

theorem exact_task_remains_open :
    currentPaidBoundary.exactDutyPaid = false ∧
    currentPaidBoundary.exactProtocolPaid = false ∧
    currentPaidBoundary.independentOperationalReconstructionPaid = false := by
  decide

end AgdaMirror.Governance.IRISDenaSameObjectAcquisitionMaxCut
