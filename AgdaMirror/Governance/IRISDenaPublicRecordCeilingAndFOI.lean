import AgdaMirror.Governance.IRISDenaSenateEstimatesDutyNarrowing

namespace AgdaMirror.Governance.IRISDenaPublicRecordCeilingAndFOI

open AgdaMirror.Governance.IRISDenaSenateEstimatesDutyNarrowing

structure PublicRecordCeiling where
  presencePaid : Bool := true
  nonOffensiveGovernmentPositionPaid : Bool := true
  dutyClassNarrowingPaid : Bool := true
  dutyClassNarrowingPrimaryVerified : Bool := false
  exactWatchstationPaid : Bool := false
  exactProtocolPaid : Bool := false
  exactActionLogPaid : Bool := false

def canonicalPublicRecordCeiling : PublicRecordCeiling := {}

inductive AcquisitionObject
  | proofHansardPages49to52
  | embeddingProtocolText
  | watchDutyRecord
  | operationalActionLog
  | debriefOrAfterActionRecord
  deriving DecidableEq, Repr

structure FOIAcquisitionDemand where
  object : AcquisitionObject
  targetAgency : String
  sameObjectRequirement : String
  publicDisclosureAlreadyFound : Bool := false
  maySubstituteNewsSummary : Bool := false

def proofHansardDemand : FOIAcquisitionDemand :=
  ⟨.proofHansardPages49to52,
   "Australian Parliament / Senate FADT Legislation Committee",
   "proof Committee Hansard, 3 June 2026, pp. 49-52"⟩

def actionLogDemand : FOIAcquisitionDemand :=
  ⟨.operationalActionLog,
   "Australian Department of Defence / U.S. Navy",
   "same-episode action log or equivalent record identifying actual tasks during the torpedo engagement"⟩

theorem public_ceiling_remains_open :
    canonicalPublicRecordCeiling.dutyClassNarrowingPrimaryVerified = false ∧
    canonicalPublicRecordCeiling.exactWatchstationPaid = false ∧
    canonicalPublicRecordCeiling.exactProtocolPaid = false ∧
    canonicalPublicRecordCeiling.exactActionLogPaid = false := by
  decide

end AgdaMirror.Governance.IRISDenaPublicRecordCeilingAndFOI
