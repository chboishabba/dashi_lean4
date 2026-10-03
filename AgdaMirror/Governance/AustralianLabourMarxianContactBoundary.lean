namespace AgdaMirror.Governance.AustralianLabourMarxianContactBoundary

inductive LabourHistoricalLayer
  | colonialWorkerMovement | australianLaborParty | marxistSocialistGroups
  | communistPartyAustralia | tradeUnionMovement
  deriving DecidableEq, Repr

inductive HistoricalContactKind
  | textualObservation | ideologicalReception | organisationalOverlap | criticalMarxistAnalysis
  deriving DecidableEq, Repr

structure ContactReceipt where
  left : LabourHistoricalLayer
  right : LabourHistoricalLayer
  kind : HistoricalContactKind
  sourceReceipt : String
  provesIdentity : Bool := false
  provesDirectOrganisationalLineage : Bool := false

def marxEurekaContact : ContactReceipt :=
  ⟨.colonialWorkerMovement, .marxistSocialistGroups, .textualObservation,
   "secondary archive reporting Marx on Eureka"⟩

def leninLaborCritique : ContactReceipt :=
  ⟨.australianLaborParty, .marxistSocialistGroups, .criticalMarxistAnalysis,
   "Lenin, In Australia, 1913"⟩

def fisherModerateSocialistContact : ContactReceipt :=
  ⟨.australianLaborParty, .marxistSocialistGroups, .ideologicalReception,
   "National Museum of Australia Andrew Fisher history"⟩

theorem contact_does_not_create_identity :
    marxEurekaContact.provesIdentity = false ∧
    leninLaborCritique.provesIdentity = false ∧
    fisherModerateSocialistContact.provesIdentity = false := by
  decide

end AgdaMirror.Governance.AustralianLabourMarxianContactBoundary
