namespace AgdaMirror.Governance.ExternalThreatRepressionMechanismTransfer

structure GeneralThreatRepressionMechanism where
  sourceRef : String
  directPath : String
  indirectPath : String
  generalCausalEvidencePaid : Bool := true
  monotoneMoreThreatMoreRepression : Bool := false
  universalAcrossCases : Bool := false

def generalMechanism : GeneralThreatRepressionMechanism :=
  ⟨"Artabe et al., British Journal of Political Science 2023",
   "external threat can provide leaders political cover to repress opponents",
   "external threat can also induce state-capacity investment that reduces repression"⟩

structure CaseTransferReceipt where
  caseRef : String
  generalMechanism : GeneralThreatRepressionMechanism
  caseSourceRef : String
  caseHasExternalThreatSurface : Bool := true
  caseHasRepressionSurface : Bool := true
  caseHasMobilisationShiftEvidence : Bool := true
  caseSpecificCausalMechanismClosed : Bool := false

def iran2026Transfer : CaseTransferReceipt :=
  ⟨"Iran-2026", generalMechanism, "NBER Working Paper 35734 (2026)"⟩

theorem transfer_is_not_closure :
    iran2026Transfer.caseSpecificCausalMechanismClosed = false ∧
    generalMechanism.monotoneMoreThreatMoreRepression = false := by
  decide

end AgdaMirror.Governance.ExternalThreatRepressionMechanismTransfer
