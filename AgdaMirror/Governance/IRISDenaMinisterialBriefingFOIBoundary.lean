namespace AgdaMirror.Governance.IRISDenaMinisterialBriefingFOIBoundary

structure MinisterialBriefingFOIReceipt where
  sourceRef : String
  reportedNoPreEventBriefs : Bool := true
  underlyingFOIReturnAcquired : Bool := false
  provesMinisterHadNoKnowledge : Bool := false
  provesDefenceHadNoKnowledge : Bool := false
  provesNoOtherCommunicationChannel : Bool := false
  provesNoAustralianAgency : Bool := false


def canonicalReceipt : MinisterialBriefingFOIReceipt :=
  ⟨"Michael West Media 2026-05-12 FOI-based reporting"⟩

theorem reported_absence_of_briefs_is_bounded :
    canonicalReceipt.reportedNoPreEventBriefs = true ∧
    canonicalReceipt.underlyingFOIReturnAcquired = false ∧
    canonicalReceipt.provesMinisterHadNoKnowledge = false ∧
    canonicalReceipt.provesDefenceHadNoKnowledge = false ∧
    canonicalReceipt.provesNoOtherCommunicationChannel = false ∧
    canonicalReceipt.provesNoAustralianAgency = false := by
  decide

end AgdaMirror.Governance.IRISDenaMinisterialBriefingFOIBoundary
