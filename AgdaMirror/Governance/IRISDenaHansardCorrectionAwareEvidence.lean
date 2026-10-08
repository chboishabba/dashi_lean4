namespace AgdaMirror.Governance.IRISDenaHansardCorrectionAwareEvidence

structure HansardIdentityReceipt where
  committeeRef : String
  hearingDate : String
  transcriptRefNo : String
  relevantPages : String
  transcriptPublishedInFull : Bool := true
  relevantTopicLocated : Bool := true
  relevantPageContentReviewed : Bool := false

structure CorrectionIndexReceipt where
  witnessRef : String
  hearingDatesCovered : String
  firstCorrectionDate : String
  laterCorrectionDate : String
  correctionDocumentListed : Bool := true
  correctionContentReviewed : Bool := false
  correctionAffectsIRISDutyEvidence : Bool := false

structure CorrectionAwarePrimaryBundle where
  hansard : HansardIdentityReceipt
  correctionIndex : CorrectionIndexReceipt
  primaryTranscriptIdentityPaid : Bool := true
  laterCorrectionExistencePaid : Bool := true
  primaryDutyContentPaid : Bool := false
  correctionApplicabilityPaid : Bool := false
  secondarySummaryMayPromoteDutyClass : Bool := false


def canonicalHansardIdentity : HansardIdentityReceipt :=
  ⟨"Foreign Affairs, Defence and Trade Legislation Committee",
   "2026-06-03", "29619", "proof Committee Hansard pp. 49-52"⟩

def chiefOfNavyCorrectionIndex : CorrectionIndexReceipt :=
  ⟨"Vice Admiral Mark Hammond AO RAN, Chief of Navy",
   "public hearings on 2-3 June 2026", "2026-06-22", "2026-07-23"⟩

def canonicalPrimaryBundle : CorrectionAwarePrimaryBundle :=
  ⟨canonicalHansardIdentity, chiefOfNavyCorrectionIndex⟩

theorem publication_identity_is_not_content_verification :
    canonicalPrimaryBundle.primaryTranscriptIdentityPaid = true ∧
    canonicalPrimaryBundle.primaryDutyContentPaid = false ∧
    canonicalPrimaryBundle.correctionApplicabilityPaid = false ∧
    canonicalPrimaryBundle.secondarySummaryMayPromoteDutyClass = false := by
  decide

end AgdaMirror.Governance.IRISDenaHansardCorrectionAwareEvidence
