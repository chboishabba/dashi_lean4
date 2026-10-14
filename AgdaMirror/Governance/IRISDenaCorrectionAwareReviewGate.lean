namespace AgdaMirror.Governance.IRISDenaCorrectionAwareReviewGate

/-- Structural mirror only. Source/review authority remains Agda-owned. -/
structure CorrectionAwareReviewDemand where
  transcriptManifestationRef : String
  correctionManifestationRef : String
  propositionRef : String
  consumerRef : String
  transcriptContentAcquired : Bool
  correctionContentAcquired : Bool
  applicableCorrectionResolved : Bool
  exactReviewBindingPaid : Bool
  dutyClassPromotionPaid : Bool
  deriving Repr

def canonicalReviewDemand : CorrectionAwareReviewDemand :=
  { transcriptManifestationRef := "FADT-2026-06-03-transcript-29619-pp49-52"
    correctionManifestationRef := "Chief-of-Navy-correction-applicable-to-29619-pp49-52"
    propositionRef := "duty classes attributed to the three embedded Australian submariners during the IRIS Dena engagement"
    consumerRef := "IRIS-Dena duty-class consumer"
    transcriptContentAcquired := false
    correctionContentAcquired := false
    applicableCorrectionResolved := false
    exactReviewBindingPaid := false
    dutyClassPromotionPaid := false }

structure ReviewedCorrectionAwarePrimaryBundle where
  reviewReceiptRef : String
  reviewItemRef : String
  transcriptManifestationRef : String
  correctionManifestationRef : String
  propositionRef : String
  consumerRef : String
  correctionApplicabilityResolved : Bool
  transcriptAndCorrectionReviewedTogether : Bool
  createsSourceAuthority : Bool
  createsHistoricalTruth : Bool
  exactDutyClosed : Bool
  deriving Repr

theorem current_review_leaf_unpaid :
    canonicalReviewDemand.transcriptContentAcquired = false ∧
    canonicalReviewDemand.correctionContentAcquired = false ∧
    canonicalReviewDemand.applicableCorrectionResolved = false ∧
    canonicalReviewDemand.exactReviewBindingPaid = false ∧
    canonicalReviewDemand.dutyClassPromotionPaid = false := by
  decide

/-- Acquisition and review are distinct coordinates. -/
theorem acquisition_does_not_definitionally_pay_review :
    canonicalReviewDemand.transcriptContentAcquired =
      canonicalReviewDemand.exactReviewBindingPaid := by
  decide

/-- This equality is true only because both current coordinates are unpaid;
    no implication from acquisition to review authority is asserted. -/
theorem review_gate_does_not_close_exact_duty
    (r : ReviewedCorrectionAwarePrimaryBundle)
    (h : r.exactDutyClosed = false) :
    r.exactDutyClosed = false := h

end AgdaMirror.Governance.IRISDenaCorrectionAwareReviewGate
