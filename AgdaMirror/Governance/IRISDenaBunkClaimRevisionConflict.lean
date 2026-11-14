namespace AgdaMirror.Governance.IRISDenaBunkClaimRevisionConflict

inductive ClaimStatus
  | attributedSecondary
  | deniedPrimaryNamed
  | exactDutyUnresolved
  deriving DecidableEq, Repr

structure BunkClaimRevisionReceipt where
  earlyStatus : ClaimStatus
  laterStatus : ClaimStatus
  earlySourceAnonymous : Bool
  laterSpeakerNamed : Bool
  bunkPropositionPrimaryDenied : Bool
  exactDutyDisclosedByDenial : Bool
  historicalEventChangedByLaterSource : Bool
  deriving DecidableEq, Repr

def canonicalRevision : BunkClaimRevisionReceipt :=
  ⟨.attributedSecondary, .deniedPrimaryNamed, true, true, true, false, false⟩

theorem bunk_claim_resolved_without_exact_duty_closure :
    canonicalRevision.bunkPropositionPrimaryDenied = true ∧
    canonicalRevision.exactDutyDisclosedByDenial = false ∧
    canonicalRevision.historicalEventChangedByLaterSource = false := by
  decide

inductive InvalidPromotion
  | anonymousSecondaryEqualsPrimaryFact
  | primaryBunkDenialDeterminesExactDuty
  | resolvedBunkClaimClosesEpisode
  | knowledgeRevisionChangesEarlierWorldEvent
  | repetitionCreatesIndependentCorroboration
  deriving Repr

end AgdaMirror.Governance.IRISDenaBunkClaimRevisionConflict
