namespace Dashi.Biology.StrictEvidencePromotionBindingExact

structure StrictPromotionBinding
    {Claim Evidence Estimand : Type}
    (claimKey : Claim → String)
    (evidenceKey : Evidence → String)
    (estimandScopeKey : Estimand → String)
    (claim : Claim)
    (evidence : Evidence)
    (estimand : Estimand) where
  boundClaimKey : String
  boundClaimKeyMatches : boundClaimKey = claimKey claim
  boundEvidenceKey : String
  boundEvidenceKeyMatches : boundEvidenceKey = evidenceKey evidence
  boundEstimandScopeKey : String
  boundEstimandScopeKeyMatches : boundEstimandScopeKey = estimandScopeKey estimand
  evidencePaysClaimReference : String
  estimandMatchesEvidenceScopeReference : String
  identificationReference : String
  deriving Repr

structure StrictPromotionPair
    {Claim Evidence : Type}
    (claimKey : Claim → String)
    (evidenceKey : Evidence → String)
    (claim : Claim)
    (evidence : Evidence) where
  pairClaimKey : String
  pairClaimKeyMatches : pairClaimKey = claimKey claim
  pairEvidenceKey : String
  pairEvidenceKeyMatches : pairEvidenceKey = evidenceKey evidence
  pairEvidencePaysClaimReference : String
  pairSameObjectReference : String
  deriving Repr

end Dashi.Biology.StrictEvidencePromotionBindingExact
