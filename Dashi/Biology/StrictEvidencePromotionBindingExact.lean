namespace Dashi.Biology.StrictEvidencePromotionBindingExact

/-!
Proof-relevant same-object/same-scope promotion binding.

Stable string keys remain useful external identifiers, but they do not pay the
promotion.  Promotion authority is carried by relations indexed by the exact
claim/evidence/estimand values.
-/

structure StrictPromotionBinding
    {Claim Evidence Estimand : Type}
    (claimKey : Claim → String)
    (evidenceKey : Evidence → String)
    (estimandScopeKey : Estimand → String)
    (evidencePaysClaim : Evidence → Claim → Prop)
    (evidenceMatchesEstimand : Evidence → Estimand → Prop)
    (claim : Claim)
    (evidence : Evidence)
    (estimand : Estimand) where
  boundClaimKey : String
  boundClaimKeyMatches : boundClaimKey = claimKey claim
  boundEvidenceKey : String
  boundEvidenceKeyMatches : boundEvidenceKey = evidenceKey evidence
  boundEstimandScopeKey : String
  boundEstimandScopeKeyMatches : boundEstimandScopeKey = estimandScopeKey estimand
  evidencePaysClaimWitness : evidencePaysClaim evidence claim
  evidenceMatchesEstimandWitness : evidenceMatchesEstimand evidence estimand
  identificationReference : String

structure StrictPromotionPair
    {Claim Evidence : Type}
    (claimKey : Claim → String)
    (evidenceKey : Evidence → String)
    (evidencePaysClaim : Evidence → Claim → Prop)
    (claim : Claim)
    (evidence : Evidence) where
  pairClaimKey : String
  pairClaimKeyMatches : pairClaimKey = claimKey claim
  pairEvidenceKey : String
  pairEvidenceKeyMatches : pairEvidenceKey = evidenceKey evidence
  pairEvidencePaysClaimWitness : evidencePaysClaim evidence claim
  pairSameObjectReference : String

end Dashi.Biology.StrictEvidencePromotionBindingExact
