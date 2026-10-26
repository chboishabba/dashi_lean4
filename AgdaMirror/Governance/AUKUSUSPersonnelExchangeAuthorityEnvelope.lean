namespace AgdaMirror.Governance.AUKUSUSPersonnelExchangeAuthorityEnvelope

structure USPEPAuthorityEnvelopeReceipt where
  statutoryExchangeAuthorityPaid : Bool
  assignmentMustBeJointlyAcceptablePaid : Bool
  noHostOathRequiredPaid : Bool
  australiaPartnerPaid : Bool
  fullyIntegratedProgramModelAttributed : Bool
  genericOperationalIntegrationPaid : Bool
  bilateralMOUOperativeTextPaid : Bool
  ranDirectivePrimaryTextPaid : Bool
  irisSameEpisodeDutyPaid : Bool
  deriving DecidableEq, Repr

def canonicalEnvelope : USPEPAuthorityEnvelopeReceipt :=
  ⟨true, true, true, true, true, true, false, false, false⟩

theorem generic_pep_does_not_pay_bilateral_or_episode :
    canonicalEnvelope.statutoryExchangeAuthorityPaid = true ∧
    canonicalEnvelope.australiaPartnerPaid = true ∧
    canonicalEnvelope.bilateralMOUOperativeTextPaid = false ∧
    canonicalEnvelope.irisSameEpisodeDutyPaid = false := by
  decide

inductive InvalidPromotion
  | fullyIntegratedMeansFormalRANCommand
  | genericPEPMeansBilateralMOUKnown
  | genericPEPMeansIRISDutyKnown
  | noOathMeansNoHostDirectionAuthority
  deriving Repr

end AgdaMirror.Governance.AUKUSUSPersonnelExchangeAuthorityEnvelope
