import Integration.RationalAlbertTauCetiF4DonorAudit

namespace Integration.RationalAlbertTauCetiF4DonorAuditRegression

open Integration.RationalAlbertTauCetiF4DonorAudit

example : canonicalAudit.tauCetiAlbertCarrierLocated = true := rfl
example : canonicalAudit.tauCetiAlbertTraceZeroLieSubmoduleLocated = true := rfl
example : canonicalAudit.tauCetiAlbertTraceZeroFinrank26Located = true := rfl
example : canonicalAudit.tauCetiAlbertTraceZeroFaithfulActionLocated = true := rfl
example : canonicalAudit.tauCetiF4RootDatumLocated = true := rfl
example : canonicalAudit.tauCetiF4LieAlgebraLocated = true := rfl
example : canonicalAudit.sameObjectAlbertDerivationToF4LieEquivLocated = false := rfl
example : canonicalAudit.externalDonorCreatesDASHITheorem = false := rfl

example : ¬ FaithfulTwentySixRepresentationCreatesF4Classification :=
  faithful_twenty_six_does_not_create_f4_classification

end Integration.RationalAlbertTauCetiF4DonorAuditRegression
