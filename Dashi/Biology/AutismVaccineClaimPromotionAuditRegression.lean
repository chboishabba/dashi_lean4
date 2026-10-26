import Dashi.Biology.AutismVaccineClaimPromotionAuditExact

namespace Dashi.Biology.AutismVaccineClaimPromotionAuditRegression

open Dashi.Biology.AutismVaccineClaimPromotionAuditExact

example : canonicalAuditBoundary.sourceVoicesSeparated = true := rfl
example : canonicalAuditBoundary.sourceReportCreatesTruth = false := rfl
example : canonicalAuditBoundary.associationCreatesCausation = false := rfl
example : canonicalAuditBoundary.symptomCutoffEqualsDiagnosisRemoval = false := rfl
example : canonicalAuditBoundary.pronounCountDiagnosesIndividual = false := rfl
example : canonicalAuditBoundary.synchronyCreatesFalseBelief = false := rfl
example : canonicalAuditBoundary.mediaPropagationDeterminesBiomedicalTruth = false := rfl
example : vaccineToAutismEdge.edgeStatus = .blockedPromotion := rfl
example : fmtToDiagnosisRemovalEdge.edgeStatus = .blockedPromotion := rfl
example : synchronyToFalseBeliefEdge.edgeStatus = .blockedPromotion := rfl
example : hbombAutismRepresentationClaim.claimSpeaker = .hbomberguy := rfl
example : wakefieldGutOpioidMechanismClaim.claimSpeaker = .wakefield := rfl

end Dashi.Biology.AutismVaccineClaimPromotionAuditRegression
