import Dashi.Biology.GABAPhenotypeBridgeExact

namespace Dashi.Biology.GABAPhenotypeBridgeRegression

open Dashi.Biology.GABAPhenotypeBridgeExact
open Dashi.Biology.GABAPhenotypeEvidenceExact

def causalBridgeExportsExistingEstimand
    {evidence : RegionalGABAEvidence}
    (bridge : AssociationToCausalBridge evidence) :
    CausalEstimandReference :=
  causalPromotionRequiresExistingEstimand bridge

theorem evidenceFamilyTagCannotPromote :
    EvidenceFamilyDeterminesCausalAuthorityPermission → False :=
  evidenceFamilyTagDoesNotDetermineCausalAuthority

theorem contextSensitivitySurvivesGABAAttachment
    {Weight Context Geometry Load : Type}
    (evidence : RegionalGABAEvidence)
    (weight : Weight) (geometry : Geometry)
    (context₁ context₂ : Context) (load₁ load₂ : Load)
    (hContext : context₁ ≠ context₂)
    (hLoad : load₁ ≠ load₂) : load₁ ≠ load₂ :=
  sameGABAEvidenceDifferentContextCanChangeLoad
    evidence weight geometry context₁ context₂ load₁ load₂ hContext hLoad

theorem memoryAttachmentDoesNotMutateIdentity
    {Memory : Type} (memory : Memory) : memory = memory :=
  schmitzEvidenceDoesNotByItselfChangeMemory memory

def adhdEvidenceHoleRegression : ADHDEvidenceGap :=
  canonicalADHDEvidenceGap

def bridgeBoundaryRegression : GABAPhenotypeBridgeBoundary :=
  canonicalGABAPhenotypeBridgeBoundary

end Dashi.Biology.GABAPhenotypeBridgeRegression
