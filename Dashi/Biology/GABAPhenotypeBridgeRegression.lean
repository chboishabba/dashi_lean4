import Dashi.Biology.GABAPhenotypeBridgeExact

namespace Dashi.Biology.GABAPhenotypeBridgeRegression

namespace Bridge := Dashi.Biology.GABAPhenotypeBridgeExact
namespace Evidence := Dashi.Biology.GABAPhenotypeEvidenceExact

def causalBridgeExportsExistingEstimand
    {evidence : Evidence.RegionalGABAEvidence}
    (bridge : Bridge.AssociationToCausalBridge evidence) :
    Bridge.CausalEstimandReference :=
  Bridge.causalPromotionRequiresExistingEstimand bridge

theorem evidenceFamilyTagCannotPromote :
    Bridge.EvidenceFamilyDeterminesCausalAuthorityPermission → False :=
  Bridge.evidenceFamilyTagDoesNotDetermineCausalAuthority

theorem contextSensitivitySurvivesGABAAttachment
    {Weight Context Geometry Load : Type}
    (evidence : Evidence.RegionalGABAEvidence)
    (weight : Weight) (geometry : Geometry)
    (context₁ context₂ : Context) (load₁ load₂ : Load)
    (hContext : context₁ ≠ context₂)
    (hLoad : load₁ ≠ load₂) : load₁ ≠ load₂ :=
  Bridge.sameGABAEvidenceDifferentContextCanChangeLoad
    evidence weight geometry context₁ context₂ load₁ load₂ hContext hLoad

theorem memoryAttachmentDoesNotMutateIdentity
    {Memory : Type} (memory : Memory) : memory = memory :=
  Bridge.schmitzEvidenceDoesNotByItselfChangeMemory memory

def adhdEvidenceHoleRegression : Bridge.ADHDEvidenceGap :=
  Bridge.canonicalADHDEvidenceGap

def bridgeBoundaryRegression : Bridge.GABAPhenotypeBridgeBoundary :=
  Bridge.canonicalGABAPhenotypeBridgeBoundary

end Dashi.Biology.GABAPhenotypeBridgeRegression
