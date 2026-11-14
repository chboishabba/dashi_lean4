import Dashi.Biology.GABAPhenotypeEvidenceExact

namespace Dashi.Biology.GABAPhenotypeEvidenceRegression

open Dashi.Biology.GABAPhenotypeEvidenceExact

/-! Focused regression surface for the bounded GABA / phenotype evidence lane. -/

theorem sourceAttributionNonAuthorityRegression :
    schmitz2017Source.citationCreatesAuthority = false := by
  rfl

theorem sourceAttributionNonProofRegression :
    schmitz2017Source.citationImportsProof = false := by
  rfl

theorem associationCausalityGateRegression :
    AssociationIsCausalSufficiencyPermission → False :=
  associationDoesNotImplyCausalSufficiency

theorem regionalWholeBrainGateRegression :
    RegionalDifferenceIsWholeBrainDifferencePermission → False :=
  regionalGABADifferenceDoesNotImplyWholeBrainDifference

theorem groupIndividualGateRegression :
    GroupMeanClassifiesIndividualPermission → False :=
  groupMeanDoesNotClassifyIndividual

theorem diagnosisGABAGateRegression :
    DiagnosisDeterminesGABALevelPermission → False :=
  diagnosisDoesNotDetermineGABALevel

theorem thoughtEmotionGateRegression :
    ThoughtSuppressionIsEmotionSuppressionPermission → False :=
  thoughtSuppressionEvidenceDoesNotPromoteToEmotionSuppression

theorem synchronyAttachmentGateRegression :
    SynchronyDefinesAttachmentPermission → False :=
  noAttachmentBridgeFromSynchronyWithoutReceipt

theorem gabaNeuroinflammationGateRegression :
    GABADefinesNeuroinflammationPermission → False :=
  noNeuroinflammationBridgeFromGABAWithoutReceipt

theorem autismCausalSufficiencyGateRegression :
    AutismCausedByLowGABAPermission → False :=
  autismLowGABAAssociationDoesNotProveCausalSufficiency

theorem adhdCausalSufficiencyGateRegression :
    ADHDCausedByLowGABAPermission → False :=
  adhdGABAHypothesisDoesNotProveCausalSufficiency

theorem sensoryUniversalizationGateRegression :
    SensoryAssociationIsGlobalSeverityLawPermission → False :=
  sensoryAssociationDoesNotUniversalizeAutism

def canonicalBoundaryRegression : GABAPhenotypeBoundary :=
  canonicalGABAPhenotypeBoundary

end Dashi.Biology.GABAPhenotypeEvidenceRegression
