import Dashi.Biology.AutismVaccinePersuasionMediaExtensionExact

namespace Dashi.Biology.AutismTranscriptHighAlphaCrossPollinationExact

open Dashi.Biology.AutismVaccinePersuasionMediaExtensionExact

structure SourceReceipt where
  authors : String
  title : String
  year : String
  doi : String
  paidReading : String
  scopeBoundary : String
  deriving Repr, DecidableEq

def shankerVlaev2026Source : SourceReceipt := {
  authors := "Ankit Shanker; Ivo Vlaev"
  title := "Correcting social norm misperceptions to counter online vaccine misinformation during pandemics"
  year := "2026"
  doi := "10.1038/s41598-026-71728-3"
  paidReading := "Randomized online experiment in 731 UK adults: misinformation reduced vaccination intention and distorted perceived peer support; reported mediation implicated norm misperception."
  scopeBoundary := "Adding descriptive norms corrected perceived norms more strongly but did not significantly outperform debunking alone on average intention change."
}

def cornelson2026Source : SourceReceipt := {
  authors := "Kirsten Cornelson; Hao Ming Chen; Caitlin Ford; Jia Hu; Madison Fullerton; Hinna Hasan; Margaret Pateman; Theresa Tang; Janette Wong"
  title := "Randomized volunteer intervention reduced comments and reaction on anti-COVID-19 vaccine posts on Facebook"
  year := "2026"
  doi := "10.1038/s41598-026-62919-z"
  paidReading := "Randomized volunteer social correction reduced comments and some reactions on treated posts."
  scopeBoundary := "Little evidence of reduced sharing; no direct demonstration of reduced misinformation prevalence, belief change, or exposure."
}

def tuckZhuThompson2026Source : SourceReceipt := {
  authors := "Alison B. Tuck; Yiqin Zhu; Renee J. Thompson"
  title := "Depressive Symptoms Are Associated with Linguistic Features of Negative but Not Positive Autobiographical Narratives"
  year := "2026"
  doi := "10.1007/s42761-026-00395-4"
  paidReading := "In 457 undergraduates, depressive symptoms were associated with more first-person pronoun use in negative autobiographical narratives."
  scopeBoundary := "Association was absent in the positive narrative condition; significant language effects were small and context-dependent."
}

def fisher2026Source : SourceReceipt := {
  authors := "Hadar Fisher; Nigel M Jaffe; Kristina Pidvirny; Anna O Tierney; Mia S Vaidean; Poorvesh Dongre; Christian A Webb"
  title := "Language-based detection of depression with machine learning: systematic review and meta-analysis"
  year := "2026"
  doi := "10.1038/s41746-026-02448-1"
  paidReading := "Language-only depression models showed pooled accuracy around 0.80 across 43 studies and 40,983 samples."
  scopeBoundary := "Performance was heterogeneous by text source and other design factors; review calls for standardization and validation before clinical use."
}

def wan2024FMTSource : SourceReceipt := {
  authors := "Lin Wan; Huan Wang; Yan Liang; Xun Zhang; Xinyun Yao; Gang Zhu; Jun Cai; Guoyin Liu; Xinting Liu; Qianqian Niu; Siwen Li; Bo Zhang; Jing Gao; Jing Wang; Xiuyu Shi; Linyan Hu; Xiaoyan Liu; Zhiyong Zou; Guang Yang"
  title := "Effect of oral faecal microbiota transplantation intervention for children with autism spectrum disorder: A randomised, double-blind, placebo-controlled trial"
  year := "2024"
  doi := "10.1002/ctm2.70006"
  paidReading := "Randomized double-blind placebo-controlled trial in 103 children (FMT 52; placebo 51). Primary SRS-2 between-group change was not significant; a Vineland-3 socialisation-domain secondary signal favoured FMT at week 17."
  scopeBoundary := "ABC between-group changes were not significant, placebo response was substantial, and no diagnosis-removal claim is paid."
}

def zou2026FMTProtocolSource : SourceReceipt := {
  authors := "Yigui Zou; Liang Liu; Hu Chen; Zimu Luo; Zhongsheng Zhu; Ziyuan Li; Baixian Lin; Zeling Zhuang; Wenwen Li; Qinghua Yang; Xiao Yang; Haokui Zhou; Mingjing Luo; Dongling Dai"
  title := "Study protocol for a randomized controlled trial of fecal microbiota transplantation via different routes in children with moderate-to-severe autism spectrum disorder"
  year := "2026"
  doi := "10.3389/fmicb.2026.1829532"
  paidReading := "Protocol for a 75-participant randomized triple-blind double-dummy placebo-controlled route-comparison trial."
  scopeBoundary := "Protocol status pays planned design and outcomes only, not efficacy."
}

def loseth2024Source : SourceReceipt := {
  authors := "Guro Løseth; Martin Trøstheim; Siri Leknes"
  title := "Endogenous mu-opioid modulation of social connection in humans: a systematic review and meta-analysis"
  year := "2024"
  doi := "10.1038/s41398-024-03088-3"
  paidReading := "Preregistered meta-analysis of randomized double-blind placebo-controlled naltrexone studies found a small reduction in self-reported social connectedness under antagonism (Hedges g about -0.20)."
  scopeBoundary := "Robust connectedness remained under blockade; this supports modulation, not necessity, truth authority, attachment classification, or an autism mechanism."
}

def linares2026Source : SourceReceipt := {
  authors := "Jon Liñares-de-Marcos; Blanca Palomero-Sierra; Victoria Sánchez-Gómez; Clara J Fernández-Álvarez; Ricardo Canal-Bedia"
  title := "An integrative approach between neurodiversity perspectives and quality of life models for autistic people across the spectrum of support needs"
  year := "2026"
  doi := "10.3389/fpsyt.2025.1756323"
  paidReading := "Mini-review integrates neurodiversity and quality-of-life approaches across support needs."
  scopeBoundary := "Identity/self-acceptance and high-quality supports/interventions are treated as compatible rather than mutually exclusive."
}

/- Attribution is provenance, not result authority.  Each result structure below
   accepts only an admission inhabitant for its exact outcome family; the
   underlying SourceReceipt is then recovered from that admission. -/
inductive HighAlphaOutcomeFamily where
  | normMediationOutcome
  | platformInterventionOutcome
  | pronounAssociationOutcome
  | languageModelMetaOutcome
  | fmtTrialOutcome
  | fmtProtocolDesignOutcome
  | muOpioidSocialOutcome
  | neurodiversityQoLOutcome
  deriving Repr, DecidableEq

inductive AdmittedHighAlphaSource : HighAlphaOutcomeFamily → Type where
  | shankerVlaevPaysNormMediationOutcome : AdmittedHighAlphaSource .normMediationOutcome
  | cornelsonPaysPlatformInterventionOutcome : AdmittedHighAlphaSource .platformInterventionOutcome
  | tuckZhuThompsonPaysPronounAssociationOutcome : AdmittedHighAlphaSource .pronounAssociationOutcome
  | fisherPaysLanguageModelMetaOutcome : AdmittedHighAlphaSource .languageModelMetaOutcome
  | wan2024PaysFMTTrialOutcome : AdmittedHighAlphaSource .fmtTrialOutcome
  | zou2026PaysFMTProtocolDesign : AdmittedHighAlphaSource .fmtProtocolDesignOutcome
  | losethPaysMuOpioidSocialOutcome : AdmittedHighAlphaSource .muOpioidSocialOutcome
  | linaresPaysNeurodiversityQoLOutcome : AdmittedHighAlphaSource .neurodiversityQoLOutcome
  deriving Repr, DecidableEq

def admittedHighAlphaSourceReceipt : {family : HighAlphaOutcomeFamily} → AdmittedHighAlphaSource family → SourceReceipt
  | _, .shankerVlaevPaysNormMediationOutcome => shankerVlaev2026Source
  | _, .cornelsonPaysPlatformInterventionOutcome => cornelson2026Source
  | _, .tuckZhuThompsonPaysPronounAssociationOutcome => tuckZhuThompson2026Source
  | _, .fisherPaysLanguageModelMetaOutcome => fisher2026Source
  | _, .wan2024PaysFMTTrialOutcome => wan2024FMTSource
  | _, .zou2026PaysFMTProtocolDesign => zou2026FMTProtocolSource
  | _, .losethPaysMuOpioidSocialOutcome => loseth2024Source
  | _, .linaresPaysNeurodiversityQoLOutcome => linares2026Source

inductive MediationCoordinate where
  | misinformationExposure
  | perceivedPeerSupport
  | vaccinationIntent
  deriving Repr, DecidableEq

structure NormMediationReceipt where
  sourceAdmission : AdmittedHighAlphaSource .normMediationOutcome
  upstream : MediationCoordinate
  mediator : MediationCoordinate
  downstream : MediationCoordinate
  randomizedDesign : Bool
  averageNormAddedBenefitOverDebunkingPaid : Bool
  reading : String
  deriving Repr, DecidableEq

namespace NormMediationReceipt
def source (r : NormMediationReceipt) : SourceReceipt := admittedHighAlphaSourceReceipt r.sourceAdmission
end NormMediationReceipt

def canonicalNormMediationReceipt : NormMediationReceipt := {
  sourceAdmission := .shankerVlaevPaysNormMediationOutcome
  upstream := .misinformationExposure
  mediator := .perceivedPeerSupport
  downstream := .vaccinationIntent
  randomizedDesign := true
  averageNormAddedBenefitOverDebunkingPaid := false
  reading := "Perceived peer support becomes a measured mediator candidate inside the existing exposure -> belief/norm -> intent chain; it is not promoted to the unique mechanism."
}

structure PlatformInterventionReceipt where
  sourceAdmission : AdmittedHighAlphaSource .platformInterventionOutcome
  commentsReduced : Bool
  someAffectiveResponseReduced : Bool
  sharingReductionPaid : Bool
  beliefChangePaid : Bool
  prevalenceReductionPaid : Bool
  deriving Repr, DecidableEq

namespace PlatformInterventionReceipt
def source (r : PlatformInterventionReceipt) : SourceReceipt := admittedHighAlphaSourceReceipt r.sourceAdmission
end PlatformInterventionReceipt

def canonicalPlatformInterventionReceipt : PlatformInterventionReceipt := {
  sourceAdmission := .cornelsonPaysPlatformInterventionOutcome
  commentsReduced := true
  someAffectiveResponseReduced := true
  sharingReductionPaid := false
  beliefChangePaid := false
  prevalenceReductionPaid := false
}

structure LanguageMentalStateReceipt (family : HighAlphaOutcomeFamily) where
  sourceAdmission : AdmittedHighAlphaSource family
  featureReference : String
  contextReference : String
  groupAssociationPaid : Bool
  singleFeatureIndividualDiagnosisPaid : Bool
  clinicalDeploymentAuthorityPaid : Bool
  deriving Repr, DecidableEq

namespace LanguageMentalStateReceipt
def source {family : HighAlphaOutcomeFamily} (r : LanguageMentalStateReceipt family) : SourceReceipt :=
  admittedHighAlphaSourceReceipt r.sourceAdmission
end LanguageMentalStateReceipt

def pronounContextReceipt : LanguageMentalStateReceipt .pronounAssociationOutcome := {
  sourceAdmission := .tuckZhuThompsonPaysPronounAssociationOutcome
  featureReference := "first-person pronoun frequency / self-focus"
  contextReference := "negative autobiographical narrative; association absent in positive narrative condition"
  groupAssociationPaid := true
  singleFeatureIndividualDiagnosisPaid := false
  clinicalDeploymentAuthorityPaid := false
}

def languageMLMetaReceipt : LanguageMentalStateReceipt .languageModelMetaOutcome := {
  sourceAdmission := .fisherPaysLanguageModelMetaOutcome
  featureReference := "multi-feature language-only machine-learning models"
  contextReference := "heterogeneous datasets, text sources, languages, features and model families"
  groupAssociationPaid := true
  singleFeatureIndividualDiagnosisPaid := false
  clinicalDeploymentAuthorityPaid := false
}

structure AutismFMTTrialReceipt where
  sourceAdmission : AdmittedHighAlphaSource .fmtTrialOutcome
  randomizedDoubleBlindPlaceboControlled : Bool
  primarySRSBetweenGroupPaid : Bool
  secondaryVinelandSocialisationSignal : Bool
  diagnosisRemovalPaid : Bool
  placeboResponseExplicit : Bool
  deriving Repr, DecidableEq

namespace AutismFMTTrialReceipt
def source (r : AutismFMTTrialReceipt) : SourceReceipt := admittedHighAlphaSourceReceipt r.sourceAdmission
end AutismFMTTrialReceipt

def canonicalAutismFMTTrialReceipt : AutismFMTTrialReceipt := {
  sourceAdmission := .wan2024PaysFMTTrialOutcome
  randomizedDoubleBlindPlaceboControlled := true
  primarySRSBetweenGroupPaid := false
  secondaryVinelandSocialisationSignal := true
  diagnosisRemovalPaid := false
  placeboResponseExplicit := true
}

structure AutismFMTProtocolReceipt where
  sourceAdmission : AdmittedHighAlphaSource .fmtProtocolDesignOutcome
  randomizedTripleBlindDesignPlanned : Bool
  efficacyResultAlreadyPaid : Bool
  deriving Repr, DecidableEq

namespace AutismFMTProtocolReceipt
def source (r : AutismFMTProtocolReceipt) : SourceReceipt := admittedHighAlphaSourceReceipt r.sourceAdmission
end AutismFMTProtocolReceipt

def canonicalAutismFMTProtocolReceipt : AutismFMTProtocolReceipt := {
  sourceAdmission := .zou2026PaysFMTProtocolDesign
  randomizedTripleBlindDesignPlanned := true
  efficacyResultAlreadyPaid := false
}

structure MuOpioidSocialReceipt where
  sourceAdmission : AdmittedHighAlphaSource .muOpioidSocialOutcome
  socialConnectionModulationPaid : Bool
  socialConnectionRequiresIntactMuOpioidSignalling : Bool
  propositionTruthAuthorityPaid : Bool
  autismMechanismPaid : Bool
  deriving Repr, DecidableEq

namespace MuOpioidSocialReceipt
def source (r : MuOpioidSocialReceipt) : SourceReceipt := admittedHighAlphaSourceReceipt r.sourceAdmission
end MuOpioidSocialReceipt

def canonicalMuOpioidSocialReceipt : MuOpioidSocialReceipt := {
  sourceAdmission := .losethPaysMuOpioidSocialOutcome
  socialConnectionModulationPaid := true
  socialConnectionRequiresIntactMuOpioidSignalling := false
  propositionTruthAuthorityPaid := false
  autismMechanismPaid := false
}

structure NeurodiversityQoLReceipt where
  sourceAdmission : AdmittedHighAlphaSource .neurodiversityQoLOutcome
  selfAcceptanceRetained : Bool
  supportQualityRetained : Bool
  identityExcludesSupport : Bool
  interventionMustEnforceNormalization : Bool
  deriving Repr, DecidableEq

namespace NeurodiversityQoLReceipt
def source (r : NeurodiversityQoLReceipt) : SourceReceipt := admittedHighAlphaSourceReceipt r.sourceAdmission
end NeurodiversityQoLReceipt

def canonicalNeurodiversityQoLReceipt : NeurodiversityQoLReceipt := {
  sourceAdmission := .linaresPaysNeurodiversityQoLOutcome
  selfAcceptanceRetained := true
  supportQualityRetained := true
  identityExcludesSupport := false
  interventionMustEnforceNormalization := false
}

inductive PronounDiagnosesDepressionPermission : Prop
inductive FMTDiagnosisRemovalPermission : Prop
inductive MuOpioidDeterminesTruthPermission : Prop
inductive EngagementMetricCollapsePermission : Prop
inductive IdentitySupportExclusionPermission : Prop

theorem pronounDoesNotDiagnoseDepression : PronounDiagnosesDepressionPermission → False := by intro h; cases h

theorem fmtDoesNotRemoveDiagnosisFromThisEvidence : FMTDiagnosisRemovalPermission → False := by intro h; cases h

theorem muOpioidDoesNotDetermineTruth : MuOpioidDeterminesTruthPermission → False := by intro h; cases h

theorem engagementMetricsDoNotCollapse : EngagementMetricCollapsePermission → False := by intro h; cases h

theorem identityDoesNotExcludeSupport : IdentitySupportExclusionPermission → False := by intro h; cases h

structure HighAlphaCrossPollination where
  existingPropagationOwner : String
  normMediation : NormMediationReceipt
  platformIntervention : PlatformInterventionReceipt
  pronounContext : LanguageMentalStateReceipt .pronounAssociationOutcome
  languageMeta : LanguageMentalStateReceipt .languageModelMetaOutcome
  fmtTrial : AutismFMTTrialReceipt
  fmtProtocol : AutismFMTProtocolReceipt
  opioidSocial : MuOpioidSocialReceipt
  neurodiversityQoL : NeurodiversityQoLReceipt
  reading : String
  deriving Repr, DecidableEq

def canonicalHighAlphaCrossPollination : HighAlphaCrossPollination := {
  existingPropagationOwner := "Dashi.Biology.AutismVaccinePersuasionMediaExtensionExact"
  normMediation := canonicalNormMediationReceipt
  platformIntervention := canonicalPlatformInterventionReceipt
  pronounContext := pronounContextReceipt
  languageMeta := languageMLMetaReceipt
  fmtTrial := canonicalAutismFMTTrialReceipt
  fmtProtocol := canonicalAutismFMTProtocolReceipt
  opioidSocial := canonicalMuOpioidSocialReceipt
  neurodiversityQoL := canonicalNeurodiversityQoLReceipt
  reading := "Norm mediation sharpens a propagation edge; engagement outcomes remain non-collapsed; language markers require contextual/calibrated inference; randomized FMT separates null primary from positive secondary outcomes; mu-opioids modulate social connection without truth authority; identity and support remain compatible coordinates. Source identity remains provenance; every result family additionally requires a sealed source/outcome admission."
}

structure HighAlphaBoundary where
  normMediationRepresented : Bool
  engagementMetricsCollapsedWithBeliefOrSharing : Bool
  singlePronounDiagnosesDepression : Bool
  languageModelCreatesClinicalDiagnosisAuthority : Bool
  fmtPrimaryClinicalEndpointPaid : Bool
  fmtRemovesAutismDiagnosis : Bool
  muOpioidModulationDeterminesBeliefTruth : Bool
  identityAndSupportCanCoexist : Bool
  deriving Repr, DecidableEq

def canonicalHighAlphaBoundary : HighAlphaBoundary := {
  normMediationRepresented := true
  engagementMetricsCollapsedWithBeliefOrSharing := false
  singlePronounDiagnosesDepression := false
  languageModelCreatesClinicalDiagnosisAuthority := false
  fmtPrimaryClinicalEndpointPaid := false
  fmtRemovesAutismDiagnosis := false
  muOpioidModulationDeterminesBeliefTruth := false
  identityAndSupportCanCoexist := true
}

example : beliefToIntent.automatic = false := rfl
example : intentToBehaviour.automatic = false := rfl

end Dashi.Biology.AutismTranscriptHighAlphaCrossPollinationExact
